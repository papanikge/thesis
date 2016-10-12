from collections import deque, defaultdict, OrderedDict
import pdb

from rpython.rtyper.lltypesystem import lltype
from rpython.translator.backendopt.removenoops import remove_same_as
from rpython.translator.simplify import (transform_dead_op_vars,
    eliminate_empty_blocks, join_blocks)
from rpython.translator import unsimplify
from rpython.flowspace.model import (SpaceOperation, Constant, Variable, Block,
                                     mkentrymap, checkgraph)
from rpython.translator.backendopt.support import (find_backedges,
                                                   find_loop_blocks)

from rpython.translator.backendopt.support import log


class VirtualObject(object):
    def __init__(self, concretetype, malloc_args):
        # vars maps (variable, concretetype) to the field value
        self.vars = OrderedDict()
        self.malloc_args = malloc_args
        self.concretetype = concretetype
        # a set of variables that all alias the current virtual
        self.aliases = set()

    def identical_malloc_args(self, other):
        if len(self.malloc_args) == 0:
            return other.malloc_args == []
        if len(self.malloc_args) == 2 and len(other.malloc_args) == 2:
            return (self.malloc_args[0] == other.malloc_args[0] and
                    self.malloc_args[1].value == other.malloc_args[1].value)
        return self.malloc_args == other.malloc_args


def materialize_object(obj_key, state, ops):
    """ Accepts a VirtualState object and creates the required operations, for
    its materialization/initialization. XXX: Edits ops in-place
    """

    if obj_key not in state:
        return False

    # We're gonna delete the object from the state dict first (since it has
    # escaped) for correct recursion reasons in case of cyclic dependency.
    # this needs to be done with all the aliases of the object!
    vo = state[obj_key] # Thus, we'll make a copy first.
    assert obj_key in vo.aliases
    for key in vo.aliases:
        del state[key]

    # Starting assembling the operations. Creation and required castings:
    newvar = Variable()
    newvar.concretetype = vo.concretetype
    ops.append(SpaceOperation('malloc', vo.malloc_args, newvar))

    # recreate the aliases
    for var in vo.aliases:
        if var.concretetype != vo.concretetype:
            ops.append(SpaceOperation('cast_pointer', [newvar], var))
        else:
            ops.append(SpaceOperation('same_as', [newvar], var))

    # Initialization
    for (key, concretetype), value in vo.vars.items():
        if concretetype != vo.concretetype:
            # we need a cast_pointer
            v = Variable()
            v.concretetype = concretetype
            op = SpaceOperation('cast_pointer', [newvar], v)
            ops.append(op)
            target = v
        else:
            target = newvar
        # What if the assigned is a virtual object? Recursion:
        materialize_object(value, state, ops)
        m = Variable()
        m.concretetype = lltype.Void
        ops.append(SpaceOperation('setfield', [target,
                                               Constant(key, lltype.Void),
                                               value], m))
    return True



def copy_state(state, exit, must_be_materialized=False):
    """ Required function to copy/rename state accordingly for splitting
    """
    new_state = {}

    # vars in prevblock -> vars in target
    copied_vars = {}
    # map vobj in state -> vobj in new_state
    copied_vobjs = {}

    sent = exit.args
    received = exit.target.inputargs

    i = 0
    while i < len(sent):
        old_var = sent[i]
        new_var = received[i]
        copied_vars[old_var] = new_var
        if old_var in state:
            if must_be_materialized:
                materialize_object(old_var, state, exit.prevblock.operations)
            else:
                # delete, because they are virtual
                del sent[i]
                del received[i]

                # creating a copy of the object and putting *that* in new_state
                old_vobj = state[old_var]
                if old_vobj in copied_vobjs:
                    new_vobj = copied_vobjs[old_vobj]
                else:
                    new_vobj = VirtualObject(
                        old_vobj.concretetype, old_vobj.malloc_args)
                    copied_vobjs[old_vobj] = new_vobj
                    # now need a loop to fill new_vobj.vars
                    for key, var in old_vobj.vars.iteritems():
                        if isinstance(var, Variable):
                            if var in copied_vars:
                                new_vobj.vars[key] = copied_vars[var]
                            else:
                                var_copy = var.copy()
                                copied_vars[var] = var_copy
                                new_vobj.vars[key] = var_copy
                                # we need them in the sent/received lists
                                sent.append(var)
                                received.append(var_copy)
                        else:
                            new_vobj.vars[key] = var
                new_state[new_var] = new_vobj
                new_vobj.aliases.add(new_var)

        else:
            i += 1

    return new_state


def merge(link_state_tuples, orig_must_be_materialized=False):
    """
    Function that actually merges states.
    Objects also get materialized here.
    """
    new_state = {}

    link_state_tuples = link_state_tuples[:] # copy so we can mutate it

    # We'll have one of the links in a proper variable to "guide" the algorithm
    # around it. We'll iterate thru the array to mirror the changes to the rest
    sample_link, sample_state = link_state_tuples.pop()
    inputargs = sample_link.target.inputargs

    # the big problem here is aliasing. there can be several variables that
    # store the same vobj. this mapping must be the same across all links
    # to keep track, use the following dict, mapping
    # vobj -> (vobj1, ..., vobjn)
    # for each vobj from all the incoming links
    passed_vobjs = {}

    # map vobj in sample_state -> vobj in new_state
    merged_vobjs = {}

    inputargsindex = 0
    while inputargsindex < len(sample_link.args):
        sample_obj = sample_link.args[inputargsindex]
        sample_vobj = sample_state.get(sample_obj, None)
        targ = inputargs[inputargsindex]
        must_be_materialized = orig_must_be_materialized
        if sample_vobj is None:
            must_be_materialized = True

        # set the flag accordingly instead of a huge if clause
        if not must_be_materialized:
            vobj_list = [sample_vobj]
            for lnk, state in link_state_tuples:
                obj = lnk.args[inputargsindex]
                vobj =  state.get(obj)
                if vobj is None:
                    must_be_materialized = True
                    break
                if not sample_vobj.identical_malloc_args(vobj):
                    must_be_materialized = True
                vobj_list.append(vobj)
            else:
                # all the same! check aliasing
                for vobj in vobj_list:
                    if vobj in passed_vobjs:
                        if passed_vobjs[vobj] != vobj_list:
                            # different aliasing! too bad
                            must_be_materialized = True
                    else:
                        passed_vobjs[vobj] = vobj_list

        if must_be_materialized:
            # We can't merge! materialize all objects!
            changed = materialize_object(sample_obj,
                                         sample_state,
                                         sample_link.prevblock.operations)
            for lnk, state in link_state_tuples:
                changed = materialize_object(
                        lnk.args[inputargsindex], state,
                        lnk.prevblock.operations) or changed
            if changed:
                # we forced something! that can have all kinds of weird effects
                # if the virtual has already been passed to the target block
                # earlier. therefore, we restart.
                inputargsindex = 0
                new_state.clear()
                passed_vobjs.clear()
                merged_vobjs.clear()
                continue
        else:
            # We can merge: objects are virtual and classes are the same
            new_vobj = merged_vobjs.get(sample_vobj)
            if new_vobj is None:
                new_vobj = VirtualObject(sample_vobj.concretetype,
                                         sample_vobj.malloc_args)
                merged_vobjs[sample_vobj] = new_vobj
                for key, v in sample_vobj.vars.iteritems():
                    m = Variable()
                    m.concretetype = v.concretetype
                    inputargs.insert((inputargsindex + 1), m)
                    sample_link.args.insert((inputargsindex + 1), v)
                    for lnk, state in link_state_tuples:
                        vo = state[lnk.args[inputargsindex]]
                        try:
                            newarg = vo.vars[key]
                        except KeyError:
                            # uninitialized field!
                            newarg = Constant(
                                    lltype.nullptr(v.concretetype.TO),
                                    v.concretetype)
                        lnk.args.insert((inputargsindex + 1), newarg)
                    new_vobj.vars[key] = m
            new_state[targ] = new_vobj
            new_vobj.aliases.add(targ)
        inputargsindex += 1
    # safety check: size of state can only shrink
    vobjset = set(new_state.values())
    for _, state in link_state_tuples:
        assert len(vobjset) <= len(set(state.values()))
    return new_state


def remove_virtual_inputargs(state, link_state_tuples):
    """ Remove all inputargs and the corresponding positions that are in state
    """
    inputargs = link_state_tuples[0][0].target.inputargs

    i = 0
    while i < len(inputargs):
        if inputargs[i] in state:
            del inputargs[i]
            for lnk, _ in link_state_tuples:
                del lnk.args[i]
        else:
            i += 1
    return


def get_current_state(link_state_tuples, must_be_materialized=False):
    """
    Accepts an array of link-state tuples.
    Returns the appropriate state dict for every block-editing iteration
    This is a wrapper around other functions
    """
    if len(link_state_tuples) == 1:
        # Normal block. We make a copy of the state
        exit, state = link_state_tuples[0]
        if exit is None:
            # startblock, no need to copy
            return state
        return copy_state(state, exit, must_be_materialized)
    new = merge(link_state_tuples, must_be_materialized)
    remove_virtual_inputargs(new, link_state_tuples)
    return new


def can_remove(op):
    S = op.args[0].value
    if op.args[1].value != {'flavor': 'gc'}:
        return False
    try:
        # cannot remove if there is a destructor
        destr_ptr = lltype.getRuntimeTypeInfo(S)._obj.destructor_funcptr
        if destr_ptr:
            return False
    except (ValueError, AttributeError):
        pass
    return True


def insert_links(graph):
    # insert a new empty block along every link, as a place to put the forcings
    for link in list(graph.iterlinks()):
        unsimplify.insert_empty_block(link)


def partial_escape(translator, graph):
    """
    Main function.
    Blocks, which we'll work on, are in a dequeue, called "worklist", and are
    indexing link-state tuples in "statemap".
    """
    insert_links(graph)
    worklist = deque([graph.startblock])
    statemap = defaultdict(list)
    statemap[graph.startblock] = [(None, {})]
    finished = set()
    entrymap = mkentrymap(graph)
    backedges = find_backedges(graph)

    number_getfield_removed = 0

    while worklist:
        block = worklist.popleft()
        must_be_materialized = block.is_final_block()
        for link in entrymap[block]:
            if link in backedges:
                must_be_materialized = True
        state = get_current_state(statemap[block],
                                  must_be_materialized=must_be_materialized)
        if block.is_final_block():
            continue

        new_operations = []
        # Going through the operations
        for op in block.operations:
            if op.opname == 'malloc':
                # Create new entry for every allocation that is not returned
                if can_remove(op):
                    vobj = VirtualObject(op.result.concretetype, op.args)
                    state[op.result] = vobj
                    vobj.aliases.add(op.result)
                else:
                    new_operations.append(op)
            elif op.opname == 'cast_pointer':
                if op.args[0] in state:
                    # Creating something like an 'alias' for the casting
                    state[op.result] = vobj = state[op.args[0]]
                    vobj.aliases.add(op.result)
                else:
                    new_operations.append(op)
            elif op.opname == 'setfield':
                if op.args[0] in state:
                    state[op.args[0]].vars[op.args[1].value,
                                           op.args[0].concretetype] = op.args[2]
                else:
                    materialize_object(op.args[2], state, new_operations)
                    new_operations.append(op)
            elif op.opname == 'getfield':
                key = op.args[1].value, op.args[0].concretetype
                if op.args[0] in state and key in state[op.args[0]].vars:
                    targ = state[op.args[0]].vars[key]
                    number_getfield_removed += 1
                    if targ in state:
                        state[op.result] = vobj = state[targ]
                        state[targ].aliases.add(vobj)
                    else:
                        new_operations.append(SpaceOperation('same_as',
                                                             [targ],
                                                             op.result))
                else:
                    materialize_object(op.args[0], state, new_operations)
                    new_operations.append(op)
            else:
                for arg in op.args:
                    materialize_object(arg, state, new_operations)
                new_operations.append(op)
        # for all backedges, materialize all arguments (loops aren't supported
        # properly yet)
        for exit in block.exits:
            if exit in backedges or exit.target.is_final_block():
                for arg in exit.args:
                    materialize_object(arg, state, new_operations)
        block.operations = new_operations

        # We're done with the internals of the block. Editing the lists:
        finished.add(block)
        for exit in block.exits:
            # Only adding to the worklist if all its ancestors are processed
            for lnk in entrymap[exit.target]:
                if lnk.prevblock not in finished and lnk not in backedges:
                    break
            else:
                if exit.target not in finished and exit.target not in worklist: # XXX
                    worklist.append(exit.target)
            # setting statemaps:
            statemap[exit.target].append((exit, state))
    if number_getfield_removed:
        if translator.config.translation.verbose:
            log.cse("partial escape analysis removed %s getfields in graph %s" % (number_getfield_removed, graph))
        else:
            log.dot()

    # Done. Cleaning up.
    remove_same_as(graph)
    transform_dead_op_vars(graph)
    eliminate_empty_blocks(graph)
    join_blocks(graph)
    checkgraph(graph)

    return number_getfield_removed
