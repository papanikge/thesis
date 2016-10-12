from rpython.flowspace.model import (SpaceOperation, Constant, Variable, Block,
    mkentrymap)
from rpython.rtyper.lltypesystem import lltype
from rpython.translator.backendopt.removenoops import remove_same_as
from rpython.translator.simplify import transform_dead_op_vars

from collections import deque

import pdb

class VirtualObject(object):
    """ Proudly representing the Virtual state of an object """
    def __init__(self):
        self.vars = {}
        self.malloc = None
        self.cast_type = None
    def copy_malloc(self, old, targ):
        """ Copying a malloc operation based on an older VS """
        self.malloc = SpaceOperation('malloc', old.malloc.args, targ)
        self.cast_type = old.cast_type


def materialize_object(obj_key, state, ops):
    """ Accepts a VirtualState object and creates the required operations, for
    its materialization and its initializaion. XXX: Edits ops in-place """

    # Check first
    if obj_key not in state:
        return

    # We're gonna delete the object from the state dict first (since it has
    # escaped) for correct recursion reasons in case of cyclic dependency.
    vo = state[obj_key] # Thus, we'll make a copy first.
    del state[obj_key]

    # Starting assembling the operations. Creation and required castings:
    ops.append(vo.malloc)

    v = Variable()
    v.concretetype = vo.cast_type
    ops.append(SpaceOperation('cast_pointer', [obj_key], v))

    # Initialization
    for key in vo.vars.keys():
        m = Variable()
        m.concretetype = lltype.Void
        if key == 'typeptr':
            target = v
        else:
            target = obj_key
        # What if the assigned is a virtual object? Recursion:
        materialize_object(vo.vars[key], state, ops)
        ops.append(SpaceOperation('setfield',
            [target, Constant(key, lltype.Void), vo.vars[key]], m))


def copy_state(state, exit):
    """ Required function to copy/rename state accordingly for splitting """
    # This is what will be returned
    new_state = {}
    # Auxilliary
    copied = {}

    sent = exit.args
    received = exit.target.inputargs

    i = 0
    while i < len(sent):
        key = sent[i]
        target_var = received[i]
        copied[key] = target_var
        if key in state:
            # delete, because they are virtual
            del sent[i]
            del received[i]

            # creating a copy of the object and putting *that* in new_state
            old_obj  = state[key]
            temp_obj = VirtualObject()
            temp_obj.copy_malloc(old_obj, target_var)
            new_state[target_var] = temp_obj

            # now need a loop to fill temp_obj.vars
            for fieldname, var in old_obj.vars.iteritems():
                if isinstance(var, Variable):
                    if var in copied:
                        temp_obj.vars[fieldname] = copied[var]
                    else:
                        var_copy = var.copy()
                        copied[var] = var_copy
                        temp_obj.vars[fieldname] = var_copy
                        # we need them in the sent/received lists
                        sent.append(var)
                        received.append(var_copy)
                else:
                    temp_obj.vars[fieldname] = var
        else:
            i += 1

    return new_state


def _merge(link_state_tuples):
    new_state = {}
    # Working only for 2 links for now
    lnk1, st1 = link_state_tuples[0]
    lnk2, st2 = link_state_tuples[1]
    targ_block = lnk1.target
    inputargs = targ_block.inputargs

    i = 0
    while i < len(lnk1.args):
        obj1 = lnk1.args[i]
        obj2 = lnk2.args[i]
        targ = inputargs[i]
        if (obj1 in st1) != (obj2 in st2):
            # We're working with XOR here to avoid too many if-s
            materialize_object(obj1, st1, lnk1.prevblock.operations)
            materialize_object(obj2, st2, lnk2.prevblock.operations)
        else:
            # Here they're either both True or both False
            if obj1 in st1:
                new_state[targ] = VirtualObject()
                new_state[targ].copy_malloc(st1[obj1], targ)
                for k, v in st1[obj1].vars.iteritems():
                    # filling in. first, arrays:
                    m = Variable()
                    m.concretetype = lltype.Void
                    lnk1.args.insert((i + 1), v)
                    lnk2.args.insert((i + 1), st2[obj2].vars[k])
                    inputargs.insert((i + 1), m)
                    # states:
                    new_state[targ].vars[k] = m
        i += 1
    return new_state


def _remove_virtual_inputargs(state, inputargs, link1, link2):
    """ Remove all inputargs and the corresponding positions in link1 and link2
    that are in state """
    args1 = link1.args
    args2 = link2.args
    
    i = 0
    while i < len(inputargs):
        if inputargs[i] in state:
            del args1[i]
            del args2[i]
            del inputargs[i]
        else:
            i += 1
    return


def merge(link_state_tuples):
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
        return copy_state(state, exit)
    new = _merge(link_state_tuples)

    # and finally...
    lnk1 = link_state_tuples[0][0]
    lnk2 = link_state_tuples[1][0]
    inputargs = lnk1.target.inputargs
    _remove_virtual_inputargs(new, inputargs, lnk1, lnk2)

    return new


def partial_escape(graph):
    """
    Main function.
    Blocks, which we'll work on, are in a dequeue, called "worklist", and are
    indexing link-state tuples in "statemap".
    """
    # Preparing...
    worklist = deque([graph.startblock])
    statemap = {}
    statemap[graph.startblock] = [(None, {})]
    # For testing purposes for now:
    entrymap = mkentrymap(graph)

    while worklist:
        block = worklist.popleft()
        if block.is_final_block():
            break
        state = merge(statemap[block])
        assert len(entrymap[block]) == len(statemap[block])

        new_operations = []
        # Going through the operations
        for op in block.operations:
            if op.opname == 'malloc':
                # We create a new entry for every new allocation that is not returned
                if op.result in block.exits[0].args and block.exits[0].target.is_final_block():
                    new_operations.append(op)
                else:
                    state[op.result] = VirtualObject()
                    state[op.result].malloc = op
            elif op.opname == 'cast_pointer':
                if op.args[0] in state:
                    # Creating something like an 'alias' for the casting
                    state[op.result] = state[op.args[0]]
                    # ... and saving the concrete-type for later
                    state[op.args[0]].cast_type = op.result.concretetype
                else:
                    new_operations.append(op)
            elif op.opname == 'setfield':
                if op.args[0] in state:
                    state[op.args[0]].vars[op.args[1].value] = op.args[2]
                else:
                    materialize_object(op.args[2], state, new_operations)
                    new_operations.append(op)
            elif op.opname == 'getfield':
                if op.args[0] in state:
                    targ = state[op.args[0]].vars[op.args[1].value]
                    if targ in state:
                        state[op.result] = state[targ]
                    else:
                        new_operations.append(SpaceOperation('same_as', [targ], op.result))
                else:
                    new_operations.append(op)
            else:
                for arg in op.args:
                    materialize_object(arg, state, new_operations)
                new_operations.append(op)
        block.operations = new_operations

        # Finding out the target blocks for the next iteration:
        for exit in block.exits:
            assert exit is not None
            if exit.target not in statemap:
                worklist.append(exit.target)
                statemap[exit.target] = []
            statemap[exit.target].append((exit, state))

    # Done. Cleaning up.
    # remove_same_as(graph)
    # transform_dead_op_vars(graph)

