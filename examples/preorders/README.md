
# Examples for Recalling a Witness: Foundations and Applications of Monotonic State

The metatheory development is available in `examples/preorders/metatheory`

The examples and supporting library code are found in the following files:

# Section 2 of the paper

- `ulib/FStar.Monotonic.Heap.fsti`
     Basic heap model interface with support for monotonic references.

- `ulib/FStar.Monotonic.Heap.fst`
     Implementation of the basic heap model interface

- `ulib/FStar.Heap.fst`
     Plain heap model where all the references have trivial preorder

- `ulib/FStar.ST.fst`
     Implementation of the STATE effect using the heap model

- `ulib/FStar.MRef.fst`
     Utility functions for monotonic references

- `examples/preorders/SnapshotST.fst`
     An example of temporarily escaping the preorder

# Section 3 of the paper

- `examples/preorders/MonotonicArray.fst`
     The monotonic array library

- `examples/preorders/Protocol.fst`
     The file transfer example

# Section 4 of the paper

- `examples/preorders/Ariadne.fst`
     Ariadne protocol example

# HyperHeaps and HyperStacks

The code for HyperHeaps and HyperStacks mentioned at the end of
section 2 can be found on the `kyod_hyperstack_monotonicity` branch

- `ulib/FStar.Monotonic.HyperHeap.fst`
     Implementation of the region-based hyper heap model

- `ulib/FStar.HyperHeap.fst`
     Hyper heap model using the trivial preorder

- `ulib/FStar.Monotonic.HyperStack.fst`
     Implementation of the hyper stack heap model featuring a strict stack discipline

- `ulib/FStar.HyperStack.fst`
     Hyper stack model using the trivial preorder

- `ulib/FStar.HyperStack.ST.fst`
     Implementation of a family of effects on hyper stacks with various invariants
