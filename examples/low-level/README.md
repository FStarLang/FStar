A library for low-level, region-based allocation in F*.
=======================================================

Helpers:
- stack.fst: an implementation of a stack using the list module
- listset.fst: extra definitions related to lists

Base files:
- located.fst: base definitions for the `located` type
- lref.fst: a bunch of lemmas ported from heap.fst so that they quantify over
  our new located (ref a) type
- regions.fst: an axiomatization of our stack of regions, along with a series of
  lemmas

High-level modules:
- rst.fst: definition of the RST (as in "Region-ST") effect of computations that
  occur within our stack of regions.
