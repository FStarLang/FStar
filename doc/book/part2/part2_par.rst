.. _Part2_par:

A First Model of Computational Effects
======================================

The inductive types we've seen so far all have constructors whose
arguments are simple types, like type parameters, natural numbers, or
instances of the inductive type itself. In this section we look at
uses of inductive types whose constructors contain functions, i.e.,
inductive types with higher-order fields, or higher-order inductive
types. These are not to be confused with Higher Inductive Types, or
HITs, a concept in `Homotopy Type Theory
<https://en.wikipedia.org/wiki/Inductive_type#Higher_inductive_types>`_.

One constraint we'll encounter is a notion of *strict positivity*, a
syntactic criterion that forces all inductive types to be well
founded, in a certain sense.

As a case study, and a point of contrast with the previous chapter
which presented a *deep embedding* of the simply typed lambda
calculus, we'll look in this chapter at *shallow embeddings*, a way to
represent other computational models (e.g., concurrent computations or
dynamically typed computations) by representing those computations as
elements of inductive types in F*.
