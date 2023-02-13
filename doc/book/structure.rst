


Structure of this book
======================

**This book is a work in progress**

The first four parts of this book explain the main features of the
language using a variety of examples. You should read them
sequentially, following along with the associated code samples and
exercises. These first four parts are arranged in increasing order of
complexity---you can stop after any of them and have a working
knowledge of useful fragments of F*.

The remaining parts of the book are more loosely connected and either
provide a reference guide to the compiler and libraries, or develop
case studies that the reader can choose depending on their
interest. Of course, some of those case studies come with
prerequisites, e.g., you must have read about effects before tackling
the case study on parsers and formatters.

* Part 1: Basic Functional Programming and Proofs


The first part of this book provides a basic introduction to
programming with pure total functions, refinement types, and SMT-based
proofs, and how to compile and execute your first F* program. This
part of the book revises a previous online tutorial on F* and is
targeted at an audience familiar with programming, though with no
background in formal proofs. Even if you are familiar with program
proofs and dependent types, it will be useful to quickly go through
this part, since some elements are quite specific to F*.

* Part 2: Inductive Types for Data, Proofs, and Computations

We turn next to inductive type definitions, the main mechanism by
which a user can define new data types. F*'s indexed inductive types
allow one to capture useful properties of data structures, and
dependently types functions over these indexed types can be proven to
respect several kinds of invariants. Beyond their use for data
structures, inductive data types are used at the core of F*'s logic to
model fundamental notions like equality and termination proofs, and
can also be used to model and embed other programming paradigms within
F*.


..
   Part 2: Dependently Typed Functional Programming
   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

   .. _Universes:
   .. _TypeConversion:

     * Working with indexed data structures
       - Vectors
       - Red-black trees
       - Merkle trees

     * Equality, type conversion, and subtyping

   .. _Classical:

     * Proof irrelevance and classical logic: prop and squash

     * More termination proofs
       - Infinitely branching trees and ordinal numbers
       - Lexicographic orderings and unification

     * Calculational Proofs

     * Generic programming
       - Printf
       - Integer overloading
       - Codes for types

     * Typeclasses

     * Universes

* Part 3: Modularity with Interfaces and Typeclasses


We discuss two main abstraction techniques, useful in structuring
larger developments: interfaces and typeclasses. Interfaces are a
simple information hiding mechanism built in to F*'s module
system. Typeclasses are suitable for more advanced developments,
providing more flexible abstraction patterns coupled with
custom type inference.

* Part 4: Computational Effects

We introduce F*'s effect system, starting with its primitive effects
for total, ghost, and divergent computations. We also provide a brief
primer on Floyd-Hoare logic and weakest precondition calculi,
connecting them to Dijkstra monads, a core concept in the design of
F*'s effect system.

* Part 5: Tactics and Metaprogramming

We introduce Meta-F*, the metaprogramming system included in
F*. Meta-F* can be used to automate the construction of proofs as well
as programmatically construct fragments of F* programs. There's a lot
to cover here---the material so far presents the basics of how to get
started with using Meta-F* to target specific assertions in your
program and to have their proofs be solved using a mixture of tactics
and SMT solving.

* Under the hood: F* & SMT

In this part of the book, we cover how F* uses the Z3 SMT solver. We
present a brief overview of F*'s SMT encoding paying attention in
particular to F* use of fuel to throttle SMT solver's unfolding of
recursive functions and inductive type definitions. We also cover a
bit of how quantifier instantiation works, how to profile Z3's
quantifier instantiation, and some strategies for how to control
proofs that are too slow because of excessive quantifier
instantiation.
  

.. _effects:

* Planned content

The rest of the book is still in the works, but the planned content is
the following:

  + Part 4: User-defined Effects

    - State

    - Exceptions
        
    - Concurrency

    - Algebraic Effects


  + Part 5: Tactics and Metaprogramming

    - Reflecting on syntax

    - Holes and proof states

    - Builtin tactics

    - Derived tactics

    - Interactive proofs

    - Custom decision procedures

    - Proofs by reflection

    - Synthesizing programs

    - Tactics for program extraction


  + Part 6: F* Libraries


  + Part 7: A User's Guide to Structuring and Maintaining F* Developments

    - The Build System
          -- Dependence Analysis
          -- Checked files
          -- Sample project

    - Using the F* editor

    - Proofs by normalization
          * Normalization steps
          * Call-by-name vs. call-by-value
          * Native execution and plugins

    - Proof Engineering
          * Building, maintaining and debugging stable proofs

    - Extraction 
          * OCaml
          * F#
          * KaRaMeL
          * Partial evaluation

    - Command line options

    - A guide to various F* error messages

    - Syntax guide

    - FAQ

  + Part 8: Steel: A Concurrent Separation Logic Embedded in F*
      
  + Part 9: Application to High-assurance Cryptography

  + Part 10: Application to Parsers and Formatters



