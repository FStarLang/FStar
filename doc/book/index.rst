.. The main file for the F* manual
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

..
   developed at `Microsoft Research
   <http://research.microsoft.com/en-us>`_, `MSR-Inria
   <http://www.msr-inria.fr/>`_, and `Inria <https://www.inria.fr/>`_.

Proof-Oriented Programming in F*
================================

F* is a dependently typed programming language and proof
assistant. This book describes how to use F* for *proof-oriented
programming*, a paradigm in which one co-designs programs and proofs
to provide mathematical guarantees about various aspects of a
program's behavior, including properties like functional correctness
(precisely characterizing the input/output behavior of a program),
security properties (e.g., ensuring that a program never leaks certain
secrets), and bounds on resource usage.

Although a functional programming language at its core, F* promotes
programming in a variety of paradigms, including programming with
pure, total functions, low-level programming in imperative languages
like C and assembly, concurrent programming with shared memory and
message-passing, and distributed programming. Built on top of F*'s
expressive, dependently typed core logic, no matter which paradigm you
choose, proof-oriented programming in F* ensures that programs behave
as intended.

.. _LowStar:
.. _Steel:

Structure of this book
......................

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

.. _SMTProofs:

.. _refinements:

Part 1: Basic Functional Programming and Proofs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The first part of this book provides a basic introduction to
programming with pure total functions, refinement types, and SMT-based
proofs. This part of the book revises a previous online tutorial on F*
and is targeted at an audience familiar with programming, though with
no background in formal proofs. Even if you are familiar with program
proofs and dependent types, it will be useful to quickly go through
this part, since some elements are quite specific to F*.

Part 2: Inductive Types for Data, Proofs, and Computations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We turn next to inductive type definitions, the main mechanism by
which a user can define new data types. F*'s indexed inductive types
allow one to capture useful properties of data structures, and
dependently types functions over these indexed types can to respect
several kinds of invariants. Beyond their use for data structures,
inductive data types are used at the core of F*'s logic to model
fundamental notions like equality and termination proofs, and can also
be used to model and embed other programming paradigms within F*.


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

.. _effects:

Part 3: User-defined Effects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

  * Ghost: An Effect for Erasable Computations

  * Nontermination: The Effect of Divergence

  * State

  * Exceptions

  * Concurrency

  * Algebraic Effects

.. _MetaFStar:

Part 4: Tactics and Metaprogramming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

  * Reflecting on syntax

  * Holes and proof states

  * Builtin tactics

  * Derived tactics

  * Interactive proofs

  * Custom decision procedures

  * Proofs by reflection

  * Synthesizing programs

  * Tactics for program extraction


.. _corelib_prims:

Part 5: F* Libraries
^^^^^^^^^^^^^^^^^^^^

.. _modules:

Part 6: A User's Guide to Structuring and Maintaining F* Developments
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

   * The Build System
       * Dependence Analysis
       * Checked files
       * Sample project

   * Using the F* editor

.. _Part6_SMT:

   * SMT Proofs
       * Quantifiers and Patterns
       * Arithmetic
       * Unsat cores, recording and replaying hints
       * Debugging a failed SMT proofs
       * SMT Profiling

   * Proofs by normalization
       * Normalization steps
       * Call-by-name vs. call-by-value
       * Native execution and plugins

   * Tactics and custom decision procedures

   * Common proof patterns
       * Classical proofs
       * Constructive proofs
       * Axioms
       * Termination proofs

   * Proof Engineering
       * Building, maintaining and debugging stable proofs

   * Extraction
       * OCaml
       * F#
       * KaRaMeL
       * Partial evaluation

   * Command line options

   * Error messages

   * Syntax guide

   * FAQ


Part 7: Application to High-assurance Cryptography
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


Part 8: Application to Programming Language Semantics
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

   * MiniVale: A verified Hoare logic for assembly language


Part 9: Application to Parsers and Formatters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


Part 10: Steel: A Concurrent Separation Logic Embedded in F*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:

   intro
   part1/part1
   part2/part2
   part3/part3
   part4/part4
