.. The main file for the F* manual
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Programming with Proofs in F*
=============================

F* is a programming language and proof assistant.

Part 1: F* Manual

1. F* Quick Start: Online tutorial (chapters 1--6, ported here)

2. The Design of F*

   A Verification-oriented Programming Language and Proof Assistant
   (general context from mumon paper)

   * Types
       * Dependent refinement types
       * Intensional vs extensional, undecidability etc.
       * Equality: Definitional and provable equality
       * Subtyping
       * Proof irrelevance

   * Effects
       * Indexed Monads and Effects
       * Subsumption and sub-effecting
       * Effect abstraction, reification and reflecition

   * Modules and Interfaces
       *

   * A Mental Model of the F* Typechecker
       * Type inference based on higher order unification
       * Normalization and proofs by reflection
       * SMT Solving

   * Extraction
       * Computational irrelevance and erasure (Ghost)
       * Normalization for extraction
           * inlining, pure subterms, postprocess(fwd to meta)

   * Scripting F* with Metaprogramming
       * Proof states
       * Reflecting on syntax
       * Quotation
       * Scripting extraction
       * Hooks

3. A User's Guide

   * The Build System
       * Dependence Analysis
       * Checked files
       * Sample project

   * Using the F* editor

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
       * Kremlin
       * Partial evaluation

   * Command line options

   * Error messages

   * Syntax guide

   * FAQ

4. Core libraries

.. _corelib_Prims:

Part 2: F* in Action

1. Foundations of Programming Languages

   a. Simply Typed Lambda Calculus: Syntatic Type Safety

   b. Normalization for STLC
      - Hereditary Substitutions: A Syntactic Normalization Technique
      - Logical Relations

   c. Semantics of an Imperative Language

   d. Floyd-Hoare Logic
      - Hoare triples
      - Weakest Preconditions

2. User-defined Effects

   a. A language with an ML-style heap

   b. Monotonic State

   c. Exceptions

   d. Algebraic Effects

   e. Concurrency

3. Low*: An Embedded DSL and Hoare Logic for Programming

   - Building on 4a and 4b.

   - Integrating / referencing the Kremlin tutorial

4. A Verified Embedding of a Verified Assembly Language

5. Modeling and Proving Cryptography Security

   - UF-CMA MAC

   - IND-CPA Encryption

   - Authenticated Encryption

6. Verified Cryptographic Implementations

7. Steel: An Extensible Concurrent Separation Logic

8. EverParse?
   * Miniparse

9. An End-to-end Verified Low-level App

Part 3: Other resources

   * Recorded coding session
   * Talks, presentations
   * Exemplary code


.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:

   tutorial-overview
   sec2/Design-of-fstar-Intro
   PL-pl-foundations
