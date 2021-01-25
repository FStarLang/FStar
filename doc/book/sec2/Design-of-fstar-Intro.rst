.. _Design-of-fstar-Intro:

Elements of F*
==============

The :ref:`short tutorial<tutorial-overview>` should have provided you
with a basic feel for F*, in particular for how to use F* and its SMT
solving backend for programming and proving simple functional
programs.

In this section, we step back and provide a more comprehensive
description of F*, starting from short summary of its design goals and
main technical features. Not all of these concepts may be familiar to
you at first, but by the end of this section, you should have gained a
working knowledge of the core design of F* as well as pointers to
further resources.


A Capsule Summary of F*
-----------------------

F* is a dependently type programming language that aims to play
several roles:

* A general purpose programming language, which encourages
  higher-order functional programming with effects, in the tradition
  of the ML family of languages.

* A compiler, which translates F* programs to OCaml or F# for
  execution.

* A proof assistant, in which to state and prove properties of
  programs.

* A program verification engine, leveraging SMT solvers to partially
  automate proofs of programs.

* A metaprogramming system, supporting the programmatic construction
  of F* programs and proof automation procedures.

To achieve these goals, the design of F* revolves around a few key
elements.

* A core language of total functions with full dependent types, with
  an extensional form of type conversion, indexed inductive types, and
  pattern matching, recursive functions with semantic termination
  checking, dependent refinement types and subtyping, and polymorphism
  over a predicative hierarchy of universes.

* A system of user-defined indexed effects, allowing modeling,
  encapsulating, and statically reasoning about various forms of
  computational effects, including a primitive notion of general
  recursion and divergence, as well as an open system of user-defined
  effects, with examples including state, exceptions, concurrency,
  algebraic effects, and several others.

* A built-in encoding of a classical fragment of F*'s logic into the
  first order logic of an SMT solver, allowing many proofs to be
  automatically discharged.

* A reflection within F* of the syntax and proof state of F*, enabling
  Meta-F* programs to manipulate F* syntax and proof goals.

Many other programming languages are closely related to F* and address
some of these goals, including other dependently typed languages like
Coq, Agda, Idris and Lean. In comparison with these languages, the
distinctive features of F* include its extensional type conversion and
SMT-based proof automation (both of which make typechecking more
flexible but also undecidable); the use of refinement types (enabling
a concise form of lightweight specification); and its user-defined
effect system.

DSLs Embedded in F*
...................

In practice, rather than a single language, the F* ecosystem is also a
collection of domain-specific languages (DSLs). A common use of F* is
to embed within it programming languages at different levels of
abstraction or for specific programming tasks, and for the embedded
language to be engineered with domain-specific reasoning, proof
automation, and compilaton backends. Some examples include:

* Low*, an shallowly embedded DSL for sequential programming against a
  C-like memory model including explicit memory management on the
  stack and heap; a Hoare logic for partial correctness based on
  implicit dynamic frames; and a custom backend (Kremlin) to compile
  Low* programs to C for further compilation by off-the-shelf C
  compilers.

* EverParse, a shallow embedding of a DSL (layered on top of the Low*
  DSL) of parser and serializer combinators, for low-level binary
  formats.

* Vale, a deeply embedded DSL for structured programming in a
  user-defined assembly language, with a Hoare logic for total
  correctness, and a printer to emit verified programs in a assembly
  syntax compatible with various standard assemblers.

* Steel, a shallow embedding of concurrency as an effect in F*, with
  an extensible concurrent separation logic for partial correctness as
  a core program logic, and proof automation built using a combination
  of Meta-F* tactics, higher-order unification, and SMT.


Core Language of Dependently Typed Terms
----------------------------------------

The syntax of F*'s core language is summarized by the following
grammar of terms::


  Constants c ::= true | false                            booleans
                | 0 | 1 | 2 | ...                         integers
                | <string constants>                      strings
                | D                                       user-defined data constructors
                | T                                       user-defined inductive type constructors

  Terms  e, t ::= c                                       constants

                | x                                       variables

                | fun bs -> t'                            functions

                | t t'                                    applications

                | match t with X1 ... bn                  pattern matching

                | let x = t in t'                         let bindings

                | let rec f1 bs1 : t1 = t1'
                  and ... fn bsn : tn = tn' ...           mutually recursive function definitions

                | bs -> t                                 function types (arrows)

                | x:t { t' }                              refinement types

  Binders  bs ::= (x:t) | (x:t) bs                        one or more typed variable bindings

  Case     X  ::= `|` P -> t                              Pattern-matching branch

  Pattern  P  ::= x | c P0..Pn                            Pattern


Effects
-------


Modules and Interfaces
----------------------


.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:
