.. The main file for the F* manual
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

..
   developed at `Microsoft Research
   <http://research.microsoft.com/en-us>`_, `MSR-Inria
   <http://www.msr-inria.fr/>`_, and `Inria <https://www.inria.fr/>`_.

Proof Oriented Programming in F*
================================

F* is a dependently typed programming language and proof
assistant. This book describes how to use F* for *proof-oriented
programming*, a paradigm in which one co-designs programs and proofs
to provide mathematical guarantees about various aspects of a
program's behavior, including properties like functional correctness
(precisely characterizing the input/output behavior of a program),
security properties (e.g., ensuring that a program never leaks certain
secrets), and bounds on resource usage.

To get a taste of F*, let's dive right in with some examples.

F* is a dependently typed language
..................................

Dependently typed programming enables one to more precisely capture
properties and invariants of a program using types. Here's a classic
example: the type ``vec a n`` represents an ``n``-dimensional vector
of ``a``-typed elements; or, more simply, a list of ``n`` values each
of type ``a``. Like other dependently typed languages, F* supports
inductively defined definitions of types.

.. literalinclude:: Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: vec
   :end-before: SNIPPET_END: vec

Operations on a vectors can be given types that describe their
behavior in terms of vector lengths.

For example, here's a recursive function ``append`` to concatenate two
vectors. Its type shows that the resulting vector has a length that is
the sum of the lengths of the input vectors.

.. literalinclude:: Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: append
   :end-before: SNIPPET_END: append

Of course, once a function like ``append`` is defined, it can be used
to define other operations and its type helps in proving further
properties. For example, it's easy to show that reversing a vector
does not change its length.

.. literalinclude:: Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: reverse
   :end-before: SNIPPET_END: reverse

Finally, to get an element from a vector, one can program a selector
whose type also includes a :ref:`*refinement type* <refinements>` to specify that the index
``i`` is less than the length of the vector.

.. literalinclude:: Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: get
   :end-before: SNIPPET_END: get

While examples like this can be programmed in other dependently typed
languages, they can often be tedious, due to various technical
restrictions. F* provides a core logic with a more flexible notion of
equality to make programming and proving easier. For now, a takeaway
is that dependently typed programming patterns that are `quite
technical in other languages
<http://adam.chlipala.net/cpdt/html/Cpdt.DataStruct.html>`_ are often
fairly natural in F*. You'll learn more about this in :ref:`a later
chapter <TypeConversion>`.


F* supports user-defined effectful programming
..............................................

While functional programming is at the heart of the language, F* is
about more than just pure functions. In fact, F* is a Turing complete
language. That this is even worth mentioning may come as a surprise to
readers coming from general-purpose programming languages like C# or
Scala, but not all dependently typed languages are Turing complete,
since nontermination can break soundness. However, F* supports general
recursive functions and non-termination in a safe manner, without
compromsing soundness.

Beyond nontermination, F* supports a system of user-defined
computational effects which can be used to model a variety of
programming idioms, including things like mutable state, exceptions,
concurrency, IO, etc.

Here below is some code in an F* dialect called :ref:`Low* <LowStar>`
which provides a sequential, imperative C-like programming model with
mutable memory. The function ``memcpy`` copies the contents of an
array of bytes ``src`` into a destination array ``dest`` of the same
length.

.. literalinclude:: MemCpy.fst
   :language: fstar
   :start-after: SNIPPET_START: memcpy
   :end-before: SNIPPET_END: memcpy

It'll take us until :ref:`much later<LowStar>` to explain ``memcpy``
fully. But, here are two main points to take away:

  * ``memcpy``'s type signature claims that under specific constraints
    on a caller, ``memcpy`` is *safe* to execute (e.g., it does not
    read outside the bounds of allocated memory) and that it is
    *correct* (i.e., that it successfully copies ``src`` to ``dest``
    without modifying any other memory)

  * Given the implementation of ``memcpy``, F* actually builds a
    mathematical proof that ``memcpy`` is safe and correct with
    respect to its signature.

While other program verifiers offer features similar to what we've
used in ``memcpy``, a notable thing about F* is that the semantics of
programs with side effects (like reading and writing memory) is
entirely encoded within F*'s logic using a system of user-defined
effects.

Whereas ``memcpy`` is programmed in Low* and specified using a
particular kind of `Floyd-Hoare logic
<https://en.wikipedia.org/wiki/Hoare_logic>`_, there's nothing
particularly special about it in F*.

Here, for example, is a concurrent program in another user-defined F*
dialect called :ref:`Steel <Steel>`. It increments two heap-allocated
references in parallel and is specified for safety and correctness in
`concurrent separation logic
<https://en.wikipedia.org/wiki/Separation_logic>`_, a different kind
of Floyd-Hoare logic than the one we used for ``memcpy``.

.. literalinclude:: IncrPair.fst
   :language: fstar
   :start-after: SNIPPET_START: par_incr
   :end-before: SNIPPET_END: par_incr

As an F* user, you can choose a programming model and a suite of
program proof abstractions to match your needs. You'll learn more
about this in the section on :ref:`user-defined effects <effects>`.

F* proofs use SMT solving, symbolic computation and tactics
...........................................................

Stating a theorem or lemma in F* amounts to declaring a type signature
and a doing a proof corresponds to providing an implementation of that
signature. Proving theorems can take a fair bit of work by a human and
F* seeks to reduce that burden, using a variety of techniques.

**SMT Solving**

Proving even a simple program often involves proving dozens or
hundreds of small facts, e.g., proving that bounded arithmetic doesn't
overflow, or that ill-defined operations like divisions by zero never
occur. All these little proofs can can quickly overwhelm a user.

The main workhorse for proofs in F* is an automated theorem prover,
known as a *Satisfiability Modulo Theories*, or SMT, solver. The F*
toolchain integrates the `Z3 SMT Solver
<https://www.microsoft.com/en-us/research/blog/the-inner-magic-behind-the-z3-theorem-prover/>`_,
which it Z3 SMT solver, which is integrated with the F* toolchain.

By default, the F* typechecker collects all the facts that must be
proven in a program and encodes them to the SMT solver, an engine that
is capable of solving problems in various combinations of mathematical
logics---F* encodes problems to Z3 in a combination of first-order
logic, with uninterpreted functions and integer arithmetic.

Z3 is remarkably effective at solving the kinds of problems that F*
generates for it. The result is that some F* programs enjoy a high
level of automation, e.g., in ``memcpy``, we specified a pre- and
postcondition and a loop invariant, and the system took care of all
the remaining proofs.

You'll learn more about how to use leverage Z3 to prove theorems in F*
in :ref:`this chapter <SMTProofs>`.

That said, Z3 cannot solve all problems that F* feeds to it. As such,
F* offers several other mechanisms with varying levels of user
control.

**Symbolic computation**

SMT solvers are great at proofs that involve equational rewriting, but
many proofs can be done simply by computation. In fact, proofs by
computation are a distinctive feature of many dependently typed
languages and F* is no exception.

As a very simple example, consider proving that ``pow2 12 == 4096``,
where ``pow2`` is the recursive function shown below.

.. literalinclude:: Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: norm_spec
   :end-before: SNIPPET_END: norm_spec

An easy way to convince F* of this fact is to ask it (using
``normalize_term_spec``) to simply compute the result of ``pow2 12``
on an interpreter that's part of the F* toolchain, which it can do
instantly, rather than relying on an SMT solvers expensive equational
machinery to encode the reduction of a recursive function.

This reduction machinery (called the *normalizer*) is capable not only
of fully computing terms like ``pow2 12`` to a result, but it can also
partially reduce symbolic F* terms, as shown in the proof below.

.. literalinclude:: Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: trefl
   :end-before: SNIPPET_END: trefl

The proof invokes the F* normalizer from a tactic called ``T.trefl``,
another F* feature that we'll review quickly, next.

**Tactics and Metaprogramming**

Finally, for complete control over a proof, F* includes a powerful
tactic and metaprogramming system.

Here's a simple example of an interactive proof of a simple fact about
propositions using F* tactics.

.. literalinclude:: Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: tac
   :end-before: SNIPPET_END: tac

This style of proof is similar to what you might find in systems like
Coq or Lean. An F* tactic is just an F* program that can manipulate F*
proof states. In this case, to prove the theorem
``a ==> b ==> (b /\ a)``, we apply commands to transform the proof
state by applying the rules of propositional logic, building of
proof of the theorem.

Tactics are an instance of a more general metaprogramming system in
F*, which allows an F* program to generate other F* programs. You'll
learn more about tactics and metaprograming in :ref:`this chapter
<meta-fstar>`.


F* programs compile to OCaml and F#, C and Wasm
...........................................................

Of course, you'll want a way to actually execute the programs you
write. For this, F* provides several ways to compile a program to
other languages for execution, including support to compile programs
to OCaml, F#, C and Wasm.

As such, a common way to use F* is to develop critical components of
larger software systems in it, use its proof-oriented facilities to
obtain assurances about those components, and then to integrate those
formally proven components into a larger system by compiling the F*
program to C, OCaml, or F# and linking the pieces together.

In this case, using a tool called `KReMLin
<https://github.com/FStarLang/kremlin>`_, a compiler used with F*, we
can produce the following C code for ``memcpy``.

.. literalinclude:: MemCpy.c
   :language: c

Notice that the code we get contains no additional runtime checks: the
detailed requires and ensures clauses are all gone and what's left is
just a plain C code. Later we'll see how to actually write loops, so
that you're not left with recursive functions in C. The point is that
all the proof and specification effort is done before the program is
compiled, imposing no runtime overhead at all.

To F*, or not to F*?
....................

We've quickly seen a bit of what F* has to offer---that may have been
bit overwhelming, if you're new to program proofs. So, you may be
wondering now about whether it's worth learning F* or not. Here are
some things to consider.

**Proofs of programs**: If you like programming and want to get better
 at it, no matter what your level is, learning about program proofs
 will help. Proving a program, or even just writing down a
 specification for it, forces you to think about aspects of your
 program that you may never have considered before. There are many
 excellent resources available to learn about program proofs, using a
 variety of other tools, including some of the following:

  * `Software Foundations <>`_:

  * `Certified Programming with Dependent Types <>`_:

  * `Type-driven Development <>`_:

  * `The Lean book <>`_

  * `Program Proofs <>`_:


** **








A Bit of F* History
...................


Structure of this book
......................



Comparing F* to other program verifiers
.......................................

If you're coming to F* having learned about other SMT-backed
verification-oriented languages like `Dafny <dafny>`_ or `Vcc <vcc>`_,
you might be wondering if F* is really any different. Here are some
points of similarity and contrast.

**User-defined language abstractions**

Perhaps the biggest difference with other program verifiers, is that
rather than offering a fixed set of constructs in which to specify and
verify a progam, F* offers a framework in which users can design their
own abstractions, often at the level of a domain-specific language, in
which to build their programs and proofs.

More concretely, ``memcpy`` is programmed in a user-defined language
embedded in F* called :ref:`Low* <LowStar>`, which targets sequential,
imperative C-like programming model with mutable heap- and
stack-allocated memory.

There's nothing particular special about Low*. Here's


There are a few differences



The signature of ``memcpy``
^^^^^^^^^^^^^^^^^^^^^^^^^^^

The type signature of ``memcpy`` is very detailed, specifying many
properties about the safety and correctness of ``memcpy``, much more
than in most other languages.

**The arguments of ``memcpy``**

  * ``len``, a 32 bit unsigned integer, or a ``uint32``

  * ``cur``, also a ``uint32``, representing the current iteration
    index, but with a constraint requiring it to be bounded by ``len``.

  * ``src`` and ``dest``, pointers to arrays of bytes (``uint8``),
    both with length at least ``len``.

**The return type and effect**

The next line ``ST unit`` states that ``memcpy`` is a function, that
may, as a side effect, read, write, allocate or deallocate memory, and
returns a value of type ``unit``---if the ``unit`` type is unfamiliar
to you, from a C or Java programmer's perspective, think of it as
returning ``void``.

**The precondition**

Now we get to the really interesting part, the ``requires`` and
``ensures`` clauses, describing the pre- and postconditions of
``memcpy``. In order to safely invoke ``memcpy``, a caller must prove
the following properties when the current state of the program is
``h``:

  * ``live h src``: The ``src`` array has been allocated in memory and
    not deallocated yet. This is to ensure that ``memcpy`` does not
    attempt to read memory that is not currently allocated, protecting
    against common violations of `memory safety
    <http://www.pl-enthusiast.net/2014/07/21/memory-safety/>`_, like
    `use-after-free bugs
    <https://cwe.mitre.org/data/definitions/416.html>`_.

  * ``live h dest``: Likewise, the ``dest`` array is also allocated
    and not deallocated yet.

  * ``disjoint src dest``: The ``src`` and ``dest`` arrays should
    point to non-overlapping arrays in memory---if they did not, then
    writing to the ``dest`` array could overwrite the contents of the
    ``src`` array.

  * ``prefix_equal h src dest cur``: The contents of the ``src`` and
    ``dest`` arrays are equal until the current iteration index
    ``cur``.

**The postcondition**

Finally, the ``ensures`` clause describes what ``memcpy`` guarantees,
by relating the contents of the memory state ``h0`` in when ``memcpy``
was called to the memory state ``h1`` at the time ``memcpy`` returns.

  * ``modifies1 dest h0 h1`` guarantees that ``memcpy`` only modified
    the ``dest``

  * ``prefix_equal h1 src dest len`` guarantees that the ``src`` and
    ``dest`` arrays have equal contents all the way up to ``len``

The implementation and proof of ``memcpy``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The signature of ``memcpy`` is significantly longer than its
implementation---that's because many aspects of safety are left
implicit in the implementation and, in this simple case, the
implementation of ``memcpy`` is really quite simple. It just checks if
the ``cur`` index is still less than the length of the array, and, if
so, copies one byte over and recurses while advancing the ``cur``
position.

What's left implicit here is a proof that ``memcpy`` actually does
obey its signature. F* actually builds a mathematical proof behind the
scenes that ``memcpy`` is safe and correct with respect to its
specification. In this case, that proof is done by F*'s typechecker,
which makes use of an automated theorem prover called `Z3
<https://www.microsoft.com/en-us/research/blog/the-inner-magic-behind-the-z3-theorem-prover/>`_
behind the scenes. As such, if you're willing to trust the
implementations of F* and Z3, you can be confident that ``memcpy``
does exactly what its specification states, i.e., that the signature
of ``memcpy`` is a *mathematical theorem* about all its executions.

Compiling ``memcpy`` for execution
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

F* provides several ways to compile a program to other languaegs for
execution, including support to compile programs to OCaml, F#, C and Wasm.

In this case, using a tool called `KReMLin
<https://github.com/FStarLang/kremlin>`_, a compiler used with F*, we
get the following C code for ``memcpy``.

.. literalinclude:: MemCpy.c
   :language: c

Notice that the code we get contains no additional runtime checks: the
detailed requires and ensures clauses are all gone and what's left is
just a plain C code. Later we'll see how to actually write loops, so
that you're not left with recursive functions in C. The point is that
all the proof and specification effort is done before the program is
compiled, imposing no runtime overhead at all.



It is closely related to several other languages, including other
dependently typed languages like `Coq <https://coq.inria.fr>`_, `Agda
<agda>`_, `Idris <idris>`_, and `Lean <lean>`_, and other SMT-based program
verification engines, like `Dafny <dafny>`_ or `Liquid Haskell <lh>`_.

What makes F* unique is a combination of several elements.

* Unlike most other dependently typed languages, F* is Turing complete
  and has a notion of user-defined effects. It encourages higher-order
  functional programming, including general recursion as well as a
  user-extensible system of computational effects powerful enough to
  express mutable state, exceptions, continuations, algebraic effects
  etc.

* F* is proof assistant, in which to state and prove properties of
  programs. Dependently typed proof assistants like

* A program verification engine, leveraging SMT solvers to partially
  automate proofs of programs.

* A framework within which to embed programming languages, developing
  their semantics in a manner suitable for formal proof and enabling
  their compilation to a variety of backends, including OCaml, F\#, C,
  assembly, Wasm, etc.

* A metaprogramming system, supporting the programmatic construction
  of programs, interactive proofs, and proof automation procedures.

Many other programming languages are


Why not F*?
...........




To achieve these goals, the design of F* revolves around a few key
elements.

* A core language of total functions with full dependent types,
  including an extensional form of type conversion, indexed inductive
  types, and pattern matching, recursive functions with semantic
  termination checking, dependent refinement types and subtyping, and
  polymorphism over a predicative hierarchy of universes.

* A system of user-defined indexed effects, for modeling,
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

This tutorial provides a first taste of
verified programming in F\*. More information about F\*, including
papers and technical reports, can be found on the `F\* website
<http://www.fstar-lang.org>`_.

It will help if you are already familiar with functional programming
languages in the ML family (e.g., [OCaml], [F#], [Standard ML]), or
with [Haskell]---we provide a quick review of some basic concepts if
you're a little rusty, but if you feel you need more background, there
are many useful resources freely available on the web, e.g., [Learn
F#], [F# for fun and profit], [Introduction to Caml], the [Real World
OCaml] book, or the [OCaml MOOC].

[OCaml]: https://ocaml.org
[F#]: http://fsharp.org/
[Standard ML]: http://sml-family.org/
[Haskell]: https://www.haskell.org

[Learn F#]: https://fsharp.org/learn.html
[F# for fun and profit]: http://fsharpforfunandprofit.com/
[Introduction to Caml]: https://pl.cs.jhu.edu/pl/lectures/caml-intro.html
[Real World OCaml]: https://realworldocaml.org/
[OCaml MOOC]: https://www.fun-mooc.fr/courses/course-v1:parisdiderot+56002+session03/about

~KK
Without any experience in ML or Ocaml my experience has been that the later
exercises are very hard to solve, as some of the notation was not obvious to me. Even
knowing the correct solution, I had to either infer syntax from the exercise
code (which is fine) or go by trial and error (which was frustrating at times).
I will leave comments on the exercises detailing what kind of notation I was (or
am still) missing. Is there a resource (maybe in the wiki) that we can point
readers to, that includes examples for most of the concepts? Something like the
[F# reference] would be really helpful. Also, it might help to specify the
audience of this tutorial a bit more. As a programmer with slightly faded memory
of how inductive proofs work, the lemmas are not very straight forward. As
someone who has never seen ML or has never done any functional programming, the
syntax and some of the patterns are hard to grasp, I feel.
~

[F# reference]: https://docs.microsoft.com/en-us/dotnet/articles/fsharp/language-reference/

The easiest way to try F\* and solve the verification exercises in this tutorial is
directly in your browser by using the [online F\* editor]. You can
load the boilerplate code needed for each exercise into the online
editor by clicking the "Load in editor" link in the body of each
exercise. Your progress on each exercise will be stored in browser
local storage, so you can return to your code later (e.g. if your
browser crashes, etc).

[online F\* editor]: https://www.fstar-lang.org/run.php

You can also do this tutorial by installing F\* locally on your
machine.  F\* is open source and cross-platform, and you can get
[binary packages] for Windows, Linux, and MacOS X or compile F\* from
the [source code on github] using these [instructions].

[binary packages]: https://github.com/FStarLang/FStar/releases
[source code on github]: http://github.com/FStarLang/FStar
[instructions]: https://github.com/FStarLang/FStar/blob/master/INSTALL.md

You can edit F\* code using your favorite text editor, but for Emacs
the community maintains [fstar-mode.el], a sophisticated extension that adds special
support for F\*, including syntax highlighting, completion, type
hints, navigation, documentation queries, and interactive development
(in the style of CoqIDE or ProofGeneral).
You can find more details about [editor support] on the [F\* wiki].

The code for the exercises in this tutorial and their solutions are in the [F\*
repository] on Github. For some exercises, you have to include
additional libraries, as done by the provided Makefiles.
To include libraries for the Emacs interactive mode follow the
[instructions here](https://github.com/FStarLang/fstar-mode.el#including-non-standard-libraries-when-using-fstar-mode).

~KK
The code available on the tutorial page and on github differs
quite a bit (as does the F\* version I guess). In my case, this lead to some
unexpected errors when copying code from the online-editor to Emacs. It would be
nice to have a pointer to the actual file and maybe the proper parameters to
verify it, in case someone prefers emacs over the online editor.
~

[fstar-mode.el]: https://github.com/FStarLang/fstar-mode.el
[Atom]: https://github.com/FStarLang/fstar-interactive
[Vim]: https://github.com/FStarLang/VimFStar
[editor support]: https://github.com/FStarLang/FStar/wiki/Editor-support-for-F*
[F\* wiki]: https://github.com/FStarLang/FStar/wiki
[F\* repository]: https://github.com/FStarLang/FStar/tree/master/doc/tutorial/code/

By default F\* only verifies the input code, **it does not execute it**.
To execute F\* code one needs to extract it to OCaml or F# and then
compile it using the OCaml or F# compiler. More details on
[executing F\* code] on the [F\* wiki].

[executing F\* code]: https://github.com/FStarLang/FStar/wiki/Executing-F*-code

<!-- CH: TODO: add a chapter on extraction to tutorial -->

<!-- CH: this is just distraction
**A note on compatibility with F\#**: The syntax of F\* and F\#
overlap on a common subset. In fact, the F\* compiler is currently
programmed entirely in this intersection. Aside from this, the
languages and their implementations are entirely distinct. In this
tutorial, we will use the full syntax of F\*, even when it is possible
to express the same program in the fragment shared with F\#. The F\*
compiler sources are a good resource to turn to when trying to figure
out the syntax of this shared fragment.
-->

<!-- # Getting started  { #sec-getstarted } -->


F* is a programming language and proof assistant.

Part 1: F* Manual

.. _SMTProofs:

1. F* Quick Start: Online tutorial (chapters 1--6, ported here)

.. _refinements:

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

.. _meta-fstar:

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

.. _TypeConversion:

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


.. _LowStar:

3. Low*: An Embedded DSL and Hoare Logic for Programming


   - Building on 4a and 4b.

   - Integrating / referencing the Kremlin tutorial

4. A Verified Embedding of a Verified Assembly Language

5. Modeling and Proving Cryptography Security

   - UF-CMA MAC

   - IND-CPA Encryption

   - Authenticated Encryption

6. Verified Cryptographic Implementations

.. _Steel:

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
