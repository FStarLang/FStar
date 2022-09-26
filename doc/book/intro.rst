############
Introduction
############

A Capsule Summary of F*
-----------------------

F* is a dependently type programming language that aims to play
several roles:

* A general purpose programming language, which encourages
  higher-order functional programming with effects, in the tradition
  of the ML family of languages.

* A compiler, which translates F* programs to OCaml or F#, and even C
  or Wasm, for execution.

* A proof assistant, in which to state and prove properties of
  programs.

* A program verification engine, leveraging SMT solvers to partially
  automate proofs of programs.

* A metaprogramming system, supporting the programmatic construction
  of F* programs and proof automation procedures.

To achieve these goals, the design of F* revolves around a few key
elements, described below. Not all of this may make sense to
you---that's okay, you'll learn about it as we go.

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
  Meta-F* programs to manipulate F* syntax and proof goals and for
  users to build proofs interactively with tactics.


DSLs Embedded in F*
~~~~~~~~~~~~~~~~~~~

In practice, rather than a single language, the F* ecosystem is also a
collection of domain-specific languages (DSLs). A common use of F* is
to embed within it programming languages at different levels of
abstraction or for specific programming tasks, and for the embedded
language to be engineered with domain-specific reasoning, proof
automation, and compilation backends. Some examples include:

* Low*, an shallowly embedded DSL for sequential programming against a
  C-like memory model including explicit memory management on the
  stack and heap; a Hoare logic for partial correctness based on
  implicit dynamic frames; and a custom backend (Karamel) to compile
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


.. _Intro_Vec:

To get a taste of F*, let's dive right in with some examples. At this
stage, we don't expect you to understand these examples in detail,
though it should give you a flavor of what is possible with F*.

F* is a dependently typed language
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Dependently typed programming enables one to more precisely capture
properties and invariants of a program using types. Here's a classic
example: the type ``vec a n`` represents an ``n``-dimensional vector
of ``a``-typed elements; or, more simply, a list of ``n`` values each
of type ``a``. Like other dependently typed languages, F* supports
inductively defined definitions of types.

.. literalinclude:: code/Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: vec
   :end-before: SNIPPET_END: vec

Operations on a vectors can be given types that describe their
behavior in terms of vector lengths.

For example, here's a recursive function ``append`` to concatenate two
vectors. Its type shows that the resulting vector has a length that is
the sum of the lengths of the input vectors.

.. literalinclude:: code/Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: append
   :end-before: SNIPPET_END: append

Of course, once a function like ``append`` is defined, it can be used
to define other operations and its type helps in proving further
properties. For example, it's easy to show that reversing a vector
does not change its length.

.. literalinclude:: code/Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: reverse
   :end-before: SNIPPET_END: reverse

Finally, to get an element from a vector, one can program a selector
whose type also includes a *refinement type* to specify that the index
``i`` is less than the length of the vector.

.. literalinclude:: code/Vec.fst
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
chapter <Part2_equality>`.


F* supports user-defined effectful programming
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

While functional programming is at the heart of the language, F* is
about more than just pure functions. In fact, F* is a Turing complete
language. That this is even worth mentioning may come as a surprise to
readers with a background in general-purpose programming languages
like C# or Scala, but not all dependently typed languages are Turing
complete, since nontermination can break soundness. However, F*
supports general recursive functions and non-termination in a safe
manner, without compromising soundness.

Beyond nontermination, F* supports a system of user-defined
computational effects which can be used to model a variety of
programming idioms, including things like mutable state, exceptions,
concurrency, IO, etc.

Here below is some code in an F* dialect called Low*
which provides a sequential, imperative C-like programming model with
mutable memory. The function ``malloc_copy_free`` allocates an array
``dest``, copies the contents of an array of bytes ``src`` into a
``dest``, deallocates ``src`` and returns ``dest``.

.. literalinclude:: code/MemCpy.fst
   :language: fstar
   :start-after: SNIPPET_START: malloc_copy_free
   :end-before: SNIPPET_END: malloc_copy_free

It'll take us until much later to explain this code in
full detail, but here are two main points to take away:

  * The type signature of the procedure claims that under specific
    constraints on a caller, ``malloc_copy_free`` is *safe* to execute
    (e.g., it does not read outside the bounds of allocated memory)
    and that it is *correct* (i.e., that it successfully copies
    ``src`` to ``dest`` without modifying any other memory)

  * Given the implementation of a procedure, F* actually builds a
    mathematical proof that it is safe and correct with respect to its
    signature.

While other program verifiers offer features similar to what we've
used here, a notable thing about F* is that the semantics of programs
with side effects (like reading and writing memory) is entirely
encoded within F*'s logic using a system of user-defined effects.

Whereas ``malloc_copy_free`` is programmed in Low* and specified using
a particular kind of `Floyd-Hoare logic
<https://en.wikipedia.org/wiki/Hoare_logic>`_, there's nothing really
special about it in F*.

Here, for example, is a concurrent program in another user-defined F*
dialect called Steel. It increments two heap-allocated
references in parallel and is specified for safety and correctness in
`concurrent separation logic
<https://en.wikipedia.org/wiki/Separation_logic>`_, a different kind
of Floyd-Hoare logic than the one we used for ``malloc_copy_free``.

.. literalinclude:: IncrPair.fst
   :language: fstar
   :start-after: SNIPPET_START: par_incr
   :end-before: SNIPPET_END: par_incr

As an F* user, you can choose a programming model and a suite of
program proof abstractions to match your needs. You'll learn more
about this in the section on :ref:`user-defined effects <effects>`.

.. _Part1_symbolic_computation:

F* proofs use SMT solving, symbolic computation and tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Stating a theorem or lemma in F* amounts to declaring a type signature
and a doing a proof corresponds to providing an implementation of that
signature. Proving theorems can take a fair bit of work by a human and
F* seeks to reduce that burden, using a variety of techniques.

**SMT Solving**

Proving even a simple program often involves proving dozens or
hundreds of small facts, e.g., proving that bounded arithmetic doesn't
overflow, or that ill-defined operations like divisions by zero never
occur. All these little proofs can quickly overwhelm a user.

The main workhorse for proofs in F* is an automated theorem prover,
known as a *Satisfiability Modulo Theories*, or SMT, solver. The F*
toolchain integrates the `Z3 SMT Solver
<https://www.microsoft.com/en-us/research/blog/the-inner-magic-behind-the-z3-theorem-prover/>`_.

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
in :ref:`this chapter <Part1_prop_assertions>`.

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

.. literalinclude:: code/Vec.fst
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

.. literalinclude:: code/Vec.fst
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

.. literalinclude:: code/Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: tac
   :end-before: SNIPPET_END: tac

This style of proof is similar to what you might find in systems like
Coq or Lean. An F* tactic is just an F* program that can manipulate F*
proof states. In this case, to prove the theorem
``a ==> b ==> (b /\ a)``, we apply commands to transform the proof
state by applying the rules of propositional logic, building a
proof of the theorem.

Tactics are an instance of a more general metaprogramming system in
F*, which allows an F* program to generate other F* programs.


F* programs compile to OCaml and F#, C and Wasm
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Of course, you'll want a way to actually execute the programs you
write. For this, F* provides several ways to compile a program to
other languages for execution, including support to compile programs
to OCaml, F#, C and Wasm.

As such, a common way to use F* is to develop critical components of
larger software systems in it, use its proof-oriented facilities to
obtain assurances about those components, and then to integrate those
formally proven components into a larger system by compiling the F*
program to C, OCaml, or F# and linking the pieces together.

In this case, using a tool called `KaRaMeL
<https://github.com/FStarLang/karamel>`_, a compiler used with F*, we
can produce the following C code for ``memcpy``.

.. literalinclude:: code/out/MemCpy.c
   :language: c
   :start-after: SNIPPET_START: malloc_copy_free
   :end-before: SNIPPET_END: malloc_copy_free

Notice that the code we get contains no additional runtime checks: the
detailed requires and ensures clauses are all gone and what's left is
just a plain C code. Later we'll see how to actually write loops, so
that you're not left with recursive functions in C. The point is that
all the proof and specification effort is done before the program is
compiled, imposing no runtime overhead at all.

To F*, or not to F*?
~~~~~~~~~~~~~~~~~~~~

We've quickly seen a bit of what F* has to offer---that may have been
bit overwhelming, if you're new to program proofs. So, you may be
wondering now about whether it's worth learning F* or not. Here are
some things to consider.

If you like programming and want to get better at it, no matter what
your level is, learning about program proofs will help. Proving a
program, or even just writing down a specification for it, forces you
to think about aspects of your program that you may never have
considered before. There are many excellent resources available to
learn about program proofs, using a variety of other tools, including
some of the following:

  * `Software Foundations
    <https://softwarefoundations.cis.upenn.edu/>`_: A comprehensive
    overview of programming language semantics and formal proofs in
    the Coq proof assistant.

  * `A Proof Assistant for Higher-Order Logic
    <https://isabelle.in.tum.de/doc/tutorial.pdf>`_: A tutorial on the
    Isabelle/HOL proof assistant.

  * `Certified Programming with Dependent Types
    <http://adam.chlipala.net/cpdt/>`_: Provides an introduction to
    proof engineering in Coq.

  * `Type-driven Development
    <https://www.manning.com/books/type-driven-development-with-idris>`_:
    Introduces using dependent types to developing programs correctly
    in Idris.

  * `Theorem Proving in Lean
    <https://leanprover.github.io/theorem_proving_in_lean/>`_: This is
    the standard reference for learning about the Lean theorem prover,
    though there are several other `resources
    <https://leanprover-community.github.io/learn.html>`_ too.

  * `Dafny resources
    <https://github.com/dafny-lang/dafny#read-more>`_: A different
    flavor than all of the above, Dafny is an SMT powered program
    verifier for imperative programs.

  * `Liquid Haskell
    <http://ucsd-progsys.github.io/liquidhaskell-tutorial/>`_: This
    tutorial showcases proving programs with refinement types.

All of these are excellent resources and each tool has unique
offerings. This book about F* offers a few unique things too. We
discuss a few pros and cons, next.

**Dependent Types and Extensionality**

F*'s dependent types are similar in expressiveness to Coq, Lean, Agda,
or Idris, i.e., the expressive power allows formalizing nearly all
kinds of mathematics. What sets F* apart from these other languages
(and more like Nuprl) is its extensional notion of type equality,
making many programming patterns significantly smoother in F* (cf. the
:ref:`vector <Intro_Vec>` example). However, this design also makes
typechecking in F* undecidable. The practical consequences of this are
that F* typechecker can time-out and refuse to accept your
program. Other dependently typed languages have decidable
typechecking, though they can, in principle, take arbitrarily long to
decide whether or not your program is type correct.

**A Variety of Proof Automation Tools**

F*'s use of an SMT solver for proof automation is unique among
languages with dependent types, though in return, one needs to also
trust the combination of F* and Z3 to believe in the validity of an F*
proof. Isabelle/HOL provides similar SMT-assisted automation (in its
Sledgehammer tool), for the weaker logic provided by HOL, though
Sledgehammer's design ensures that the SMT solver need not be
trusted. F*'s use of SMT is also similar to what program verifiers
like Dafny and Liquid Haskell offer. However, unlike their SMT-only
proof strategies, F*, like Coq and Lean, also provides symbolic
reduction, tactics, and metaprogramming. That said, F*'s tactic and
metaprogramming engines are less mature than other systems where
tactics are the primary way of conducting proofs.

**A Focus on Programming**

Other dependently typed languages shine in their usage in formalizing
mathematics---Lean's `mathlib
<https://github.com/leanprover-community/mathlib>`_ and Coq's
`Mathematical Components <https://math-comp.github.io/>`_ are two
great examples. In comparison, to date, relatively little pure
mathematics has been formalized in F*. Rather, F*, with its focus on
effectful programming and compilation to mainstream languages like C,
has been used to it produce industrial-grade high-assurance software,
deployed in settings like the `Windows
<https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/>`_
and `Linux <https://lwn.net/Articles/770750/>`_ kernels, among `many
others <https://project-everest.github.io>`_.

**Maturity and Community**

Isabelle/HOL and Coq are mature tools that have been developed and
maintained for many decades, have strong user communities in academia,
and many sources of documentation. Lean's community is growing fast
and also has excellent tools and documentation. F* is less mature, its
design has been the subject of several research papers, making it
somewhat more experimental. The F* community is also smaller, its
documentation is more sparse, and F* users are usually in relatively
close proximity to the F* development team. However, F* developments
also have a good and growing track record of industrial adoption.


A Bit of F* History
~~~~~~~~~~~~~~~~~~~

F* is an open source project at `GitHub
<https://github.com/FStarLang/FStar>`_ by researchers at a number of
institutions, including `Microsoft Research
<http://research.microsoft.com/en-us>`_, `MSR-Inria
<https://www.microsoft.com/en-us/research/collaboration/inria-joint-centre/>`_, `Inria <https://www.inria.fr/>`_,
`Rosario <https://www.cifasis-conicet.gov.ar/en/>`_, and `Carnegie-Mellon <https://www.cs.cmu.edu/>`_.

**The name** The F in F* is a homage to System F
(https://en.wikipedia.org/wiki/System_F) which was the base calculus
of an early version of F*. We've moved beyond it for some years now,
however. The F part of the name is also derived from several prior
languages that many authors of F* worked on, including `Fable
<https://ieeexplore.ieee.org/document/4531165>`_, `F7
<https://www.microsoft.com/en-us/research/project/f7-refinement-types-for-f/>`_,
`F9
<https://link.springer.com/chapter/10.1007/978-3-642-11957-6_28>`_,
`F5
<https://prosecco.gforge.inria.fr/personal/hritcu/publications/rcf-and-or-coq-tosca2011-post.pdf>`_,
`FX
<https://www.microsoft.com/en-us/research/wp-content/uploads/2011/01/plpv11k-borgstrom.pdf>`_,
and even `F# <https://fsharp.org>`_.

The "\*" was meant as a kind of fixpoint operator, and F* was meant to
be a sort of fixpoint of all those languages. The first version of F*
also had affine types and part of the intention then was to use affine
types to encode separation logic---so the "\*" was also meant to evoke
the separation logic "\*". But, the early affine versions of F* never
really did have separation logic. It took until almost
a decade later to have a separation logic embedded in F* (see Steel),
though without relying on affine types.
