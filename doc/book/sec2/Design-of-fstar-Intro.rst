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


Core Language
-------------

The syntax of F*'s core language is summarized by the simplified
grammar of terms, representing the core abstract syntax of terms used
by the F* typechecker. Note, this is not the full concrete syntax of
F* terms, which includes many additional features, including
parentheses for enforcing precedence, implicit arguments, n-ary
functions, various forms of syntactic sugar for common constructs like
tuples and sequencing, etc. However, the essence of F*'s core language
is distilled below. Understand how all these constructs fit together
and you should be able to see how the core of F* is simultaneously a
functional programming language and a logic. The goal of this section
is to explain all these constructs in detail, down to specifics of the
various syntactic conventions used in F*.

Core abstract syntax of F* terms::


  Constants c ::= p                                       primitive constant
                | D                                       user-defined data constructors
                | T                                       user-defined inductive type constructors

  Terms  e, t ::= x                                       variables

                | c                                       constants and constructors


                | fun (x:t) -> t'                         functions

                | t t'                                    applications

                | match t with [b1 ... bn]                pattern matching with zero or more cases

                | let x = t in t'                         let bindings

                | let rec f1 (x:t1) : t1' = e1 ...
                  and ... fn (x:tn) : tn' = en            mutually recursive function definitions

                | x:t -> t                                function types (arrows)

                | x:t { t' }                              refinement types

                | Type u#U                                Type of types

                | x u#U1 ... u#Un                         Variable applied to one or more universes

  Case     X  ::= `|` P -> t                              Pattern-matching branch

  Pattern  P  ::= x                                       Variable
                | c                                       Constant
                | D [P1...Pn]                             Constructor applied to zero or more patterns

  Universe U  ::= x                                       Universe variable
                | 0                                       Universe 0
                | U + 1                                   Successor universe
                | max U U                                 Maximum of universes

Basic syntactic structure
.........................

An F* program is a collection of :ref:`modules<modules>`, with each
module represented by a single file with the filename extension
`.fst`. Later, we'll see that a module's interface is in a separate
file.

A module begins with the module's name and contains a sequence of
top-level signatures and definitions.

* Signatures ascribe a type to a definition, e.g., `val f : t`.

Definitions come in several flavors: the two main forms we'll focus on
in this section are

* possibly recursive definitions (let bindings, `let [rec] f = e`)
* and, inductive type definitions (datatypes, `type t = | D1 : t1 | ... | Dn : tn`)

In later sections, we'll see two other kinds of definition:
user-defined indexed effects and sub-effects.

Classes of Identifiers
^^^^^^^^^^^^^^^^^^^^^^

TODO:

Comments
^^^^^^^^

Block comments are delimited by `(*` and `*)`. Line comments begin
with `//`. ::

  (* this is a
     block comment *)


  //This is a line comment


Primitive constants
...................

Every F* program is checked in the context of some ambient primitive
definitions taken from the core F* module :ref:`Prims<corelib_Prims>`.

Unit
^^^^

The primitive type `unit` has a single element denoted `()`.


Booleans
^^^^^^^^

The primitive type `bool` has two elements, `true` and
`false`. `Prims` also provides the following primitive boolean
operators

* `&&`: Boolean conjunction (infix)
* `||`: Boolean disjunction (infix)
* `not`: Boolean negation (prefix)

TODO: Precedence

Integers
^^^^^^^^

The type `int` represents unbounded, primitive mathematical
integers. Its elements are formed from the literals `0, 1, 2, ...`,
and the following primitive operators:

* `-`: Unary negation (prefix)
* `-`: Subtraction (infix)
* `+`: Addition (infix)
* `/`: Euclidean division (infix)
* `%`: Euclidean modulus (infix)
* `op_Multiply`: Unfortunately, the traditional multiplication symbol
  `*` is reserved by default for the :ref:`tuple<tuples>` type
  constructor. Use the module `FStar.Mul` to treat `*` as integer
  multiplication---see :ref:`this note<tuples>`.
* `<` : Less than (infix)
* `<=`: Less than or equal (infix)
* `>` : Greater than (infix)
* `>=`: Greater than or equal (infix)

TODO: Precedence

Functions
.........

F* provides several forms of syntactic sugar to define functions. The
syntax is largely inherited from OCaml, and this
`OCaml tutorial <https://ocaml.org/learn/tutorials/basics.html#Defining-a-function>`_
provides more details for those unfamiliar with the language.

The following are synonyms::

  let incr = fun (x:int) -> x + 1
  let incr (x:int) = x + 1

You can also let F* infer the type of the parameter `x`::

  let incr x = x + 1

Functions can take several arguments and the result type of a function
can also be annotated, if desired::

  let incr (x:int) : int = x + 1
  let more_than_twice (x:int) (y:int) : bool = x > y + y

It's considered good practice to annotate all the parameters and
result type of a top-level definition.

.. note::

   The type of any term in F* can be annotated using a *type
   ascription*, `e <: t`. This form instructs F* to check that the
   term `e` has the type `t`. For example, we could have written::

     let incr = fun (x:int) -> (x + 1 <: int)

   We'll cover more about type ascriptions in this later
   :ref:`section<ascriptions>`.


User-defined operators and infix notation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Most commonly, to call, or "apply", a function, just place the
arguments to the right of the function. For example::

  incr 0 // calls `incr` with the argument 0
  more_than_twice 17 8 //calls `more_than_twice` with `17` and `8`

You can also immediately apply an unnamed function, or lambda term::

  (fun (x:int) -> x + 1) 0

However, functions with two arguments can be applied in infix
notation, enclosing the function's name in "backticks". For example,
one could write, which can sometimes make code more readable.

  17 \`more_than_twice\` 8

Functions can also be given names using special operator symbols,
e.g., one could write::

  let (>>) = more_than_twice

And then call the function using::

  17 >> 8

This `wiki page
<https://github.com/FStarLang/FStar/wiki/Parsing-and-operator-precedence>`_
provides more details on defining functions with operator symbols.

Boolean refinement types
........................

Types are a way to describe collections of terms. For instance, the
type `int` describes terms which compute integer results, i.e., when
an `int`-typed term is reduced fully it produces a value in the set
`{..., -2, -1, 0, 1, 2, ...}`. Similarly, the type `bool` is the type
of terms that compute or evaluate to one of the values in the set
`{true,false}`.

One (naive but useful) mental model is to think of a type as
describing a set of values. With that in mind, and unlike in other
mainstream programming languages, one can contemplate defining types
for arbitrary sets of values. We will see a great many ways to define
such types, starting with boolean refinement types.

Some simple refinement types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:ref:`Prims<corelib_Prims>` defines the type of natural numbers as::

       let nat = x:int{x >= 0}

This is an instance of a boolean refinement type, whose general form
is `x:t { e }` where `t` is a type, and `e` is a `bool`-typed term
that may refer to the `t`-typed bound variable `x`. The term `e`
*refines* the type `t`, in the sense that the set `S` denoted by `t`
is restricted to those elements `x $\in$ S` for which `e` evaluates to
`true`.

That is the type `nat` describes the set of terms that evaluate to an
element of the set `{0, 1, 2, 3, ...}`.

But, there's nothing particularly special about `nat`. You can define
arbitrary refinements of your choosing, e.g.,::

  let empty = x:int { false } //one type for the empty set
  let zero = x:int{ x = 0 } //the type containing one element `0`
  let pos = x:int { x > 0 } //the positive numbers
  let neg = x:int { x < 0 } //the negative numbers
  let even = x:int { x % 2 = 0 } //the even numbers
  let odd = x:int { x % 2 = 1 } //the odd numbers

.. note::

   If you're coming from a language like C or Java where a type
   primarily describes some properties about the representation of
   data in memory, this view of types as describing arbitrary sets of
   values may feel a bit alien. But, let it sink in a bit---types that
   carve out precise sets of values will let you state and check
   invariants about your programs that may otherwise have only been
   implicit in your code.

Refinement subtyping
^^^^^^^^^^^^^^^^^^^^




Function types or arrows
........................


Syntax of binders
^^^^^^^^^^^^^^^^^


Type: The type of types
.........................


Implicit arguments
..................


Let bindings
............


Inductive type definitions
..........................

.. _tuples:

Pattern matching
................


Recursive definitions and termination
.....................................


Refinement Types
................


Proof irrelevance, squash types and classical logic
...................................................


Decidable equality and `eqtype`
...............................


Universes
.........


Misc
....

.. _ascriptions:

Effects
-------


Modules and Interfaces
----------------------
.. _modules:


.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:
