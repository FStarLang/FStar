.. _Design-of-fstar-Intro:

Elements of F*
==============

The short tutorial should have provided you
with a basic feel for F*, in particular for how to use F* and its SMT
solving backend for programming and proving simple functional
programs.

In this section, we step back and provide a more comprehensive
description of F*, starting from short summary of its design goals and
main technical features. Not all of these concepts may be familiar to
you at first, but by the end of this section, you should have gained a
working knowledge of the core design of F* as well as pointers to
further resources.


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
``.fst``. Later, we'll see that a module's interface is in a separate
file.

A module begins with the module's name and contains a sequence of
top-level signatures and definitions.

* Signatures ascribe a type to a definition, e.g., ``val f : t``.

Definitions come in several flavors: the two main forms we'll focus on
in this section are

* possibly recursive definitions (let bindings, ``let [rec] f = e``)
* and, inductive type definitions (datatypes, ``type t = | D1 : t1 | ... | Dn : tn``)

In later sections, we'll see two other kinds of definition:
user-defined indexed effects and sub-effects.

Classes of Identifiers
^^^^^^^^^^^^^^^^^^^^^^

TODO:

Comments
^^^^^^^^

Block comments are delimited by ``(*`` and ``*)``. Line comments begin
with ``//``. ::

  (* this is a
     block comment *)


  //This is a line comment


Primitive constants
...................

Every F* program is checked in the context of some ambient primitive
definitions taken from the core F* module :ref:`Prims<corelib_Prims>`.

False
^^^^^

The type ``False`` has no elements. It represents a logical
falsehood in F*---


Unit
^^^^

The type ``unit`` has a single element denoted ``()``.


Booleans
^^^^^^^^

The primitive type ``bool`` has two elements, ``true`` and
``false``. ``Prims`` also provides the following primitive boolean
operators

* ``&&``: Boolean conjunction (infix)
* ``||``: Boolean disjunction (infix)
* ``not``: Boolean negation (prefix)

TODO: Precedence

Integers
^^^^^^^^

The type ``int`` represents unbounded, primitive mathematical
integers. Its elements are formed from the literals ``0, 1, 2, ...``,
and the following primitive operators:

* ``-``: Unary negation (prefix)
* ``-``: Subtraction (infix)
* ``+``: Addition (infix)
* ``/``: Euclidean division (infix)
* ``%``: Euclidean modulus (infix)
* ``op_Multiply``: Unfortunately, the traditional multiplication symbol
  ``*`` is reserved by default for the :ref:`tuple<tuples>` type
  constructor. Use the module ``FStar.Mul`` to treat ``*`` as integer
  multiplication---see :ref:`this note<tuples>`.
* ``<`` : Less than (infix)
* ``<=``: Less than or equal (infix)
* ``>`` : Greater than (infix)
* ``>=``: Greater than or equal (infix)

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

You can also let F* infer the type of the parameter ``x``::

  let incr x = x + 1

Functions can take several arguments and the result type of a function
can also be annotated, if desired::

  let incr (x:int) : int = x + 1
  let more_than_twice (x:int) (y:int) : bool = x > y + y

It's considered good practice to annotate all the parameters and
result type of a top-level definition.

.. note::

   The type of any term in F* can be annotated using a *type
   ascription*, ``e <: t``. This form instructs F* to check that the
   term ``e`` has the type ``t``. For example, we could have written::

     let incr = fun (x:int) -> (x + 1 <: int)

   We'll cover more about type ascriptions in this later
   :ref:`section<ascriptions>`.


User-defined operators and infix notation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Most commonly, to call, or "apply", a function, just place the
arguments to the right of the function. For example::

  incr 0 // calls ``incr`` with the argument 0
  more_than_twice 17 8 //calls ``more_than_twice`` with ``17`` and ``8``

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
type ``int`` describes terms which compute integer results, i.e., when
an ``int``-typed term is reduced fully it produces a value in the set
``{..., -2, -1, 0, 1, 2, ...}``. Similarly, the type ``bool`` is the type
of terms that compute or evaluate to one of the values in the set
``{true,false}``.

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
is ``x:t { e }`` where ``t`` is a type, and ``e`` is a ``bool``-typed term
that may refer to the ``t``-typed bound variable ``x``. The term ``e``
*refines* the type ``t``, in the sense that the set ``S`` denoted by ``t``
is restricted to those elements ``x $\in$ S`` for which ``e`` evaluates to
``true``.

That is the type ``nat`` describes the set of terms that evaluate to an
element of the set ``{0, 1, 2, 3, ...}``.

But, there's nothing particularly special about ``nat``. You can define
arbitrary refinements of your choosing, e.g.,::

  let empty = x:int { false } //one type for the empty set
  let zero = x:int{ x = 0 } //the type containing one element `0`
  let pos = x:int { x > 0 } //the positive numbers
  let neg = x:int { x < 0 } //the negative numbers
  let even = x:int { x % 2 = 0 } //the even numbers
  let odd = x:int { x % 2 = 1 } //the odd numbers

.. note::

   Refinement types in F* trace their lineage to `F7
   <https://www.microsoft.com/en-us/research/project/f7-refinement-types-for-f/>`_,
   a language developed at Microsoft Research c. 2007 -- 2011. `Liquid
   Haskell <https://ucsd-progsys.github.io/liquidhaskell-blog/>`_ is
   another language with refinement types. Those languages provide
   additional background and resources for learning about refinement
   types.

   Refinement types, in conjunction with dependent function types,
   are, in principle, sufficient to encode many kinds of logics for
   program correctness. However, refinement types are just one among
   several tools in F* for program specification and proof.

Refinement subtyping
^^^^^^^^^^^^^^^^^^^^

We have seen so far how to define a new refinement type, like ``nat`` or
``even``. However, to make use of refinement types we need rules that
allow us to:

1. check that a program term has a given refinement type, e.g., to
   check that ``0`` has type ``nat``. This is sometimes called
   *introducing* a refinement type.

2. make use of a term that has a refinement type, e.g., given ``x :
   even`` we would like to be write ``x + 1``, treating ``x`` as an ``int``
   to add ``1`` to it. This is sometimes called *eliminating* a
   refinement type.

The technical mechanism in F* that supports both these features is
called *refinement subtyping*.

If you're used to a language like Java, C# or some other
object-oriented language, you're familiar with the idea of
subtyping. A type ``t`` is a subtype of ``s`` whenever a program term of
type ``t`` can be safely treated as an ``s``. For example, in Java, all
object types are subtypes of the type ``Object``, the base class of all
objects.

For boolean refinement types, the subtyping rules are as follows:

* The type ``x:t { p }`` is a subtype of ``t``. That is, given ``e :
  (x:t{p})``, it is always safe to *eliminate* the refinement and
  consider ``e`` to also have type ``t``.

* For a term ``e`` of type ``t`` (i.e., ``e : t``), ``t`` is a subtype of the
  boolean refinement type ``x:t { p }`` whenever ``p[e / x]`` is provably
  equal to ``true``. In other words, to *introduce* ``e : t`` at the
  boolean refinement type ``x:t{ p }``, it suffices to prove that the
  term ``p`` with ``e`` substituted for bound variable ``x``, evaluates to
  ``true``.

The the elimination rule for refinement types (i.e., the first part
above) is simple---with our intuition of types as sets, the refinement
type ``x:t{ p }`` *refines* the set corresponding to ``t`` by the
predicate ``p``, i.e., the ``x:t{ p }`` denotes a subset of ``t``, so, of
course ``x:t{ p }`` is a subtype of ``t``.

The other direction is a bit more subtle: ``x:t{ p }`` is only a subtype
of ``p``, for those terms ``e`` that validate ``p``. You're probably also
wondering about how to prove that ``p[e/x]`` evaluates to ``true``---this
:ref:`part of the tutorial<tutorial:refinements>` should provide some
answers. But, the short version is that F*, by default, uses an SMT
solver to prove such fact, though you can also use tactics and other
techniques to do so. More information can be found
:ref:`here<mental-model:refinements>`.

An example
++++++++++

Given ``x:even``, consider typechecking ``x + 1 : odd``; it takes a few
steps:

1. The operator ``+`` expects both its arguments to have type ``int`` and
   returns an ``int``.

2. To prove that the first argument ``x:even`` is a valid argument for
   ``+``, we use refinement subtyping to eliminate the refinement and
   obtain ``x:int``. The second argument ``1:int`` already has the
   required type. Thus, ``x + 1 : int``.

3. To conclude that ``x + 1 : odd``, we need to introduce a refinement
   type, by proving that the refinement predicate of ``odd`` evaluates
   to true, i.e., ``x + 1 % 2 = 1``. This is provable by SMT, since we
   started with the knowledge that ``x`` is even.

As such, F* applies subtyping repeatedly to introduce and eliminate
refinement types, applying it multiple times even to check a simple
term like ``x + 1 : odd``.


Function types or arrows
........................

Functions are the main abstraction facility of any functional language
and their types are, correspondigly, the main specificational
construct.

Total dependent functions
^^^^^^^^^^^^^^^^^^^^^^^^^

In its most basic form, function types have the shape::

  x:t0 -> t1

This is the type of a function that

1. receives an argument ``e`` of type ``t0``, and

2. always returns a value of type ``t1[e / x]``, i.e., the type of the
   returned value depends on the argument ``e``.

It's worth emphasizing how this differs from function types in other
languages.

* F*'s function type are dependent---the type of the result depends on
  the argument. For example, we can write a function that returns a
  ``bool`` when applied to an even number and returns a ``string`` when
  applied to an odd number.

* In F*'s core language, all functions are total, i.e., a function
  call always terminates after consuming a finite but unbounded amount
  of resources.

.. note::

   That said, on any given computer, it is possible for a function
   call to fail to return due to resource exhaustion, e.g., running
   out of memory. Later, as we look at :ref:`effects <effects>`, we
   will see that F* also supports writing non-terminating functions.

Some examples and common notation
+++++++++++++++++++++++++++++++++

1. Functions are *curried*. Functions that take multiple arguments are
   written as functions that take the first argument and return a
   function that takes the next argument and so on. For instance, the
   type of integer addition is::

     val (+) : x:int -> y:int -> int

2. Not all functions are dependent and the name of the argument can be
   omitted when it is not needed. For example, here's a more concise
   way to write the type of ``(+)``::

     val (+) : int -> int -> int

3. Function types can be mixed with refinement types. For instance,
   here's the type of integer division---the refinement on the divisor
   forbids division-by-zero errors::

     val (/) : int -> (divisor:int { divisor <> 0 }) -> int

4. Dependence between the arguments and the result type can be used to
   state relationships among them. For instance, there are several
   types for the function ``let incr = (fun (x:int) -> x + 1)``::

     val incr : int -> int
     val incr : x:int -> y:int{y > x}
     val incr : x:int -> y:int{y = x + 1}

   The first type ``(int -> int)`` is its traditional type in languages
   like OCaml.

   The second type ``(x:int -> y:int{y > x})`` states that the returned
   value ``y`` is greater than the argument ``x``.

   The third type is the most precise: ``(x:int -> y:int{y = x + 1})``
   states that the result ``y`` is exactly the increment of the argument
   ``x``.

5. It's often convenient to add refinements on arguments in a
   dependent function type. For instance::

     val f : x:(x:int{ x >= 1 }) -> y:(y:int{ y > x }) -> z:int{ z > x + y }

   Since this style is so common, and it is inconvenient to have to
   bind two names for the parameters ``x`` and ``y``, F* allows (and
   encourages) you to write::

     val f : x:int{ x >= 1 } -> y:int{ y > x } -> z:int{ z > x + y }

6. To emphasize that functions in F*'s core are total functions (i.e.,
   they always return a result), we sometimes annotate the result type
   with the effect label "``Tot``". This label is optional, but
   especially as we learn about :ref:`effects <effects>`, emphasizing
   that some functions have no effects via the ``Tot`` label is
   useful. For example, one might typically write::

     val f : x:int{ x >= 1 } -> y:int{ y > x } -> Tot (z:int{ z > x + y })

   adding a ``Tot`` annotation on the last arrow, to indicate that the
   function has no side effects. One could also write::

     val f : x:int{ x >= 1 } -> Tot (y:int{ y > x } -> Tot (z:int{ z > x + y }))

   adding an annotation on the intermediate arrow, though this is not
   customary.

Please refer to the section on :ref:`Implicit Arguments <implicits>`,
where we explain the full syntax of binders, in function abstractions
and types.

Type: The type of types
.........................

One characteristic of F* (and many other dependently typed languages)
is that it treats programs and their types uniformly, all within a
single syntactic class. A type system in this style is sometimes
called a *Pure Type System* or `PTS
<https://en.wikipedia.org/wiki/Pure_type_system>`_.

In F* (as in other PTSs) types have types too, functions can take
types as arguments and return types as results, etc. In particular,
the type of a type is ``Type``, e.g., ``bool : Type``, ``int : Type``, ``int
-> int : Type`` etc. In fact, even ``Type`` has a type---as we'll see in
the subsection on :ref:`universes <universes>`.

Parametric polymorphism or generics
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Most modern typed languages provide a way to write programs with
generic types. For instance, C# and Java provide generics, C++ has
templates, and languages like OCaml and Haskell have several kinds of
polymorphic types.

In F*, writing functions that are generic or polymorphic in types
arises naturally as a special case of dependent function types. For
example, here's a polymorphic identity function::

  let id : a:Type -> a -> a = fun a x -> x

There are a several things to note here:

* The type of ``id`` is a dependent function type, with two
  arguments. The first argument is ``a : Type``; the second argument is
  a term of type ``a``; and the result also has the same type ``a``.

* The definition of ``id`` is a lambda term with two arguments ``a :
  Type`` (corresponding to the first argument type) and ``x : a``. The
  function returns ``x``---it's an identity function on the second
  argument.

Here are some equivalent ways to write it::

  let id = fun (a:Type) (x:a) -> x <: a
  let id (a:Type) (x:a) : a = x

To call ``id``, one can apply and check its type as shown::

  id bool true : bool
  id bool false : bool
  id int (-1) : int
  id nat 17 : nat
  id string "hello" : string
  id (int -> int) (fun x -> x) 0 : int

.. note::

   Exercises

   Try completing the following programs::

     let apply : a:Type -> b:Type -> (a -> b) -> a -> b = <fill me in>
     let compose : a:Type -> b:Type -> c:Type -> (b -> c) -> (a -> b) -> a -> c = <fill me in>
     let twice : <fill me in> = fun a f x -> compose a a a f f x

It's quite tedious to have to explicitly provide that first type
argument to ``id``. Implicit arguments and type inference will help, as
we'll see in :ref:`a later section <inference>`.


Type inference: Basics
......................
.. _inference:

Like many other languages in the tradition of
`Milner's ML <https://en.wikipedia.org/wiki/ML_%28programming_language%29>`_,
type inference is a central component in F*'s design.

You may be used to type inference in other languages, where one can
leave out type annotations (e.g., on variables, or when using
type-polymorphic (aka generic) functions) and the compiler determines
an appropriate type based on the surrounding program context. F*'s
type inference certainly includes such a feature, but is considerably
more powerful. Like in other dependently typed language, F*'s
inference engine is based on `higher-order unification
<https://en.wikipedia.org/wiki/Unification_(computer_science)#Higher-order_unification>`_
and can be used to infer arbitrary fragments of program text, not just
type annotations on variables.

Let's consider our simple example of the definition and use of the
identity function again::

  let id (a:Type) (x:a) : a = x

  id bool true : bool
  id bool false : bool
  id int (-1) : int
  id nat 17 : nat
  id string "hello" : string
  id (int -> int) (fun x -> x) 0 : int

Instead of explicitly providing that first type argument when applying
``id``, one could write it as follows, replacing the type arguments with
an underscore ``_``::

  id _ true : bool
  id _ false : bool
  id _ (-1) : int
  id _ 17 : nat
  id _ "hello" : string
  id _ (fun x -> x) 0 : int

The underscore symbols is a wildcard, or a hole in program, and it's
the job of the F* typechecker to fill in the hole.

.. note::

   Program holes are a very powerful concept and form the basis of
   Meta-F*, the metaprogramming and tactics framework embedded in
   F*---we'll see more about holes in a :ref:`later
   section<MetaFStar>`.


Implicit arguments
^^^^^^^^^^^^^^^^^^
.. _implicits:

Since it's tedious to write an ``_`` everywhere, F* has a notion of
*implicit arguments*. That is, when defining a function, one can add
annotations to indicate that certain arguments can be omitted at call
sites and left for the typechecker to infer automatically.

For example, one could write::

  let id (#a:Type) (x:a) : a = x

decorating the first argument ``a`` with a ``#``, to indicate that it is
an implicit argument. Then at call sites, one can simply write::

  id true
  id 0
  id (fun x -> x) 0

And F* will figure out instantiations for the missing first argument
to ``id``.

In some cases, it may be useful to actually provide an implicit
argument explicitly, rather than relying on the F* to pick one. For
example, one could write the following::

  id #nat 0
  id #(x:int{x == 0}) 0
  id #(x:int{x <> 1}) 0

In each case, we provide the first argument of ``id`` explicitly, by
preceding it with a ``#`` sign, which instructs F* to take the user's
term rather than generating a hole and trying to fill it.

Universes
.........

.. _universes:

As mentioned before, every well-typed term in F* has a type, and this
is true of the type ``Type`` itself. In some languages that are
designed only for programming rather than both programs and proofs,
the type of ``Type`` is itself ``Type``, a kind of circularity known
as `impredicativity
<https://en.wikipedia.org/wiki/Impredicativity>`_. This circularity
leads to paradoxes and can make a logic inconsistent.

As such, F*, like many other dependently typed systems, employ a
system of *universes*. The type ``Type`` actually comes in (countably)
infinite variants, written ``Type u#0``, ``Type u#1``, ``Type u#2``,
etc. The ``u#i`` annotation following the ``Type`` is called a
*universe level*, where ``Type u#i`` has type ``Type u#(i + 1)``. One
way to think of it is the each universe level contains an entire copy
of ``F*``'s type system, with higher universes being large enough to
accommodate copies of the systems available at all lower levels.

This may seem a bit mind-bending at first. And, indeed, the universe
system of F* can often be ignored, since F* will infer universes
levels, e.g., one can just write ``Type`` instead of picking a
specific universe level. That said, occasionally, the universe
constraints will make themselves known and preventy you from doing
certain things that can break consistency. Nevertheless, universes are
a crucial feature that allow F* programs to abstract over nearly all
elements of the language (e.g., one can write functions from types to
types, or store types within data structures) while remaining
logically consistent.

F*'s type system is universe polymorphic, meaning that by default, a defin






Syntax of binders
.................

Having informally introduced implicit arguments, we can now present a
first take at the syntax of binders in F*.

**Binding occurrences**: A binding occurence `b` of a variable
introduces a variable in a scope and is associated with one of several
language constructs, including a lambda abstraction, a refinement
type, a let binding, etc. Each binding occurrence is in one of several
forms:

  1. The form ``x:t``, declaring a variable ``x`` at type ``t``

  2. The ``#x:t``, indicating that the binding is for an implicit
     argument ``x`` of type ``t``.

In many cases the type annotation on a binder can be omitted,

Later, we will see additional forms of binding occurrences, including
versions that associate attributes with binders and others with
various forms of type-inference hints.

**Introducing binders**: The syntax ``fun (b1) ... (bn) -> t``
introduces a lambda abstraction, whereas ``b1 -> .. bn -> t`` is the
shape of a function type.


Decidable equality and `eqtype`
...............................



Let bindings
............


Inductive type definitions
..........................

.. _tuples:

Discriminators
^^^^^^^^^^^^^^

Projectors
^^^^^^^^^^

Equality
^^^^^^^^

Positivity
^^^^^^^^^^

Universe constraints
^^^^^^^^^^^^^^^^^^^^

Pattern matching
................


Recursive definitions and termination
.....................................


Refinement Types
................


Proof irrelevance, squash types and classical logic
...................................................


Misc
....


Evaluation strategy
^^^^^^^^^^^^^^^^^^^

.. _ascriptions:

Effects
-------
.. _effects:


Modules and Interfaces
----------------------
.. _modules:

.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:

A Mental Model of the F* Typechecker
------------------------------------
.. _mental-model:refinements:


Dangling

.. _tutorial:refinements:
