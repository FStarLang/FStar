.. _Part2_phoas:

Parametric Higher-order Abstract Syntax
=======================================

In the previous chapter, we looked at a *deep embedding* of the simply
typed lambda calculus (STLC). The encoding is "deep" in the sense that
we used an inductive type to represent the *syntax* of the lambda
calculus in F*, and then defined and proved some properties of its
semantics represented mathematically in F*.

Another way to embed a language like the STLC in F* is a *shallow
embedding*. F* is itself a functional programming language, and it has
a type system that is certainly powerful enough to represent simply
typed terms, so why not use lambda terms in F* itself to represent
STLC, rather than merely encoding STLC's abstract syntax in F*. This
kind of encoding is called a shallow embedding, where we use semantic
constructs in the host (or meta) language (F*) to represent analogous
features of the embedded (or object) language (STLC, in our example).


In this chapter, we look at a particularly elegant technique for doing
this called *parametric higher-order abstract syntax* (or PHOAS),
invented by `Adam Chlipala in 2008
<http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf>`_.  The
linked paper provides an excellent introduction to the topic, if
you're looking for more details. We use this example to illustrate the
use of inductive types with non-trivial parameters and indexes, while
also containing strictly positive functions as arguments.

Roadmap
+++++++

The type ``typ`` below represents the types we'll use in our STLC
object language, i.e., the base type ``Bool`` and function types
``Arrow t1 t2``.

.. literalinclude:: ../code/Part2.PHOAS.fst
   :language: fstar
   :start-after: //SNIPPET_START: typ$
   :end-before: //SNIPPET_END: typ$

This is analogous to our representation of STLC types in the deep
embedding of the previous chapter.

Where things get interesting is in the representation of STLC terms
and their semantics. To set the goal posts, we want to

  1. Define a type ``term t``, to represent well-typed STLC
     terms whose type is ``t:typ``

  2. Give an interpretation of STLC types into F* types, by defining a
     function ``denote_typ : typ -> Type``

  3. Give an intepretation of STLC terms in to F* terms of the
     suitable type, i.e., define a function ``denote_term (#t:typ)
     (e:term t) : denote_typ t``, proving that every well-typed STLC
     term at type ``t`` can be represented in F* as a function of type
     ``denote_typ t``.

Such a result would encompass the type soundness results we proved in
the previous chapter (proving that well-typed programs can always make
progress), but would go substantially further to show that the
reduction of all such terms always terminate producing F* values that
model their semantics.

Term representation
++++++++++++++++++++

The main difficulty in representing a language like STLC (or any
language with lambda-like variable-binding structure), is the question
of how to represent variables and their binders.

In the deep embedding of the previous chapter, our answer to this
questions was very syntactic---variables are de Bruijn indexes, where,
at each occurrence, the index used for a variable counts the number of
lambdas to traverse to reach the binder for that variable.

The PHOAS approach to answering these questions is very different. The
idea is to use the binding constructs and variables already available
in the host language (i.e., lambda terms in F*) to represent
binders and variables in the object language (STLC).

The main type in our representation of terms is the ``term0`` defined
below. There are several clever subtleties here, which we'll try to
explain briefly---Chlipala's paper is a better reference for more
details.

.. literalinclude:: ../code/Part2.PHOAS.fst
   :language: fstar
   :start-after: //SNIPPET_START: term0$
   :end-before: //SNIPPET_END: term0$

First, ``term0`` is parameterized by a ``v: typ -> Type``, a function
that represents every variable of type ``t`` in the program as a term
of type ``v t``. Additionally, ``term0`` is indexed by a ``t:typ``,
which describes the type of encoded STLC term---the indexing structure
encode the typing rules of STLC, ensuring that only well-typed STLC
terms can be constructed. That is, ``e:term0 v t`` is an STLC term of
type ``t``, whose variables of type ``s`` are represented by a term of
type ``v s``.

  * ``Var`` : Variables are represented as ``Var #t n : term0 v t``,
    where ``n`` is a term of type ``v t``.

  * ``TT`` and ``FF``: The two boolean constansts are represented by
    these constructors, both of type ``term0 v Bool``, where the index
    indicates that they have type ``Bool``.

  * ``App``: To apply ``e1`` to ``e2`` in a well-typed way, we must
    prove that ``e1`` has an arrow type ``TArrow t1 t2``, while ``e2``
    has type ``t2``, and the resulting term ``App e1 e2`` has type
    ``t2``. Notice how the indexing structure of the ``App``
    constructor precisely captures this typing rule.

  * ``Lam``: Finally, and crucially, we represent STLC lambda terms
    using F* functions, i.e., ``Lam f`` has type ``Arrow t1 t2``, when
    ``f`` is a function from STLC variables of type ``v t1``, to terms
    of type ``term0 v t``. The ``Lam`` case includes a function-typed
    field, but the type of that field, ``v t1 -> term0 v t2`` is
    strictly positive---unlike the the ``dyn`` type, :ref:`shown
    earlier <Part2_strict_positivity>`.

Now, we can define our type ``term``, completing step 1 of our roadmap.

.. literalinclude:: ../code/Part2.PHOAS.fst
   :language: fstar
   :start-after: //SNIPPET_START: term$
   :end-before: //SNIPPET_END: term$

A ``term t`` is a function returning a ``term0 v t``, for any
``v``. This representation, parametric in the
representation of variables, is what gives this approach the name
*Parametric* Higher-order Abstract Syntax.

Denotation of types
+++++++++++++++++++

Step 2 in our roadmap is to give an interpreration of STLC types
``typ`` into F* types. This is easily done, as shown below.

.. literalinclude:: ../code/Part2.PHOAS.fst
   :language: fstar
   :start-after: //SNIPPET_START: denote_typ$
   :end-before: //SNIPPET_END: denote_typ$

We have here a recursive function that computes a *Type* from its
argument. This is may seem odd at first, but it's perfectly legal in a
dependently typed language like F*.

The function ``denote_typ`` The interpretation of ``Bool`` is the F*
type ``bool``, while the interpretation of ``Arrow`` is an F*
arrow. Note, the function terminates because the two recursive calls
are on strict sub-terms of the argument.


Denotation of terms
+++++++++++++++++++

The coolest part of this development is in Step 3 (below), where we
give an interpretation to ``term0``, from which the interpretation of
``term`` becomes trivial.

The main idea is to define an interpretation for the type ``term0
denote_typ t``, i.e., STLC terms of type ``t``, whose variables are
already represented by F* values of the suitable type (determined by
``denote_typ``). In other words, the trickiest part (giving an
interpretation to the variables) is done simply by instantiating the
``v`` parameter in a clever way.

.. literalinclude:: ../code/Part2.PHOAS.fst
   :language: fstar
   :start-after: //SNIPPET_START: denote_term0$
   :end-before: //SNIPPET_END: denote_term0$

Let's look at each of the cases:

  * The ``Var`` case is easy, since the variable ``x`` is already
    interpreted into an element of the appropriate F* type.

  * The constants ``TT`` and ``FF`` are easy too, since we can just
    interpret them as the suitable boolean constants.

  * For the ``App #t1 #t2 f a`` case, we recursively interpret ``f``
    and ``a``. The type indices tell us that ``f`` must be interpreted
    into an F* function of type ``denote_typ t1 -> denote_typ t2`` and
    that ``denote_term0 a`` has type ``denote_typ t1``. So, we can
    simply apply the denotation of ``f`` to the denotation of ``a`` to
    get a term of type ``denote_typ t2``. In other words, function
    application in STLC is represented semantically by function
    application in F*.

  * Finally, in the ``Lam #t1 #t2 f`` case, we need to produce a term
    of type ``denote_typ t1 -> denote_typ t2``. So, we build an F*
    lambda term (where the argument ``x`` has type ``denote_typ t1``),
    and in the body we apply ``f x`` and recursively call
    ``denote_term0`` on ``f x``.

Finally, to complete our development, we define ``denote_term`` just
by calling ``denote_term0``.

.. literalinclude:: ../code/Part2.PHOAS.fst
   :language: fstar
   :start-after: //SNIPPET_START: denote_term$
   :end-before: //SNIPPET_END: denote_term$

If that felt a little bit magical, it's because it almost is! We've
defined the syntax, typing rules, and an interpreter that doubles as a
denotational semantics for the STLC, and proved everything sound in
around 33 lines of code and proof. By picking the right
representation, everything just follows very smoothly.

Termination
-----------

You may be wondering why F* accepts that ``denote_term0 e``
terminates. There are three recursive calls to consider

  * The two calls in the ``App`` case are easy: The recursive calls
    are on strict sub-terms of ``App f a``.

  * In the ``Lam f`` case, we have one recursive call ``denote_term0
    (f x)``, and F* accepts that ``f x`` is strictly smaller than ``Lam
    f``. This is an instance of the sub-term ordering on inductive
    types explained earlier, as part of F*'s ``precedes`` relation,
    :ref:`explained earlier <Part1_precedes_relation>`.

For a bit of intuition, one way to understand the type ``term0 v`` is
by thinking of it as a tree of finite depth, but possibly infinite
width:

  * The leaves of the tree are the ``Var``, ``TT``, and ``FF`` cases.

  * The internal node ``App e0 e1`` composes two sub-trees, ``e0`` and
    ``e1``.

  * The internal node ``Lam #t1 #t2 f`` composes a variable number of
    sub-trees, where the number of sub-trees depends on the parameter
    ``v``. For example:

    - If ``v t1 = unit``, then ``f : unit -> term0 v t``, i.e.,
      there is only one child node, ``f()``.

    - If ``v t1 = bool``, then ``f : bool -> term0 v t``, i.e.,
      there are two children, ``f true`` and ``f false``.

    - if ``v t1 = nat``, then ``f : nat -> term0 v t``, i.e.,
      there are infinitely many children, ``f 0, f 1, f 2, ...``.

With this intuition, informally, it is safe to recursively call
``denote_term0 e`` on any of the children of ``e``, since the depth of
the tree will decrease on each recursive call. Hence the call
``denote_term0 (f x)`` terminates.

We'll revisit termination arguments for recursive functions more
formally in a subsequent chapter on :ref:`well-founded recursion
<Part2_well_founded_recursion>`.

Exercises
+++++++++

Giving a semantics to STLC is just the tip of the iceberg. There's a
lot more one can do with PHOAS and Chlipala's paper gives lots of
examples and sample code in Coq.

An easy first exercise to get familiar with the definitions is to add
another base type, e.g., the type ``Int`` for integers.


For several more advanced exercises, based on the definitions shown in
this chapter, try reconstructing other examples from Chlipala's paper,
including a proof of correctness of a compiler implementing a
continuation-passing style (CPS) transformation of STLC.
