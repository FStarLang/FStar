.. _Part2_equality:

Equality Types
==============

In an :ref:`early section <Part1_equality>` we learned that F*
supports at least two kinds of equality. In this section, we look in
detail at definitional equality, propositional equality, extensional
equality of functions, and decidable equality. These topics are fairly
technical, but are core features of the language and their treatment
in F* makes essential use of an indexed inductive type, ``equals #t x
y``, a proposition asserting the equality of ``x:t`` and ``y:t``.

Depending on your level of comfort with functional programming and
dependent types, you may want to skip or just skim this chapter on a
first reading, returning to it for reference if something is unclear.

Definitional Equality
.....................

One of the main distinctive feature of a type theory like F* (or Coq,
Lean, Agda etc., and in contrast with foundations like set theory) is
that *computation* is a primitive notion within the theory, such that
lambda terms that are related by reduction are considered
identical. For example, there is no way to distinguish within the
theory between :math:`(\lambda x.x) 0` and :math:`0`, since the former
reduces in a single step of computation to the latter. Terms that are
related by reduction are called *definitionally equal*, and this is
the most primitive notion of equality in the language. Definitional
equality is a congruence, in the sense that within any context
:math:`T[]`, :math:`T[n]` is definitionally equal to :math:`T[m]`,
when :math:`n` and :math:`m` are definitionally equal.

Since definitionally equal terms are identical, all type theories,
including F*, will implicit allow treating a term ``v:t`` as if it had
type ``t'``, provided ``t`` and ``t'`` are definitionally equal.

Let's look at a few examples, starting again with our type of
length-indexed vectors.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: vec$
   :end-before: //SNIPPET_END: vec$

As the two examples below show a ``v:vec a n`` is also has type ``vec
a m`` when ``n`` and ``m`` are definitionally equal.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: vec_conversions$
   :end-before: //SNIPPET_END: vec_conversions$

In the first case, a single step of computation (a function
application, or :math:`\beta`-reduction) suffices; while the second
case requires a :math:`\beta`-reduction followed by a step of integer
arithmetic. In fact, any computational step, including unfolding
defintions, conditionals, fixpoint reduction etc. are all allowed when
deciding if terms are definitionally equivalent---the code below
illustrates how F* implicitly reduces the ``factorial`` function when
deciding if two terms are definitionally equal.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: vec_conversions_fact$
   :end-before: //SNIPPET_END: vec_conversions_fact$

Of course, there is nothing particularly special about the ``vec``
type or its indices. Definitional equality applies everywhere, as
illustrated below.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: conv_int$
   :end-before: //SNIPPET_END: conv_int$

Here, when adding ``1`` to ``x``, F* implicitly converts the type of
``x`` to ``int`` by performing a :math:`\beta`-reduction followed by a
case analysis.

Propositional Equality
......................

Definitional equality is so primitive in the language that there is no
way to even state within the terms that two terms are definitional
equal, i.e., there is no way to state within the logic that two terms
are related to each other by reduction. The closest one can get
stating that two terms are equal is through a notion called a
*provable equality* or propositional equality.

In thinking of propositions as types, we mentioned at the :ref:`very
start of the book <Part1>`, that one can think of a type ``t`` as a
proposition, or a statement of a theorem, and ``e : t`` as a proof of
the theorem ``t``. So, one might ask, what type corresponds to the
equality proposition and how are proofs of equality represented?

The listing below shows the definition of an inductive type ``equals
#a x y`` representing the equality proposotion between ``x:a`` and
``y:a`` . Its single constructor ``Reflexivity`` is an equality proof.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: equals$
   :end-before: //SNIPPET_END: equals$

Its easy to construct some simple equality proofs. In the second case,
just as with our vector examples, F* accepts ``Reflexivity #_ #6`` as
having type ``equals (factorial 3) 6``, since ``equals 6 6`` is
definitionally equal to ``equals (factorial 3) 6``.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: sample_equals_proofs$
   :end-before: //SNIPPET_END: sample_equals_proofs$

Although the only constructor of ``equals`` is ``Reflexivity``, as the
the following code shows, ``equals`` is actually an equivalence
relation, satisfying (in addition to reflexivity) the laws of symmetry
and transitivity.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: equivalence_relation$
   :end-before: //SNIPPET_END: equivalence_relation$

This might seem like magic: how is it is that we can derive symmetry
and transitivity from reflexivity alone? The answer lies in how F*
interprets inductive type definitions.

In particular, given an inductive type definition of type
:math:`T~\overline{p}`, where :math:`\overline{p}` is a list of
parameters and, F* includes an axiom stating that any value :math:`v:
T~\overline{p}` must be an application of one of the constructors of
:math:`T`, :math:`D~\overline{v} : T~\overline{p'}`, such that
:math:`\overline{p} = \overline{p'}`.

In the case of equality proofs, this allows F* to conclude that every
equality proof is actually an instance of ``Reflexivity``, as shown
below.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: uip_refl$
   :end-before: //SNIPPET_END: uip_refl$

Spend a minute looking at the statement above: the return type is a
statement of equality about equality proofs. Write down a version of
``uip_refl`` making all implicit arguments explicit.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/ProvableEquality.fst
       :language: fstar
       :start-after: //SNIPPET_START: uip_refl_explicit$
       :end-before: //SNIPPET_END: uip_refl_explicit$

--------------------------------------------------------------------------------

In fact, from ``uip_refl``, a stronger statement showing that all
equality proofs are equal is also provable. The property below is
known as the *uniqueness of identity proofs* (UIP) and is at the core
of what makes F* an extensional type theory.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: uip$
   :end-before: //SNIPPET_END: uip$

The F* module ``Prims``, the very first module in every program's
dependence graph, defines the ``equals`` type as shown here. The
provable equality predicate ``(==)`` that we've used in several
examples already is just a squashed equality proof, as shown below.

.. code-block:: fstar

   let ( == ) #a (x y : a) = squash (equals x y)

In what follows, we'll mostly use squashed equalities, except where we
wish to emphasize the reflexivity proofs.

Equality Reflection
...................

What makes F* an *extensional* type theory (and unlike the
*intensional* type theories implemented by Coq, Lean, Agda, etc.) is a
feature known as equality reflection. Whereas intensional type
theories treat definitional and provable equalities separate, in F*
terms that are provably equal are also considered definitionally
equal. That is, if in a given context ``x == y`` is derivable, the
``x`` is also definitionally equal to ``y``. This has some
wide-reaching consequences.

Implicit conversions using provable equalities
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Recall from the start of the chapter that ``v:vec a ((fun x -> x) 0)``
is implicitly convertible to the type ``vec a 0``, since the two types
are related by congruence and reduction. However, as the examples
below show, if ``a == b`` is derivable in the context, then
``v:a`` can be implicity converted to the type ``b``.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: conversion_with_equality_proofs$
   :end-before: //SNIPPET_END: conversion_with_equality_proofs$

We do not require a proof of ``a == b`` to be literally bound in the
context. As the example below shows, the hypothesis ``h`` is used in
conjunction with the control flow of the program to prove that in the
``then`` branch ``aa : int`` and in the ``else`` branch ``bb : int``.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: conversion_complex$
   :end-before: //SNIPPET_END: conversion_complex$

In fact, with our understanding of equality proofs, we can better
explain how case analysis works in F*. In the code above, the
``then``-branch is typechecked in a context including a hypothesis
``h_then: squash (equals (x > 0) true)``, while the ``else`` branch
includes the hypothesis ``h_else: squash (equals (x > 0) false)``. The
presence of these additional control-flow hypotheses, in conjunction
with whatever else is in the context (in particular hypothesis ``h``)
allows us to derive ``(a == int)`` and ``(b == int)`` in the
respective branches and convert the types of ``aa`` and ``bb``
accordingly.

Undecidability and Weak Normalization
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Implicit conversions with provable equalities are very convenient---we
have relied on it without noticing in nearly all our examples so far,
starting from the simplest examples about lists to vectors and Merkle
trees, and some might say this is the one key feature which gives F*
its programming-oriented flavor.

However, as the previous example hinted, it is, in general,
undecidable to determine if ``a == b`` is derivable in a given
context. In practice, however, through the use of an SMT solver, F*
can often figure out when terms are provably equal and convert using
it. But, it cannot always do this. In such cases, the F* standard
library offers the following primitive (in FStar.Pervasives), which
allows the user to write ``coerce_eq pf x``, to explicitly coerce the
type of ``x`` using the equality proof ``pf``.

.. code-block:: fstar

   let coerce_eq (#a #b:Type) (_:squash (a == b)) (x:a) : b = x

Another consequence of equality reflection is the loss of strong
normalization. Intensional type theories enjoy a nice property
ensuring that every term will reduce to a canonical normal form, no
matter the order of evaluation. F* does not have this property, since
some terms, under certain evaluation orders, can reduce
infinitely. However, metatheory developed for F* proves that closed
terms (terms without free variables) in the ``Tot`` effect do not
reduce infinitely, and as a corollary, there are no closed proofs of
``False``.

F* includes various heuristics to avoid getting stuck in an infinite
loop when reducing open terms, but one can craft examples to make F*'s
reduction macinery loop forever. As such, deciding if possibly open
terms have the same normal form is also undecidable in F*.

.. _Part2_funext:

Functional Extensionality
.........................

Functional extensionality is a principle that asserts the provable
equality of functions that are pointwise equal. That is, for functions
:math:`f` and :math:`g`, :math:`\forall x. f x == g x` implies
:math:`f == g`.

This principle is provable as a theorem in F*, but only for function
literals, or, equivalently, :math:`\eta`-expanded functions. That is,
the following is a theorem in F*.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: funext_eta$
   :end-before: //SNIPPET_END: funext_eta$

.. note::

   Note, the proof of the theorem makes use of tactics, a topic we'll
   cover in a later chapter. You do not need to understand it in
   detail, yet. The proof roughly says to descend into every sub-term
   of the goal and try to rewrite it using the pointwise equality
   hypothesis ``hyp``, and if it fails to just rewrite the sub-term to
   itself.

Unfortunately, functional extensionality does not apply to all
functions. That is, the following is not provable in F* nor is it
sound to assume it as an axiom.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: funext$
   :end-before: //SNIPPET_END: funext$

The problem is illustrated by the following counterexample, which
allows deriving ``False`` in a context where ``funext`` is valid.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: funext_false$
   :end-before: //SNIPPET_END: funext_false$

The proof works by exploiting the interaction with refinement
subtyping. ``f`` and ``g`` are clearly not pointwise equal on the
entire domain of natural numbers, yet they are pointwise equal on the
positive natural numbers. However, from ``ax #pos f g`` we gain that
``f == g``, and in particular that ``f 0 == g 0``, which is false.

.. note::

   The trouble arises in part because although ``ax:funext`` proves
   ``squash (equals #(pos -> int) f g)``, F*'s encoding of the
   equality to the SMT solver (whose equality is untyped) treats the
   equality as ``squash (equals #(nat -> int) f g)``, which leads to
   the contradiction.

Further, :math:`\eta`-equivalent functions in F* are not considered
provably equal. Otherwise, in combination with ``funext_on_eta``, an
:math:`\eta`-equivalence principle leads to the same contradiction as
``funext_false``, as shown below.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: eta_equiv_false$
   :end-before: //SNIPPET_END: eta_equiv_false$

The F* standard library module ``FStar.FunctionalExtensionality``
provides more information and several utilities to work with
functional extensionality on :math:`\eta`-expanded functions.

Thanks in particular to Aseem Rastogi and Dominique Unruh for many
insights and discussions related to functional extensionality.

Exercise
........

Leibniz equality ``leq x y``, relates two terms ``x:a`` and ``y:a`` if
for all predicates ``p:a -> Type``, ``p a`` implies ``p b``. That is,
if no predicate can distinguish ``x`` and ``y``, the they must be
equal.

Define Leibniz equality and prove that it is an equivalence relation.

Then prove that Leibniz equality and the equality predicate ``equals x
y`` defined above are isomorphic, in the sense that ``leq x y ->
equals x y`` and ``equals x y -> leq x y``.

`Exercise file <../code/exercises/Part2.Leibniz.fst>`_

.. container:: toggle

    .. container:: header

       **Hint**

       The section on Leibniz equality `here
       <https://plfa.github.io/Equality/>`_ tells you how to do it in
       Agda.

    .. literalinclude:: ../code/ProvableEquality.fst
       :language: fstar
       :start-after: //SNIPPET_START: leibniz$
       :end-before: //SNIPPET_END: leibniz$

--------------------------------------------------------------------------------

.. _Part2_equality_qualifiers:

Decidable equality and equality qualifiers
..........................................

To end this chapter, we discuss a third kind of equality in F*, the
polymorphic *decidable equality* with the signature shown below taken
from the the F* module ``Prims``.

.. code-block:: fstar

   val ( = ) (#a:eqtype) (x y:a) : bool

On ``eqtype``, i.e., ``a:Type{hasEq a}``, decidable quality ``(=)``
and provable equality coincide, as shown below.

.. literalinclude:: ../code/ProvableEquality.fst
   :language: fstar
   :start-after: //SNIPPET_START: dec_equals_dec$
   :end-before: //SNIPPET_END: dec_equals_dec$

That is, for the class of ``eqtype``, ``x = y`` returns a boolean
value that decides equality. Decidable equality and ``eqtype`` were
first covered in :ref:`an earlier chapter <Part1_equality>`, where we
mentioned that several primitive types, like ``int`` and ``bool`` all
validate the ``hasEq`` predicate and are, hence, instances of ``eqtype``.

When introducing a new inductive type definition, F* tries to
determine whether or not the type supports decidable equality based on
a structural equality of the representation of the values of that
type. If so, the type is considered an ``eqtype`` and uses of the ``(
= )`` operator are compiled at runtime to structural comparison of
values provided by the target language chosen, e.g., OCaml, F\#, or C.

The criterion used to determine whether or not the type supports
equality decidable is the following.

Given an inductive type definition of :math:`T` with parameters
:math:`\overline{p}` and indexes :math:`~\overline{q}`, for each
constructor of :math:`D` with arguments :math:`\overline{v:t_v}`,

1. Assume, or every type parameter :math:`t \in \overline{p}`, :math:`\mathsf{hasEq}~t`.

2. Assume, for recursive types, for all :math:`\overline{q}`, :math:`\mathsf{hasEq}~(T~\overline{p}~\overline{q})`.

3. Prove, for all arguments :math:`\overline{v:t_v}`, prove :math:`\mathsf{hasEq}~t_v`.

If the proof in step 3 suceeds for all constructors, then F*
introduces an axiom
:math:`\forall~\overline{p}~\overline{q}. (\forall t \in \overline{p}. \mathsf{hasEq}~t) \Rightarrow \mathsf{hasEq}~(T~\overline{p}~\overline{q})`.

If the check in step 3 fails for any constructor, F* reports an error
which the user can address by adding one of two qualifiers to the type.

1. ``noeq``: This qualifier instructs F* to consider that the type
   does not support decidable equality, e.g., if one of the
   constructors contains a function, as show below.

   .. literalinclude:: ../code/ProvableEquality.fst
      :language: fstar
      :start-after: //SNIPPET_START: noeq$
      :end-before: //SNIPPET_END: noeq$

2. ``unopteq``: This qualifier instructs F* to determine whether a
   given instance of the type supports equality, even when some of its
   parameters are not themselves instances of ``eqtype``. This can be
   useful in situations such as the following:

   .. literalinclude:: ../code/ProvableEquality.fst
      :language: fstar
      :start-after: //SNIPPET_START: unopteq$
      :end-before: //SNIPPET_END: unopteq$

This `wiki page
<https://github.com/FStarLang/FStar/wiki/Deriving-hasEq-predicate-for-inductive-types,-and-types-of-equalities-in-F*>`_
provides more information about equality qualifiers on inductive types.
