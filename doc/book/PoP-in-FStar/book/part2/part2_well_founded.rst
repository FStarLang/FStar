.. _Part2_well_founded_recursion:

Well-founded Relations and Termination
======================================

In an earlier chapter on :ref:`proofs of termination
<Part1_termination>`, we learned about how F* checks that recursive
functions terminate. In this chapter, we see how the termination check
arises from inductive types and structural recursion. Just as with
:ref:`equality <Part2_equality>`, termination checking, a core feature
of F*'s logic and proof system, finds its foundation in inductive
types.

For more technical background on this topic, the following resources
may be useful:

  * `Constructing Recursion Operators in Type Theory, L. Paulson, Journal of Symbolic Computation (1986) 2, 325-355 <https://core.ac.uk/download/pdf/81965996.pdf>`_

  * `Modeling General Recursion in Type Theory, A. Bove & V. Capretta,
    Mathematical Structures in Computer Science (2005)
    <http://www.duplavis.com/venanzio/publications/General_Recursion_MSCS_2005.pdf>`_

Thanks to Aseem Rastogi, Chantal Keller, and Catalin Hritcu, for
providing some of the F* libraries presented in this chapter.

  * `FStar.WellFounded.fst <https://github.com/FStarLang/FStar/blob/master/ulib/FStar.WellFounded.fst>`_

  * `FStar.LexicographicOrdering <https://github.com/FStarLang/FStar/blob/master/ulib/FStar.LexicographicOrdering.fsti>`_



Well-founded Relations and Accessibility Predicates
---------------------------------------------------

A binary relation :math:`R` on elements of type :math:`T` is
well-founded if there is no infinite sequence :math:`x_0, x_1, x_2,
...`, such that :math:`x_i~R~x_{i + 1}`, for all :math:`i`.

As explained :ref:`earlier <Part1_termination>`, when typechecking a
recursive function ``f``, F* requires the user to provide a *measure*,
some function of the arguments of `f`, and checks that on a recursive
call, the measure of the arguments is related to the measure of the
formal parameters a built-in well-founded relation on F* terms. Since
well-founded relations have no infinite descending chains, every chain
of recursive calls related by such a relation must eventually
terminate. However, this built-in well-founded relation, written
``<<`` or ``precedes``, is a derived notion.

In its most primitive form, the well-foundedness of a relation can be
expressed in terms of an inductive type ``acc`` (short for
"accessible") shown below.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: acc$
   :end-before: //SNIPPET_END: acc$

The type ``acc`` is parameterized by a type ``a``; a binary relation
``r: a -> a -> Type`` on ``a``; and an element of the type
``x:a``. Informally, the relation ``r y x`` is provable when ``y``
is "smaller" than ``x``.

The ``acc`` type has just one constructor ``AccIntro``, whose only
argument is a function of type ``y:a -> r y x -> acc r
y``. Intuitively, this says that in order to build an instance of
``acc r x0``, you have to provide a function which can build a proof
of ``acc r x1`` for all ``x1:a`` smaller than ``x0``. The only way to
build such a function is one can avoid infinite regress, is if
the chain ``x0 r x1 r x2 r ...``, eventually terminates in some ``xn``
such that there are no elements smaller than it according to ``r``.

In other words, if one can prove ``acc r x`` for all ``x:a``, then
this precisely captures the condition that there are no infinite
descending ``r``-related chains in ``a``, or that ``r`` is
well-founded. This is exactly what the definition below says, where
``is_well_founded`` is a classical (SMT-automatable) variant of
``well_founded``.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: well_founded$
   :end-before: //SNIPPET_END: well_founded$

Well-founded Recursion
----------------------

Given a relation ``r`` and proof of ``p:acc r x`` , one can define a
recursive function on ``x`` whose termination can be established
purely in terms of structural recursion on the proof ``p``, even
though the function may not itself be structurally recursive on ``x``.

The combinator ``fix_F`` shown below illustrates this at work:

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: fix_F$
   :end-before: //SNIPPET_END: fix_F$

If ``f`` is a function such that every recursive call in the
definition of ``f x`` is on an argument ``y``, such that that ``y`` is
smaller than ``x`` according to some relation ``r``; and if starting
from some argument ``x0``, we have a proof of accessibility ``acc r
x0`` (i.e., no infinite descending ``r``-chains starting at ``x0``),
then the fixpoint of ``f`` can be defined by structural recursion on
the proof of ``accessible_x0``.

  * ``fix_F`` is structurally recursive on ``accessible_x0`` since the
    recursive call is on an element ``h1 y r_yx``, i.e., a child node
    of the (possibly infinitely branching) tree rooted at ``AccIntro h1``.

A slightly simpler version of ``fix_F`` is derivable if ``r`` is
well-founded, i.e., ``r`` is accessible for all elements ``x:a``.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: fix$
   :end-before: //SNIPPET_END: fix$

Some Well-founded Relations
---------------------------

We show how to buid some basic well-founded relations here. For
starters, since F* already internalizes that the ``<`` ordering on
natural numbers as part of its termination check, it is easy to prove
that ``<`` is well-founded.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: lt_nat$
   :end-before: //SNIPPET_END: lt_nat$

We can also define combinators to derive well-founded relations from
other well-founded relations. For example, if a relation ``sub_r`` is
a *sub-relation* of a well-founded relation ``r`` (meaning we have ``r
x y`` whenever we have ``sub_r x y``), then ``sub_r`` is well-founded
too.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: subrel_wf$
   :end-before: //SNIPPET_END: subrel_wf$

Another useful combinator derives the well-foundedness of a relation
``r: binrel b`` if it can be defined as the inverse image under some
function ``f: a -> b`` of some other well-founded relation ``r:
binrel``.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: inverse_image$
   :end-before: //SNIPPET_END: inverse_image$

For example, the ``>`` ordering on negative numbers can be proven
well-founded by defining it as the inverse image of the ``<`` ordering
on natural numbers.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: inverse_image_neg$
   :end-before: //SNIPPET_END: inverse_image_neg$

Termination Checking with Custom Well-founded Relations
-------------------------------------------------------

In the F* library, ``FStar.LexicographicOrdering``, several other
relations are proven to be well-founded, including the lexicographic
ordering on dependent pairs.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: lexicographic_order$
   :end-before: //SNIPPET_END: lexicographic_order$

This order, defined as a ``binrel (x:a & b x)``, and is paramterized
by a binary relation (``r_a``) on ``a`` and a family of relations
(``r_b``) on ``b x``, one for each ``x:a``. It has two cases:

  * ``Left_lex``: The first component of the pair decreases by
    ``r_a``, and the second component is irrelevant.


  * ``Right_lex``: The first component of the pair is invariant, but
    the second component decreases by ``r_b``.

The proof is a little involved (see
``FStar.LexicographicOrdering.fst``), but one can prove that it is
well-founded when ``r_a`` and ``r_b`` are themselves well-founded,
i.e.,

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: lexicographic_order_wf$
   :end-before: //SNIPPET_END: lexicographic_order_wf$

But, with this well-foundedness proof in hand, we can define recursive
functions with our own well-founded orders.

To illustrate, let's define the ``ackermann`` function again (we saw
it first :ref:`here <Part1_lexicographic_orderings>`), this time using
accessibilty and well-founded relations, rather than the built-in
``precedes`` relation.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: ackermann_manual$
   :end-before: //SNIPPET_END: ackermann_manual$

This version is way more verbose than the ackermann we saw
earlier---but this version demonstrates that F*'s built-in support for
the lexicographic orders over the precedes relation is semantically
justified by a more primitive model of well-founded relations

To make user-defined well-founded orderings easier to work with, F*
actually provides a variant of the ``decreases`` clause to work with
well-founded relations. For example, one can use the following syntax
to gain from F*'s built-in from SMT automation and termination
checking, with the expressiveness of using ones own well-founded relation.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: ackermann_wf$
   :end-before: //SNIPPET_END: ackermann_wf$

To explain the syntax:

  * ``decreases {:well-founded p x}``: Here, ``p`` is meant to be an
    instance for
    ``FStar.LexicographicOrdering.well_founded_relation``, applied to
    some term ``x`` built from the formal parameters in scope.

  * In this case, we use the combinator ``L.lex`` to build a
    lexicographic ordering from ``wf_lt_nat`` (coercing it using a
    utility ``coerce_wf`` to turn the definitions used in our tutorial
    chapter here to the types expected by the
    ``FStar.LexicographicOrdering`` library).

We show the coercions below for completeness, though one would not
necessarily need them outside the context of this tutorial.

.. literalinclude:: ../code/Part2.WellFounded.fst
   :language: fstar
   :start-after: //SNIPPET_START: coercions$
   :end-before: //SNIPPET_END: coercions$
