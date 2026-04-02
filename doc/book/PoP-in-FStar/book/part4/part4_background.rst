.. _Part4_Background:

Computation Types to Track Dependences
======================================

A main goal for F*'s effect system is to *track dependences* among the
various parts of a program. For example, the effect system needs to
ensures that the total part of a program that is proven to always
terminate never calls a function in the divergent fragment (since that
function call may loop forever). Or, that the runtime behavior of a
compiled program does not depend on ghost computations that get erased
by the compiler.

In a paper from 1999 called `A Core Calculus of Dependency
<https://dl.acm.org/doi/pdf/10.1145/292540.292555>`_, Abadi et
al. present DCC, a language with a very generic way to track
dependences. DCC's type system includes an indexed, monadic type
:math:`T_l`, where the index :math:`l` ranges over the elements of a
lattice, i.e., the indexes are arranged in a partial order. DCC's type
system ensures that a computation with type :math:`T_l` can depend on
another computation with type :math:`T_m` only if :math:`m \leq l` in
the lattice's partial order.  F*'s effect system is inspired by DCC,
and builds on a 2011 paper by Swamy et al. called `Lightweight Monadic
Programming in ML <https://dl.acm.org/doi/10.1145/2034574.2034778>`_
which develops a DCC-like system for an ML-like programming language.

At its core, F*'s effect system includes the following three elements:

**Computation Types**: F*'s type system includes a notion of
*computation type*, a type of the form ``M t`` where ``M`` is an
*effect label* and ``t`` is the return type of the computation. A term
``e`` can be given the computation type ``M t`` when executing ``e``
exhibits *at-most* the effect ``M`` and (possibly) returns a value of
type ``t``. We will refine this intuition as we go along. In contrast
with computation types, the types that we have seen so far (``unit``,
``bool``, ``int``, ``list int``, other inductive types, refinement
types, and arrows) are called *value types*.

**Partially Ordered Effect Labels**: The effect label of a computation
type is drawn from an open-ended, user-extensible set of labels, where
the labels are organized in a user-chosen partial order. For example,
under certain conditions, one can define the label ``M`` to be a
sub-effect of ``N``, i.e., ``M < N``.  For any pair of labels ``M``
and ``N``, a partial function ``lub M N`` (for least upper bound)
computes the least label greater than both ``M`` and ``N``, if any.

**Typing Rules to Track Dependences**: The key part of the effect
system is a rule for composing computations sequentially using ``let x
= e1 in e2``. Suppose ``e1 : M t1``, and suppose ``e2 : N t2``
assuming ``x:t1``, then the composition ``let x = e1 in e2`` has type
``L t2``, where ``L = lub M N``---if ``lub M N`` is not defined, then
the ``let``-binding is rejected. Further, a computation with type ``M
t`` can be implicitly given the type ``N t``, when ``M < N``, i.e.,
moving up the effect hierarchy is always permitted. The resulting
typing discipline enforces the same dependence-tracking property as
DCC: a computation ``M t`` can only depend on ``N t`` when ``lub M N =
M``.

In full generality, F*'s computation types are more complex than just
an effect label ``M`` and a result type (i.e., more than just ``M
t``), and relying on F*'s dependent types, computation types do more
than just track dependences, e.g., a computation type in F* can also
provide full, functional correctness specifications. The papers
referenced below provide some context and we discuss various elements
of these papers throughout this part of the book.


  + `Verifying Higher-order Programs with the Dijkstra Monad
    <https://dl.acm.org/doi/10.1145/2499370.2491978>`_, introduces the
    idea of a Dijkstra monad, a construction to structure the
    inference of weakest preconditions of effectful computations.
    
  + This 2016 paper,
    `Dependent Types and Multi-Monadic Effects in F* <https://fstar-lang.org/papers/mumon/>`_,
    has become the canonical reference for F\*. It shows how to combine
    multiple Dijkstra monads with a DCC-like system.

  + `Dijkstra Monads for Free
    <https://dl.acm.org/doi/10.1145/3009837.3009878>`_ presents an
    algorithm to construct Dijkstra monads automatically for a class
    of simple monads.

  + `Dijkstra Monads for All
    <https://dl.acm.org/doi/abs/10.1145/3341708>`_ generalizes the
    construction to apply to relate any computational monad to a
    specificational counterpart, so long as the two are related by a
    monad morphism.
    
  + `Programming and Proving with Indexed Effects
    <https://fstar-lang.org/papers/indexedeffects/>`_ describes
    F*'s user-defined effect system in its most general form, allowing
    it to be applied to any indexed effects, including Dijkstra
    monads, but several other constructions as well.
