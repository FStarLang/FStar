.. _Part4_Ghost:

Erasure and the Ghost Effect
============================

When writing proof-oriented programs, inevitably, some parts of the
program are there only to state and prove properties about the code
that actually executes. Our first *effect* separates the
computationally relevant parts of the program from the computationally
irrelevant (i.e., specificational or *ghost*) parts of a program. This
separation enables the F* compiler to guarantee that all the ghost
parts of a program are optimized away entirely.

For a glimpse of what all of this is about, let's take a look again at
length-indexed vectors---we saw them first :ref:`here <Part2_vectors>`.

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: vec
   :end-before: //SNIPPET_END: vec

and a function to concatenate two vectors:

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: append
   :end-before: //SNIPPET_END: append

Compare this with concatenating two lists:

.. code-block:: fstar

   let rec list_append #a (l1 l2:list a) =
       match l1 with
       | [] -> []
       | hd::tl -> hd :: list_append tl l2

Superficially, because of the implicit arguments, it may look like
concatenating vectors with ``append`` is just as efficient as a
concatenating lists---the length indexes seem to impose no
overhead. But, let's look at the code that F* extracts to OCaml for
length-indexed vectors.

First, in the definition of the ``vec`` type, since OCaml is not
dependently typed, the ``nat``-index of the F* ``vec`` is replaced by
a ``'dummy`` type argument---that's fine. But, notice that the
``Cons`` constructor contains three fields: a ``Prims.nat`` for the
length of the tail of the list, the head of the list, and then then
tail, i.e., the length of the tail of the list is stored at every
``Cons`` cell, so the ``vec`` type is actually less space efficient
than an ordinary ``list``.

.. literalinclude:: ../code/Vec.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: vec *)
   :end-before: (* SNIPPET_END: vec *)

Next, in the OCaml definition of ``append``, we see that it receives
additional arguments ``n`` and ``m`` for the lengths of the vectors,
and worse, in the last case, it incurs an addition to sum ``n' + m``
when building the result vector. So, ``append`` is also less
time-efficient than ``List.append``.

.. literalinclude:: ../code/Vec.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: append *)
   :end-before: (* SNIPPET_END: append *)

This is particularly unfortunate, since the computational behavior of
``append`` doesn't actually depend on the length indexes of the input
vectors. What we need is a principled way to indicate to the F\*
compiler that some parts of a computation are actually only there for
specification or proof purposes and that they can be removed when
compiling the code, without changing the observable result computed by
the program. This is what *erasure* is about---removing the
computationally irrelevant parts of a term for compilation. Put
another way, erasure involves *slicing* the program to remove all the
irrelevant or dead code.

Here's a revised version of vectors, making use of the ``erased`` type
from the ``FStar.Ghost`` library to indicate to F* which parts must be
erased by the compiler.

.. literalinclude:: ../code/VecErased.fst
   :language: fstar

We'll look into this in much more detail in what follows, but notice
for now that:

  1. The first argument of ``Cons`` now has type ``erased nat``.

  2. The two implicit arguments of ``append`` corresponding the
     indexes of the input vectors also have type ``erased nat``.

And, if we extract this code to OCaml, here's what we get:


.. literalinclude:: ../code/VecErased.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: vec *)
   :end-before: (* SNIPPET_END: vec *)

.. literalinclude:: ../code/VecErased.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: append *)
   :end-before: (* SNIPPET_END: append *)

Notice that the erased arguments have all been turned into the unit
value ``()``, and the needless addition in ``append`` is gone too.

.. note:: 

   Of course, the code would be cleaner if F* were to have entirely
   removed the argument instead of leaving behind a unit term, but we
   leave it to the downstream compiler, e.g., OCaml itself, to remove
   these needless units. Further, if we're compiling the ML code
   extracted from F* to C, then KaRaMeL does remove these additional
   units in the C code it produces.

Tracking Dependences with a Hierarchy of Effects
------------------------------------------------

Recall our goal: We aim to track the irrelevant parts of a program,
ensuring that they remain separate from the part of the program that
gets compiled, i.e., the compiled part of the program should not have
any dependences on the erased part of the program. 

In a paper from 1999 called `A Core Calculus of Dependency
<https://dl.acm.org/doi/pdf/10.1145/292540.292555>`_, Abadi, Banerjee,
Heintze, and Riecke present DCC, a language with a very generic way to
track dependences. DCC's type system has a family of computation types
arranged in hierarchy (a partial order induced by lattice), where a
computations can only depend on other computations whose type is less
than (or equal to) it in the partial order.

Very briefly, DCC includes a family of computation types :math:`T_l`,
where the label :math:`l` ranges over the elements of a lattice
:math:`L`, where some pairs of labels may be related by :math:`l_1
\leq l_2`. The key typing rule in DCC defines how computations compose
sequentially using ``bind x = e1 in e2``: if ``e1`` has type
:math:`T_{l_1}(t)`, then assuming that ``x`` has type :math:`t`,
``e2`` must have a type like :math:`T_{l_2}(t_2)`, where :math:`l_1
\leq l_2`. That is, since ``e2`` *depends* on the result of a
computation ``e1`` at level :math:`l_1`, ``e2``'s type must be at
least at the same level.

The design of F*'s effect system draws inspiration from DCC. The
effect label of an F* computation type is drawn from an open-ended,
user-extensible set of labels, where the labels are organized in a
user-chosen partial order. The rule for composing computations that
have different effect labels are based on a rule similar to DCC's,
though things become more involved due to F*'s dependent types. The
spirit of DCC's main result remains: computations can only depend on
other computations equal to or lower than it in the effect label
hierarchy.


Ghost: A Primitive Effect
-------------------------


   
