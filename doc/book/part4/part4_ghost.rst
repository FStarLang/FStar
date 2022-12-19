.. _Part4_Ghost:

Erasure and the Ghost Effect
============================

When writing proof-oriented programs, inevitably, some parts of the
program are there only to state and prove properties about the code
that actually executes. Our first *effect* separates the
computationally relevant parts of the program from the computationally
irrelevant, specificational or *ghost* parts of a program. This
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


Superficially, because of the implicit arguments, it may look like
concatenating vectors with ``append`` is just as efficient as a
concatenating lists---the length indexes seem to impose no
overhead. But, let's look at the code that F* extracts to OCaml:

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
vectors. What we need is a principled way to indicate to the F*
compiler that some parts of a computation are actually only there for
specification or proof purposes and that they can be removed when
compiling the code without changing the observable result computed by
the program. This is what *erasure* is about---removing the
computationally irrelevant parts of a term for compilation.
