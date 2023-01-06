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

Of course, the code would be cleaner if F* were to have entirely
removed the argument instead of leaving behind a unit term, but we
leave it to the downstream compiler, e.g., OCaml itself, to remove
these needless units. Further, if we're compiling the ML code
extracted from F* to C, then KaRaMeL does remove these additional
units in the C code it produces.


Ghost: A Primitive Effect
-------------------------

The second, primitive effect in F*'s effect system is the effect of
*ghost* computations, i.e., computation types whose effect label is
``GTot``. [#]_ The label ``GTot`` is strictly above ``Tot`` in the
effect hierarchy, i.e., ``Tot < GTot``. This means that a term with
computation type ``GTot t`` cannot influence the behavior of a term
whose type is ``Tot s``. Conversely, every ``Tot`` computation can be
implicitly promoted to a ``GTot`` computation.

Ghost computations are just as well-behaved as pure, total
terms---they always terminate on all inputs and exhibit no observable
effects, except for the value they return. As such, F*'s logical core
really includes both ``Tot`` and ``GTot`` computations. The
distinction, however, is only relevant when considering how programs
are compiled. Ghost computations are guaranteed to be erased by the
the compiler---the effect hierarchy ``Tot < GTot`` serves to ensure
that erasure ghost terms does not impact the runtime semantics of
compiled, ``Tot`` terms.

Since ``Tot`` terms are implicitly promoted to ``GTot``, it is easy to
designate that some piece of code should be erased. For example, here
is an ghost version of the factorial function:

.. literalinclude:: ../code/FactorialTailRec.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial$
   :end-before: //SNIPPET_END: factorial$

Its definition is identical to the corresponding total function that
we saw earlier, except that we have annotated the return computation
type of the function as ``GTot nat``. This indicates to F* that
``factorial`` is to be erased during compilation, and the F*
type-and-effect checker imposes that no ``Tot`` computation depends on
an application of ``factorial n``.

.. [#] The name ``GTot`` is meant to stand for "Ghost and Total"
       computations, and is pronounced "Gee-Tote". However, it's a
       poor name and is far from self-explanatory. We plan to change
       the name of this effect in the future (e.g., to something like
       ``Spec``, ``Ghost``, or ``Erased``), though this is a breaking
       change to a large amount of existing F* code.

Ghost Computations as Specifications
------------------------------------

A ghost function like ``factorial`` can be used in specifications, as
shown below, in a proof that a tail recursion optimization
``factorial_tail`` is equivalent to ``factorial``.

.. literalinclude:: ../code/FactorialTailRec.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_tail$
   :end-before: //SNIPPET_END: factorial_tail$

This type allows a client to use the more efficient ``fact``, but for
reasoning purposes, one can use the more canonical ``factorial``,
proven equivalent to ``fact``.

In contrast, if we were to try to implement the same specification by
directly using the factorial ghost function, F* complains with a
effect incompatibility error.
      
.. literalinclude:: ../code/FactorialTailRec.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_bad$
   :end-before: //SNIPPET_END: factorial_bad$

The error is:

.. code-block::

   Computed type "r: nat{r == out * factorial n}" and effect "GTot" is
   not compatible with the annotated type "r: nat{r == out * factorial n}"
   effect "Tot"

So, while F* forbids using ghost computations in ``Tot`` contexts, it
seems to be fine with accepting a use of factorial in specifications,
e.g., in the type ``r:nat { r == out * factorial n }``. We'll see in a
moment why this is permitted.

Erasable Types
--------------


Implicit coercions: `reveal` and `hide`
---------------------------------------


Non-informative Types
---------------------


Ghost Effect Promotion
----------------------


Revisiting Vector Concatenation
-------------------------------
