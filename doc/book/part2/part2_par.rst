.. _Part2_par:

A First Model of Computational Effects
======================================

As a final chapter in this section, we show how inductive types can be
used model not just data, but also *computations*, including
computations with side effects, like mutable state and shared-memory
concurrency. This is meant to also give a taste of the next section in
this book, which deals with modeling and proving properties of
programs with effects and F*'s user-extensible system of indexed
effects.

A First Taste: The State Monad
++++++++++++++++++++++++++++++

All the programs we've written so far have been purely
functional. However, one can model programs that manipulate mutable
state within a purely functional language, and one common but powerful
way to do this is with something called a *monad*, an idea that was
introduced to functional programmers in the late 1980s and early 90s
by `Philip Wadler <https://dl.acm.org/doi/10.1145/143165.143169>`_
building on semantic foundations developed by `Eugenio Moggi
<https://ieeexplore.ieee.org/document/39155>`_. If you've been
puzzled about monads before, we'll start from scratch here, and
hopefully this time it will all make sense!

Consider modeling a program that manipulates a single piece of mutable
state, just a single integer that programs can read and write, and
which returns a result of type ``a``. One way to do this is to
represent such a *stateful computation* as a program whose type is
``st a``:

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: st$
   :end-before: //SNIPPET_END: st$

An ``st a`` computation is a function which when given an initial
value for the state ``s0`` returns a pair ``(x, s1)`` with the result
of the computation ``x:a`` and a final value for the state ``s1``.

For example, a computation that read the state, incremented it, and
returned the initial value of the state, could be expressed as shown
below.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: read_and_increment_v0$
   :end-before: //SNIPPET_END: read_and_increment_v0$

This is pretty straightforward, but writing computations in this style
can be quite tedious and error prone. For example, if you wanted to
read the state and increment it twice, one would write:

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: inc_twice_v0$
   :end-before: //SNIPPET_END: inc_twice_v0$

This is quite clumsy, since at each call to ``read_and_increment_v0``
we had to be careful to pass it the "the most recent version" of the
state. For instance, a small typo could easily have caused us to write
the program below, where we pass ``s0`` to the second can of
``read_and_increment``, causing the program to only increment the
state once.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: inc_twice_buggy$
   :end-before: //SNIPPET_END: inc_twice_buggy$

The main idea with the state monad is to structure stateful programs
by abstracting out all the plumbing related to manipulating the state,
eliminating some of the tedium and possibilities for errors.

The way this works is by defining a functions to read and write the
state, plus a couple of functions to return a pure value without
reading or writing the state (a kind of an identity function that's a
noop on the state); and a function to sequentially compose a pair of
stateful computations.

* The function ``read : st int`` below, reads the state and returns it,
  without modifying the state.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: read$
   :end-before: //SNIPPET_END: read$

* The function ``write (s1:int) : st unit`` below, sets the state to ``s1`` and
  returns ``() : unit``.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: write$
   :end-before: //SNIPPET_END: write$

* The function ``bind`` is perhaps the most interesting. Given a
  stateful computation ``f: st a`` and another computatoin ``g : a ->
  st b`` which depends on the result of ``f`` and then may read or
  write the state returning a ``b``; ``bind f g`` composes ``f`` and
  ``g`` sequentially, passing the initial state ``s0`` to ``f``, then
  passing its result ``x`` and next state ``s1`` to ``g``.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: bind$
   :end-before: //SNIPPET_END: bind$

* Finally, ``return`` promotes a pure value ``x:a`` into an ``st a``,
  without touching the state.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: return$
   :end-before: //SNIPPET_END: return$

Some stateful programs
----------------------

With these combinators in hand, we can write stateful programs in a
more compact style, never directly manipulating the underlying integer
variable that holds the state directly.

Here's a next attempt at ``read_and_increment``:

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: read_and_increment$
   :end-before: //SNIPPET_END: read_and_increment$

Now, you're probably thinking that this version is even worse than
``read_and_increment_v0``! But, the program looks obscure "just"
because it's using a convoluted syntax to call ``bind``. Many
languages, most famously Haskell, provide specialized syntax to
simplify writing computations that work with APIs like ``bind`` and
``return``. And F* provides some very simple-minded syntax to handle
this too.

* Instead of writing ``bind f (fun x -> e)`` you can write ``x <-- f; e``.

* And, instead of writeing ``bind f (fun _ -> e)``  you can write ``f;; e``.

Using this bit of syntactic sugar, we come to our final version of
``read_and_increment``, where now, hopefully, the imperative-looking
state updates make the intent of our program clear.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: read_and_increment$
   :end-before: //SNIPPET_END: read_and_increment$

Having structured our programs with ``return`` and ``bind``, larger
``st`` computations can be built from smaller ones, without having to
worry about how to plumb the state through---that's handled once and
for all by our combinators.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: inc_twice$
   :end-before: //SNIPPET_END: inc_twice$

``st`` is a monad
-----------------

It turns out that every API that is structured like our ``st`` is an
instance of a general pattern called a *monad*, an algebraic
structure. Specifically, a monad consists of:

  * A type operator ``m : Type -> Type``
  * A function ``return (#a:Type) (x:a) : m a``
  * A function ``bind (#a #b:Type) (f:m a) (g: a -> m b) : m b``

which satisfy the following laws, where `~` is some suitable
equivalence relation on ``m a``

  * Left identity: ``bind (return x) f ~ g``
  * Right identity: ``bind f return ~ f``
  * Associativity: ``bind f1 (fun x -> bind (f2 x) f3) ~ bind (bind f1 f2) g``

Its easy to prove that ``st``, ``return``, and ``bind`` satisfy these
laws in F*, where we pick the equivalence relation to equate functions
that take equal arguments to equal results.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: monad_laws$
   :end-before: //SNIPPET_END: monad_laws$

These laws are practically useful in that they can catch bugs in our
implementations of the combinators. For instance, suppose we were to
write ``bind_buggy`` below, which like in ``inc_twice_buggy``,
mistakenly re-uses the old state ``s0`` when calling ``g``---in this
case, the ``right_identity`` law below cannot be proved.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: bind_buggy$
   :end-before: //SNIPPET_END: bind_buggy$

We can also prove laws about how the stateful actions, ``read`` and
``write``, interact with each other in sequential composition.

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: action_laws$
   :end-before: //SNIPPET_END: action_laws$

That completes our tour of our very first monad, the state monad.

Exercise
--------

Make the ``st`` type generic, so that instead of the state being fixed to
a single integer value, it can be used with any type for the
state. I.e., define ``st (s:Type) (a:Type) : Type``, where ``s`` is
the type of the state.

Adapt the full development seen above to work with ``st s``, incluing
proving the various laws.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.ST.fst
       :language: fstar

--------------------------------------------------------------------------------

Computation Trees
+++++++++++++++++
