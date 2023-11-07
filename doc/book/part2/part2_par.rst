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

Thanks to Guido Martinez and Danel Ahman, for some of the content in
this chapter.

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

A ``(st a)`` computation is a function which when given an initial
value for the state ``s0`` returns a pair ``(x, s1)`` with the result
of the computation ``x:a`` and a final value for the state ``s1``.

For example, a computation that reads the state, increments it, and
returns the initial value of the state, can be expressed as shown
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
the program below, where we pass ``s0`` to the second call of
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
  stateful computation ``f: st a`` and another computation ``g : a ->
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
   :start-after: //SNIPPET_START: read_and_increment_v1$
   :end-before: //SNIPPET_END: read_and_increment_v1$

Now, you're probably thinking that this version is even worse than
``read_and_increment_v0``! But, the program looks obscure "just"
because it's using a convoluted syntax to call ``bind``. Many
languages, most famously Haskell, provide specialized syntax to
simplify writing computations that work with APIs like ``bind`` and
``return``. F* provides some syntactic sugar to handle this too.

Monadic let bindings
++++++++++++++++++++

The definition below defines a function with a special name
``let!``. Names of this form, the token ``let`` followed by a sequence
of one or more operator characters such as ``!``, ``?``, ``@``, ``$``,
``<``, and ``>`` are monadic let-binding operators. 

.. literalinclude:: ../code/Part2.STInt.fst
   :language: fstar
   :start-after: //SNIPPET_START: let!$
   :end-before: //SNIPPET_END: let!$

With ``let!`` in scope, the following syntactic sugar becomes available:

* Instead of writing ``bind f (fun x -> e)`` you can write ``let! x = f in e``.

* Instead of writing ``bind f (fun _ -> e)`` you can write ``f ;!
  e``, i.e., a semicolon followed the sequence of operator characters
  uses in the monadic let-binding operator.

* Instead of writing ``bind f (fun x -> match x with ...)``, you can
  write ``match! f with ...``

* Instead of writing ``bind f (fun x -> if x then ...)``, you can
  write ``if! f then ...``

See this file `MonadicLetBindings.fst
<https://github.com/FStarLang/FStar/blob/master/examples/misc/MonadicLetBindings.fst>`_
for more details an examples of the syntactic sugar.

Using this syntactic sugar, we come to our final version of
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

.. _Part2_monad_intro:

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

  * Left identity: ``bind (return x) f ~ f``
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

Make the ``st`` type generic, so that instead of the state being fixed
to a single integer value, it can be used with any type for the
state. I.e., define ``st (s:Type) (a:Type) : Type``, where ``s`` is
the type of the state.

Adapt the full development seen above to work with ``st s``, including
proving the various laws.

`Exercise file <../code/exercises/Part2.ST.fst>`__

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.ST.fst
       :language: fstar

--------------------------------------------------------------------------------

Exercise
--------

Monads can be used to model many computational effects, not just
mutable state.  Another common example is to use monads to model
computations that may raise runtime errors. Here's an exercise to help
you see how.

Prove that the ``option`` type can be made into a monad, i.e., define
``bind`` and ``return`` and prove the monad laws.

`Exercise file <../code/exercises/Part2.Option.fst>`__

--------------------------------------------------------------------------------

Computation Trees, or Monads Generically
++++++++++++++++++++++++++++++++++++++++

Each time one defines a monad to model a computational effect, one
usually thinks first of the effectful *actions* involved (e.g.,
reading and writing the state, or raising an error), and then finds a
way to pakage those actions into the interface of monad with
``return`` and ``bind``, and then, to keep things honest, proves that
the implementation satisfies the monad laws.

However, a lot of this is boilerplate and can be done once and for all
by representing effectful computations not just as functions (as we
did with ``st a = int -> a & s``) but instead as an inductive type
that models a *computation tree*, with effectful actions made explicit
at each node in the tree. One can prove that this representation,
sometimes called a *free monad*, is a monad, and then instantiate it
repeatedly for the particular kinds of actions that one may want to
use in given program.

.. note ::

  In this section, we're scratching the surface of a rich area of
  research called *algebraic effects*. While what we show here is not
  a full-blown algebraic effects development (we'll save that for a
  later chapter), here are some other resources about it.

    * `Alg.fst
      <https://github.com/FStarLang/FStar/blob/master/examples/layeredeffects/Alg.fst>`_:
      An F* development with algebraic effects (to be covered in
      detail later).

    * `Koka <https://koka-lang.github.io/koka/doc/index.html>`_, a
      language with algebraic effects at its core

    * A bibliography about `effects
      <https://github.com/yallop/effects-bibliography>`_

We'll start our development of computation trees with a type
describing the signature of a language of actions.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: action_class$
   :end-before: //SNIPPET_END: action_class$

This kind of signature is sometimes called a *type class*, a type
``act:Type``, together with some operations it supports. In this case,
the operations tell us what kind of input and output a given action
expects.

.. note::

   F* also provides support for type classes and inference of type
   class instantiations. This will be described in a later
   chapter. Meanwhile, you can learn more about type classes in F*
   `from the wiki
   <https://github.com/FStarLang/FStar/wiki/Typeclasses-(via-meta-arguments>`_
   and from these `examples
   <https://github.com/FStarLang/FStar/tree/master/examples/typeclasses>`_.

For example, if we were interested in just the read/write actions on a
mutable integer state (as in our ``st a`` example), we could build an
instance of the ``action_class``, as shown below.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: rw_action_class$
   :end-before: //SNIPPET_END: rw_action_class$

However, we can define a type ``tree acts a``, the type of a computation
tree whose effectful actions are from the class ``acts``, completely
generically in the actions themselves.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: tree$
   :end-before: //SNIPPET_END: tree$

A ``tree act a`` has just two cases:

  * Either it is a leaf node, ``Return x``, modeling a computation
    that immediately returns the value ``x``;

  * Or, we have a node ``DoThen act input k``, modeling a computation
    that begins with some action ``act``, to which we pass some input,
    and where ``k`` represents all the possible "continuations" of the
    action, represented by a ``tree act a`` for each possible output
    returned by the action. That is, ``DoThen`` represents a node in
    the tree with a single action and a possibly infinite number of
    sub-trees.

With this representation we can define ``return`` and ``bind``, and
prove the monad laws once and for all.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: return and bind$
   :end-before: //SNIPPET_END: return and bind$

* The ``return`` combinator is easy, since we already have a
  ``Return`` leaf node in the tree type.

* The ``bind`` combinator is a little more interesting, involving a
  structural recursion over the tree, relying (as we did in the
  previous chapter on well-founded recursion) on the property that all
  the trees returned by ``k`` are strictly smaller than the original
  tree ``f``.

To prove the monad laws, we first need to define an equivalence
relation on trees---this relation is not quite just ``==``, since each
continuation in the tree is function which itself returns a tree. So,
we define ``equiv`` blow, relating trees that are both ``Returns``, or
when they both begin with the same action and have
pointwise-equivalent continuations.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: equiv$
   :end-before: //SNIPPET_END: equiv$

.. note::

   We are specifically avoiding the use of :ref:`functional
   extensionality <Part2_funext>` here, a property which allows
   equating pointwise equal :math:`\eta`-expanded functions. We show
   how one can use functional extensionality in this development as an
   advanced exercise.

To prove that ``equiv`` is an equivalence relation, here are lemmas
that prove that it is reflexive, symmetric, and transitive---we see
here a use of the syntactic sugar for logical connectives,
:ref:`introduced in a previous chapter <Part2_connectives>`.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: equiv is an equivalence$
   :end-before: //SNIPPET_END: equiv is an equivalence$

Now, we can prove that ``tree`` satisifies the monad laws with respect
to ``equiv``.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: tree is a monad$
   :end-before: //SNIPPET_END: tree is a monad$

The associativity law, in particular, should make intuitive sense in
that a ``tree acts a`` represents a computation in a canonical fully
left-associative form, i.e., a single action followed by its
continuation. As such, no matter how you associate computations in
``bind``, the underlying representation is always fully
left-associated.

Having defined our computation trees generically, we can use them with
any actions we like. For example, here's our ``read_and_increment``
re-built using computation trees.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: read_and_increment$
   :end-before: //SNIPPET_END: read_and_increment$

Finally, given a computation tree we can "run" it, by interpreting it
as a state-passing function.

.. literalinclude:: ../code/Part2.Free.fst
   :language: fstar
   :start-after: //SNIPPET_START: interp$
   :end-before: //SNIPPET_END: interp$

.. note::

   A main difference between what we've shown here with ``interp`` and
   a general treament of algebraic effects is that rather than
   "bake-in" the interpretation of the individual actions in
   ``interp``, we can also abstract the semantics of the actions using
   an idea similar to exception handling, allowing the context to
   customize the semantics of the actions simply by providing a
   different handler.

Exercise
--------

Prove that the ``interp`` function interprets equivalent trees ``f``
and ``g`` to pointwise equivalent functions.

`Exercise File <../code/exercises/Part2.ComputationTreeEquiv.fst>`__

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.Free.fst
       :language: fstar
       :start-after: //SNIPPET_START: interp_equiv$
       :end-before: //SNIPPET_END: interp_equiv$

--------------------------------------------------------------------------------

Exercise
--------

Instead of proving every time that a function like ``interp`` produces
equivalent results when applied to equivalent trees, using functional
extensionality, we can prove that equivalent trees are actually
provably equal, i.e., ``equiv x y ==> x == y``.

This is a little technical, since although functional extensionality
is a theorem in F*, it is only true of :math:`\eta`-expanded functions.

Try to use ``FStar.FunctionalExtensionality.fsti`` to adapt the
definitions shown above so that we can prove the lemma ``equiv x y ==>
x == y``.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.FreeFunExt.fst
       :language: fstar

--------------------------------------------------------------------------------

Manipulating Computation Trees: Nondeterminism and Concurrency
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

As a final bit, we show that representing computations as trees is not
just useful from a perspective of genericity and code re-use.
Computation trees expose the structure of a computation in a way that
allows us to manipulate it, e.g., interpreting actions in an
alternative semantics.

In this section, we enhance our computation trees to support
non-deterministic choice, i.e., given pair of computations ``l, r:tree
acts a``, we can non-deterministically choose to evaluate ``l`` or
``r``. With this capability, we can also express some models of
concurrency, e.g., a semantics that interleaves imperative actions
from several threads.

Let's start by enhancing our ``tree`` type to now include an node ``Or
l r``, to represent non-deterministic choice between ``l`` and ``r``.

.. literalinclude:: ../code/Part2.Par.fst
   :language: fstar
   :start-after: //SNIPPET_START: tree$
   :end-before: //SNIPPET_END: tree$

As before, we can define ``return`` and ``bind``, this time in
``bind`` we sequence ``g`` after both choices in ``Or``.

.. literalinclude:: ../code/Part2.Par.fst
   :language: fstar
   :start-after: //SNIPPET_START: return and bind$
   :end-before: //SNIPPET_END: return and bind$

What's more interesting is that, in addition to sequential
composition, we can also define parallel composition of a pair of
computations using ``par f g``, as shown below.

.. literalinclude:: ../code/Part2.Par.fst
   :language: fstar
   :start-after: //SNIPPET_START: par$
   :end-before: //SNIPPET_END: par$

There's quite a lot going on here, so let's break it down a bit:

  * The functions ``l_par f g`` and ``r_par f g`` are mutually
    recursive and define an interleaving semantics of the actions in
    ``f`` and ``g``.

  * ``l_par f g`` is left-biased: picking an action from ``f`` to
    execute first (if any are left); while ``r_par f g`` is
    right-biased, picking an action from ``g`` to execute first.

  * Consider the ``DoThen`` case in ``l_par``: if picks the head
    action ``a`` from ``f`` and the recurses in the continuation with
    ``r_par (k x) g``, to prefer executing first an action from ``g``
    rather than ``k x``. The ``DoThen`` case of ``r_par`` is
    symmetric.

  * For ``l_par``, in the non-deterministic choice case (``Or``), we
    interleave either choice of ``f`` with ``g``, and ``r_par`` is
    symmetric.

  * Finally, we define parallel composition ``par f g`` as the
    non-deterministic choice of either the left-biased or right-biased
    interleaving of the actions of ``f`` and ``g``. This fixes the
    semantics of parallel composition to a round-robin scheduling of
    the actions between the threads, but one could imagine
    implementing other kinds of schedulers too.

As before, we can now instantiate our tree with read/write actions and
write some simple programs, including ``par_inc``, a computation that
tries to increment the counter twice in parallel.

.. literalinclude:: ../code/Part2.Par.fst
   :language: fstar
   :start-after: //SNIPPET_START: sample program$
   :end-before: //SNIPPET_END: sample program$

However, there's trouble ahead---because of the interleaving
semantics, we don't actually increment the state twice.

To check, let's define an interpretation function to run our
computations. Since we need to resolve the non-deterministic choice in
the ``Or`` nodes, we'll parameterize our intepreter by a source of
"randomness", an infinite stream of booleans.

.. literalinclude:: ../code/Part2.Par.fst
   :language: fstar
   :start-after: //SNIPPET_START: interp$
   :end-before: //SNIPPET_END: interp$

This interpreter is very similar to our prior interpreter, except in
the ``Or`` case, we read a boolean from ``rand``, our randomness
stream, and choose the left- or right-branch accordingly.

We can run our program on this interpreter and check what it
returns. One way to do this is to make use of F*'s normalizer, the
abstract machine that F* uses to reduce computations during
type-checking. The ``assert_norm p`` feature used below instructs F*
to symbolically reduce the term ``p`` as much as possible and then
check that the result is equivalent to ``True``.

.. note::

   F*'s emacs mode ``fstar-mode.el`` provides some utilites to allow
   reducing terms of F*'s abstract machine and showing the results to
   the user. F*'s tactics also also allow evaluating terms and viewing
   the results---we leave further discussion of these features to a
   future chapter.


.. literalinclude:: ../code/Part2.Par.fst
   :language: fstar
   :start-after: //SNIPPET_START: test_par_inc$
   :end-before: //SNIPPET_END: test_par_inc$

In this case, we ask F* to interpret ``par_inc`` on the interpreter we
just defined. And, indeed, F* confirms that in the final state, we
have incremented the state only once. Due to the round-robin
scheduling of actions, the interpreter has executed both the reads
before both the writes, making one of the reads and one of the writes
redundant.

Exercise
--------

Define an action class that include an increment operation, in
addition to reads and writes. Adapt the interpreter shown above to
work with this action class and prove (using ``assert_norm``) that a
program that contains two parallel atomic increments increments the
state twice.

`Exercise File <../code/exercises/Part2.AtomicIncrement.fst>`__

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.Par.fst
       :language: fstar
       :start-after: //SNIPPET_START: atomic increment$
       :end-before: //SNIPPET_END: atomic increment$

--------------------------------------------------------------------------------

Looking ahead
+++++++++++++

Writing correct programs with side-effects is hard, particularly when
those effects include features like mutable state and concurrency!

What we've seen here is that although we've been able to model the
semantics of these programs, proving that they work correctly is
non-trivial. Further, while we have defined interpreters for our
programs, these interpreters are far from efficient. In practice, one
usually resorts to things like shared-memory concurrency to gain
performance and our interpreters, though mathematically precise, are
horribly slow.

Addressing these two topics is the main purpose of F*'s user-defined
effect system, a big part of the language which we'll cover in a
subsequent section. The effect system aims to address two main needs:

  * Proofs of effectful programs: The effect system enables developing
    effectful programs coupled with *program logics* that enable
    specifying and proving program properties. We'll learn about many
    different kinds of logics that F* libraries provide, ranging from
    classical Floyd-Hoare logics for sequential programs, relational
    logics for program equivalence, weakest precondition calculi, and
    separation logics for concurrent and distributed programs.

  * Effect abstraction: Although programs can be specified and proven
    against a clean mathematical semantics, for efficient execution,
    F* provides mechanisms to hide the representation of an effect so
    that effectful programs can be compiled efficiently to run with
    native support for effects like state, exceptions, concurrency,
    and IO.
