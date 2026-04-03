.. _Pulse_Ghost:

Ghost Computations
==================

Throughout the chapters on pure F*, we made routine use of the
``Lemmas`` and ghost functions to prove properties of our
programs. Lemmas, you will recall, are pure, total functions that
always return ``unit``, i.e., they have no computational significance
and are erased by the F* compiler. F* :ref:`ghost functions
<Part4_Ghost>` are also pure, total functions, except that they are
allowed to inspect erased values in a controlled way---they too are
erased by the F* compiler.

As we've seen already, F* lemmas and ghost functions can be directly
used in Pulse code. But, these are only useful for describing
properties about the pure values in scope. Often, in Pulse, one needs
to write lemmas that speak about the state, manipulate ``slprops``,
etc. For this purpose, Pulse provides its own notion of *ghost
computations* (think of these as the analog of F* lemmas and ghost
functions, except they are specified using ``slprops``); and *ghost
state* (think of these as the analog of F* erased types, except ghost
state is mutable, though still computationally irrelevant). Ghost
computations are used everywhere in Pulse---we've already seen a few
example. Ghost state is especially useful in proofs of concurrent
programs.


Ghost Functions
...............

Here's a Pulse function that fails to check, with the error message
below.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //incr_erased_non_ghost$
   :end-before: //end incr_erased_non_ghost$

.. code-block::

    Cannot bind ghost expression reveal x with ST computation

We should expect this to fail, since the program claims to be able to
compute an integer ``y`` by incrementing an erased integer ``x``---the
``x:erased int`` doesn't exist at runtime, so this program cannot be
compiled.

But, if we tag the function with the ``ghost`` qualifier, then this
works:


.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //incr_erased$
   :end-before: //end incr_erased$

The ``ghost`` qualifier indicates the the Pulse checker that the
function is to be erased at runtime, so ``ghost`` functions are
allowed to make use of F* functions with ``GTot`` effect, like
``FStar.Ghost.reveal``.

However, for this to be sound, no compilable code is allowed to depend
on the return value of a ``ghost`` function. So, the following code
fails with the error below:

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //try_use_incr_erased$
   :end-before: //end try_use_incr_erased$

.. code-block::

   Expected a term with a non-informative (e.g., erased) type; got int

That is, when calling a ``ghost`` function from a non-ghost context,
the return type of the ghost function must be non-informative, e.g,
``erased``, or ``unit`` etc. The class of non-informative types and
the rules for allowing F* :ref:`ghost computations to be used in total
contexts is described here <Ghost_in_total_contexts>`, and the same
rules apply in Pulse.

To use of ``incr_erased`` in non-ghost contexts, we have to erase its
result. There are a few ways of doing this.

Here's a verbose but explicit way, where we define a nested ghost
function to wrap the call to ``incr_erased``.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //use_incr_erased$
   :end-before: //end use_incr_erased$

The library also contains ``Pulse.Lib.Pervasives.call_ghost`` that is
a higher-order combinator to erase the result of a ghost call.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //use_incr_erased_alt$
   :end-before: //end use_incr_erased_alt$

The ``call_ghost`` combinator can be used with ghost functions of
different arities, though it requires the applications to be curried
in the following way.

Suppose we have a binary ghost function, like ``add_erased``:

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //add_erased$
   :end-before: //end add_erased$

To call it in a non-ghost context, one can do the following:

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //use_add_erased$
   :end-before: //end use_add_erased$

That said, since ``ghost`` functions must have non-informative return
types to be usable in non-ghost contexts, it's usually best to define
them that way to start with, rather than having to wrap them at each
call site, as shown below:

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //add_erased_erased$
   :end-before: //end add_erased_erased$


Some Primitive Ghost Functions
..............................

Pulse ghost functions with ``emp`` or ``pure _`` pre and
postconditions are not that interesting---such functions can usually
be written with regular F* ghost functions.

Ghost functions are often used as proof steps to prove equivalences
among ``slprops``. We saw a few :ref:`examples of ghost functions
before <Pulse_nullable_ref_helpers>`---they are ghost since their
implementations are compositions of ``ghost`` functions from the Pulse
library.

The ``rewrite`` primitive that we saw :ref:`previously
<Pulse_rewriting>` is in fact a defined function in the Pulse
library. Its signature looks like this:

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //__rewrite_sig$
   :end-before:  //end __rewrite_sig$

Many of the other primitives like ``fold``, ``unfold``, etc. are
defined in terms of ``rewrite`` and are ``ghost`` computations.

Other primitives like ``introduce exists*`` are also implemented in
terms of library ``ghost`` functions, with signatures like the one
below:

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //intro_exists_sig$
   :end-before:  //end intro_exists_sig$


.. _Pulse_recursive_predicates:

Recursive Predicates and Ghost Lemmas
.....................................

We previously saw how to :ref:`define custom predicates
<Pulse_DefinedVProps>`, e.g., for representation predicates on data
structures. Since a ``slprop`` is just a regular type, one can also
define ``slprops`` by recursion in F*. Working with these recursive
predicates in Pulse usually involves writing recursive ghost functions
as lemmas. We'll look at a simple example of this here and revisit in
subsequent chapters as look at programming unbounded structures, like
linked lists.

Say you have a list of references and want to describe that they all
contain integers whose value is at most ``n``. The recursive predicate
``all_at_most l n`` does just that:

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: fstar
   :start-after: //all_at_most$
   :end-before:  //end all_at_most$

As we did when working with :ref:`nullable references
<Pulse_nullable_ref_helpers>`, it's useful to define a few helper
ghost functions to introduce and eliminate this predicate, for each of
its cases.


Recursive Ghost Lemmas
++++++++++++++++++++++

Pulse allows writing recursive ghost functions as lemmas for use in
Pulse code. Like F* lemmas, recursive ghost functions must be proven
to terminate on all inputs---otherwise, they would not be sound.

To see this in action, let's write a ghost function to prove that
``all_at_most l n`` can be weakened to ``all_at_most l m`` when ``n <=
m``.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //weaken_at_most$
   :end-before: //end weaken_at_most$               

A few points to note:

  * Recursive functions in Pulse are defined using ``fn rec``.

  * Ghost recursive functions must also have a ``decreases``
    annotation---unlike in F*, Pulse does not yet attempt to infer a
    default decreases annotation. In this case, we are recursing on
    the list ``l``.

  * List patterns in Pulse do not (yet) have the same syntactic sugar
    as in F*, i.e., you cannot write ``[]`` and ``hd::tl`` as
    patterns.

  * The proof itself is fairly straightforward:

    - In the ``Nil`` case, we eliminate the ``all_at_most`` predicate
      at ``n`` and introduce it at ``m``.

    - In the ``Cons`` case, we eliminate ``all_at_most l n``,` use the
      induction hypothesis to weaken the ``all_at_most`` predicate on
      the ``tl``; and then introduce it again, packaging it with
      assumption on ``hd``.

Mutable Ghost References
........................

The underlying logic that Pulse is based on actually supports a very
general form of ghost state based on partial commutative monoids
(PCMs). Users can define their own ghost state abstractions in F*
using PCMs and use these in Pulse programs. The library
``Pulse.Lib.GhostReference`` provides the simplest and most common
form of ghost state: references to erased values with a
fractional-permission-based ownership discipline.

We'll use the module abbreviation ``module GR =
Pulse.Lib.GhostReference`` in what follows. The library is very
similar to ``Pulse.Lib.Reference``, in that it provides:

  * ``GR.ref a``: The main type of ghost references. ``GR.ref`` is an
    erasable type and is hence considered non-informative.

  * ``GR.pts_to (#a:Type0) (r:GR.ref a) (#p:perm) (v:a) : slprop`` is
    the main predicate provided by the library. Similar to the regular
    ``pts_to``, the permission index defaults to ``1.0R``.

  * Unlike ``ref a`` (and more like ``box a``), ghost references
    ``GR.ref a`` are not lexically scoped: they are allocated using
    ``GR.alloc`` and freed using ``GR.free``. Of course, neither
    allocation nor free'ing has any runtime cost---these are just
    ghost operations.

  * Reading a ghost reference using ``!r`` returns an ``erased a``,
    when ``r:GR.ref a``. Likewise, to update ``r``, it is enough to
    provide a new value ``v:erased a``.

  * Operations to ``share`` and ``gather`` ghost references work just
    as with ``ref``.

A somewhat contrived example
++++++++++++++++++++++++++++

Most examples that require ghost state usually involve stating
interesting invariants between multiple threads, or sometimes in a
sequential setting to correlate knowledge among different
components. We'll see examples of that in a later chapter. For now,
here's a small example that gives a flavor of how ghost state can be
used.

Suppose we want to give a function read/write access to a reference,
but want to ensure that before it returns, it resets the value of the
reference to its original value. The simplest way to do that would be
to give the function the following signature:

.. code-block:: pulse

   fn uses_but_resets #a (x:ref a)
   requires pts_to x 'v
   ensures pts_to x 'v

Here's another way to do it, this time with ghost references.

First, we define a predicate ``correlated`` that holds full permission
to a reference and half permission to a ghost reference, forcing them
to hold the same value.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //correlated$
   :end-before: //end correlated$

Now, here's the signature of a function ``use_temp``: at first glance,
from its signature alone, one might think that the witness ``v0``
bound in the precondition is unrelated to the ``v1`` bound in the
postcondition.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //use_temp_sig$
   :end-before: //end use_temp_sig$

But, ``use_temp`` only has half-permission to the ghost reference and
cannot mutate it. So, although it can mutate the reference itself, in
order to return its postcondition, it must reset the reference to its
initial value.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //use_temp_body$
   :end-before: //end use_temp_body$

This property can be exploited by a caller to pass a reference to
``use_temp`` and be assured that the value is unchanged when it
returns.

.. literalinclude:: ../code/pulse/PulseTutorial.Ghost.fst
   :language: pulse
   :start-after: //use_correlated$
   :end-before: //end use_correlated$

