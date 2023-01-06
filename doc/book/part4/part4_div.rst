.. _Part4_Div:

Divergence, or Non-Termination
===============================

Consider programming a webserver, whose top-level loop takes a network
socket as argument, reads an HTTP request from it, services the
request, sends the response on the socket, and iterates. Can we program this top-level loop in F*? Let's
try. Assume that we have the following API available::

  val receive : socket -> http_request
  val process : http_request -> http_response
  val send : socket -> http_response -> unit

(The API is only for illustration, in reality ``receive``,
``process``, and ``send`` will be effectful functions rather than
``Tot``.)

We may try writing the top-level loop as a recursive function::

  let rec main (s:socket) : unit =
    let req = receive s in
    let resp = process req in
    send s resp;
    main s  // trouble!

Unfortunately, this doesn't work: F*
would like us to prove that ``main`` terminates, whereas we,
intentionally, want to write a non-terminating function.

The ``Dv`` effect
^^^^^^^^^^^^^^^^^^^

To allow for such non-terminating programs, F* provides a primitive
``Dv`` (for divergence) effect. Computations
in ``Dv`` may not terminate, even with infinite resources. In other
words, computations in the ``Dv`` effect have the observational
behavior of non-termination. For example, the following ``loop``
function has type ``unit -> Dv unit`` and it always diverges when
called::

  let rec loop () : Dv unit = loop ()

(If we remove the ``Dv`` effect label, then F* will default the return
type to ``Tot unit``, and fail as expected.)

Since the ``Dv`` effect admits divergence, F* essentially turns-off
the termination checker when typechecking ``Dv`` computations. So the
recursive ``loop ()`` call does not require a decreasing termination
metric and typechecks as is.

Now the ``main`` function of our webserver can be annotated in the
``Dv`` effect, and we can program it as an infinite loop::

  let main (s:socket) : Dv unit = ...


Partial correctness semantics of ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Recall :ref:`that <Part1>` we understand the meaning of F* typing
``e:t`` (and ``e:Tot t``) as a proof of correctness of ``e`` with
specification ``t``. If ``e:t``, then at runtime, ``e``
terminates and produces a value of type ``t``. This notion is also
called *total correctness* of ``e`` w.r.t. the specification ``t``.

With ``Dv`` however, the interpretation changes to *partial
correctness*---if F* typechecks an expression ``e:Dv t``, then at
runtime, ``e`` may either diverge (i.e. run forever), or if it terminates
then the resulting value has type ``t`` (i.e. it satisfies the
specification ``t``). The following example is, therefore, untypeable::

  [@@ expect_failure]
  let rec decr (x:int) : Dv nat = if x = 0 then -1 else decr (x - 1)

since ``-1``, the return value if the function terminates, does not
have the annotated type ``nat``. On the other hand, if we changed it
to::

  let rec decr (x:int) : Dv nat = if x = 0 then 0 else decr (x - 1)

then the function typechecks, and we can conclude that for any
``x:int``, ``decr x`` either diverges or returns a ``nat``. We may
further refine the return type to ``y:nat{y == 0}``, and conclude a
more precise characterization of ``decr``.

Separating the logical core from ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Usually proof-assistants mandate all the programs to be total, and
for good reasons. With divergence, if we are not careful, the logical
system can collapse very easily. For example, following is a
well-typed program in F*::

  let rec helper () : Dv False = helper ()

that returns a proof of ``False`` (whenever it terminates). So now, to
prove any theorem in F*, we can call ``helper``, and voilà, we are done!

Thankfully not so, the effect system of F* itself comes to the
rescue. It carefully separates total computations (in
``Tot``) from other effectful computations, including ``Dv``.

As mentioned earlier, all expressions are typechecked
to a computation type with an effect label, where the effect label
soundly captures all the effects of the typed expression. It implies
that, for example, ``Tot`` computations cannot have effectful
subcomputations and that effectful computations are not typeable as
``Tot`` (if they were, then the effect label is not sound w.r.t. the
effects of the computation).

Relying on this separation, F* checks that the logical core can refer
*only* to the total computations. For example, specifications such as
refinements are checked to be total.

And this is what ensures the soundness of the logical fragment of F*
in the presence of arbitrary effects, including ``Dv``. A term ``e:Tot
t`` can be soundly interpreted as the proof of ``t``---the effect
system ensures that it is really so---whereas a judgment like ``e:Dv
t`` should be interpreted in the partial correctness semantics.

As an example, the following attempt to use ``helper`` in a total
function fails::

  [@@ expect_failure]
  let zero () : Tot (y:int{y == 0}) = helper (); 1

An attempt to cast ``helper`` to ``Tot`` also fails::

  [@@ expect_failure]
  let helper_tot () : Tot False = helper ()

Thus, the logical core of F* consists only of the total fragment of
F*. Yet, the fact that we can write non-terminating programs in F*,
cleanly separated from the logical core, makes F* a `Turing-complete
<https://en.wikipedia.org/wiki/Turing_completeness/>`_.
programming language.

No extrinsic proofs for ``Dv`` computations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

One important consequence of any effectful code, including ``Dv``,
being outside the logical core of F* is that it is not possible to do
:ref:`extrinsic proofs <Part1_intrinsic_extrinsic>` about
effectful code. As a result, all logical properties of interest must
be encoded in the specifications of the effectful code. For example,
if we wrote a ``factorial`` definition in ``Dv``::

  let rec factorial (x:int) : Dv int =
    if x = 0
    then 1
    else x * factorial (x - 1)

that diverges when called with negative inputs, then with
the given signature, we cannot derive after-the-fact that
``factorial`` returns a positive integer if it terminates. To be able
to reason so, we need to refine the return type and prove it
intrinsically::

  let rec factorial (x:int) : Dv (y:int{y >= 1}) = ...


Lifting of ``Tot`` computations into ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While F* does not allow ``Dv`` computations to be
typed as/used in ``Tot`` computations, going the other way is *totally*
fine. Intuitively, always terminating computations are
potentially non-terminating. We can think of it like a *weakening* of
the specification::

  let add_one (x:int) : int = x + 1
  let add_one_div (x:int) : Dv int = add_one x

The effect system of F* automatically *lifts* ``Tot`` computations
into ``Dv``, meaning that ``Tot`` functions can be seamlessly used in
``Dv`` functions::

  let rec add_one_loop (x:int) : Dv int =
    let y = add_one x in
    add_one_loop y


In general, effects in F* have a partial ordering among them,
where sub-effects (e.g., ``Tot``) can be automatically lifted to
super-effects (e.g., ``Dv``) by the F* effect system.

This also explains the meaning of :ref:`at-most
<Part4_Computation_Types_And_Tot>` when intuitively understanding the
meaning of ``e:M t``. Executing ``e`` should exhibit *at-most* the effect
``M``---if the effect of ``e`` at runtime is ``N``, then ``N <= M`` in
the partial ordering. In our example, the expression
``add_one x`` has effect ``Tot``, but it may also be typed as ``Dv``
since ``Tot`` is below ``Dv`` in the partial ordering.

The partial ordering among effects in F* is crucial for the effects to
seamlessly work with each other, we will see more examples when we
discuss user-defined effects.

.. note::

   The logical core of F* also includes the ghost effect. We can think
   of the partial order for the effects we have seen so far as: ``Tot
   < GTot < Dv``.
