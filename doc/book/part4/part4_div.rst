.. _Part4_Div:

Divergence, or Non-Termination
===============================

Real-world programs are sometimes non-terminating. Think of a
webserver that is listening to incoming requests on a network socket
and servicing them in an infinite loop. Clearly, the top-level loop of
such a webserver cannot be programmed in the total computations world
of F* that we have seen so far.

To allow for non-terminating programs, F* provides a primitive
``Dv`` (for divergence) effect. Computations
in ``Dv`` may not terminate even with infinite resources. In other
words, computations in the ``Dv`` effect have the observational
behavior of non-termination. For example, the following ``loop``
function has type ``unit -> Dv unit`` and it diverges when called::

  let rec loop () : Dv unit = loop ()

(If we remove the ``Dv`` effect label, then F* will default the return
type to ``Tot unit``, and fail as expected.)


Partial correctness semantics of ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Recall :ref:`that <Part1>` we understand the meaning of F* typing
``e:t`` (and ``e:Tot t``) as a proof of correctness of ``e`` with
specification ``t``. When we have ``e:t``, then at runtime, ``e``
terminates and produces a value of type ``t``. This notion is also
called *total correctness*.

With ``Dv`` however, the semantics changes to *partial
correctness*---if F* typechecks an expression ``e:Dv t``, then at
runtime, ``e`` may either diverge (i.e. run forever), or if it terminates
then the resulting value has type ``t`` (i.e. it satisfies the
specification ``t``). The following example is, therefore, untypeable::

  [@@ expect_failure]
  let rec decr (x:int) : Dv nat = if x = 0 then -1 else decr (x - 1)

since ``-1``, the return value if the function terminates, does not
have the annotated type ``nat``. On the other hand, the ``loop``
example from earlier is fine since it never returns at runtime.


Separating the logical core from ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Usually proof-assistants mandate all the programs to be total, and
for good reasons. With divergence, if we are not careful, the logical
system can collapse very easily. For example, following is a
well-typed program in F*::

  let rec helper () : Dv (squash False) = helper ()

that returns a proof of ``False`` (whenever it terminates). So now to
prove any theorem, we only need to call ``helper``, and voilà, we are
done!

Thankfully not so, the effect system of F* itself comes to the rescue.

The effect system carefully separates total computations (in ``Tot``)
from other effectful computations, including ``Dv``. There are several
aspects to it. As mentioned earlier, all expressions are typechecked
to a computation type, with an effect label. Further, the effect
system ensures that ``Tot`` computations cannot have effectful
subcomputations or that effectful computations are not typeable as
``Tot``.

Relying on this separation, F* checks that the logical core can refer
*only* to the total computations. For example, specifications such as
refinements are checked to be total.

And this is what ensures the soundness of the logical fragment of F*
in the presence of arbitrary effects, including ``Dv``. A term ``e:Tot
t`` can be soundly interpreted as the proof of ``t``---the effect
system ensures that it is really so---and ``e:Dv t`` should be
interpreted in the partial correctness semantics.

As an example, the following attempt to use ``helper`` in a total
function fails::

  [@@ expect_failure]
  let zero () : Tot (y:int{y == 0}) = helper (); 1

An attempt to cast ``helper`` to ``Tot`` also fails::

  [@@ expect_failure]
  let helper_tot () : Tot (squash False) = helper ()

Thus, the logical core of F* consists only of the total fragment of
F*. Yet, the fact that we can write non-terminating programs in F*,
cleanly separated from the logical core, makes F* a turing-complete
programming language.


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
``M``---the expression ``add_one x`` in the
example above has effect ``Tot``, but it also has ``Dv`` effect since
``Tot`` can be lifted to ``Dv`` in the effects ordering.

The partial ordering among effects in F* is crucial for the effects to
seamlessly work with each other, we will see more examples when we
discuss user-defined effects.

.. note::

   The logical core of F* includes the ghost effect, so it is also
   separate from the ``Dv`` effect.
