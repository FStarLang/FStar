.. _Part4_Div:

Divergence, or Non-Termination
===============================

Real-world programs are sometimes non-terminating. Think of a
webserver that is listening to incoming requests on a socker and
servicing them in an infinite loop. Clearly, the top-level loop of
such a webserver cannot be programmed in the total computational world
of F* that we have seen so far.

To allow for non-terminating programs, F* provides a primitive
``Dv`` (for divergence) effect, with the semantics that computations
in ``Dv`` may not terminate even with infinite resources. In other
words, computations in the ``Dv`` effect have the observational
behavior of non-termination::

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

With ``Dv`` however, the meaning of ``e:Dv t`` changes to *partial
correctness*---if F* typechecks an expression ``e:Dv t``, then at
runtime, it may either diverge (i.e. run forever), or if it terminates
then the resulting value will have type ``t``. This means the following example
is untypeable::

  [@@ expect_failure]
  let rec decr (x:int) : Dv nat = if x = 0 then -1 else decr (x - 1)

since ``-1``, the return value if the function terminates, does not
have the annotated type ``nat``.


Separating the logical core from ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Many proof-assistants mandate all the programs to be total, and
for good reasons. With divergence, if we are not careful, the logical
system can collapse very easily. For example, following is a
well-typed program in F*::

  let rec helper () : Dv (squash False) = helper ()

that returns a proof of ``False`` (whenever it terminates). So now to
prove any theorem, we only need to call ``helper``, and voilà, we are
done!

Thankfully not so, the effect system of F* itself comes to the rescue.

The effect system separates total computations (in ``Tot``) from other
effectful computations, including ``Dv``, using the effect labels. And
then F* ensures that the logical core of F* can refer only to the
total computations. This means, for example, that the refinement
formulas are total, ``Tot`` computations cannot have ``Dv``
subcomputations, a ``Dv`` computation cannot be typed as a ``Tot``
computation, etc. So an attempt to use ``helper`` to prove something
unsound thankfully fails::

  [@@ expect_failure]
  let zero () : Tot (y:int{y == 0}) = helper (); 1

If it did not fail, we would have a terminating function whose spec
says that it returns ``0``, but it would return ``1`` at runtime.

An attempt to cast ``helper`` to ``Tot`` also fails::

  [@@ expect_failure]
  let helper_tot () : Tot (squash False) = helper ()

Thus, the logical core of F* consists only of the total fragment of
F*. Yet, the fact that we can write non-terminating programs in F*,
cleanly separated from the logical core, makes F* a turing-complete
programming language.


Lifting of ``Tot`` computations into ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While (for good reasons) F* does not allow ``Dv`` computations to be
typed as/used in ``Tot`` computations, going the other way is totally
fine (pun intended)---always terminating computations are also
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


Let's revisit our :ref:`intuition
<Part4_Computation_Types_And_Tot>` regarding the meaning of ``e:M
t``. Recall that an expression ``e`` can be typed as ``M t`` when
executing ``e`` exhibits *at-most* the effect ``M`` and returns a
value of type ``t``. Effects in F* have a partial-order among them,
where sub-effects (e.g., ``Tot``) can be automatically lifted to
super-effects (e.g., ``Dv``), and this is the intended meaning of
having an effect *at-most* ``M``. The expression ``add_one x`` in the
example above has effect ``Tot``, but it also has effect ``Div``.

The partial-ordering among effects in F* is crucial for the effects to
seamlessly work with each other, we will see more examples when we
discuss the user-defined effects.

.. note::

   The logical core of F* includes the ghost effect, so it is also
   separate from the ``Dv`` effect, as with ``Tot``.
   


   
