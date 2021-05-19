.. _Part1_ch4:

Simple proofs of termination
============================

It's absolutely crucial to the soundness of F*'s core logic that all
functions terminate. Otherwise, one could non-terminating write
functions like this::

  let rec loop (x:unit) : False = loop x

and show that ``loop () : False``, i.e., we'd have a proof term for
``False`` and the logic would collapse.

In the previous chapter, we just saw how to define recursive functions
to :ref:`compute the length of list <Part1_inductives_length>` and to
:ref:`append two lists <Part1_inductives_append>`. We also said
:ref:`earlier <Part1_ch1_arrows>` that all functions in F*'s core are
*total*, i.e., they always return in a finite amount of time. So, you
may be wondering, what is it that guarantees that recursive function
like ``length`` and ``append`` actually terminate on all inputs?

The full details of how F* ensures termination of all functions in its
core involves several elements, including positivity restrictions on
datatype definitions and universe constraints. However, the main thing
that you'll need to understand at this stage is that F* includes a
termination check that applies to the recursive definitions of total
functions. The check is a semantic check, not a syntactic criterion,
like in some other dependently typed languages.

We quickly sketch the basic structure of the F\* termination check on
recursive functions---you'll need to understand a bit of this in order
to write more interesting programs.

A well-founded partial order on terms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In order to prove a function terminating in F\* one provides a
*measure*: a pure expression depending on the function's
arguments. F\* checks that this measure strictly decreases on each
recursive call.  The measure for the arguments of the call is compared
to the measure for the previous call according to a well-founded
partial order on F\* terms. We write `v1 << v2` when `v1` _precedes_
`v2` in this order.

.. note::

   A relation `R` is a well-founded partial order on a set `S` if, and
   only if, `R` is a partial order on `S` and there are no infinite
   descending chains in `S` related by `R`. For example, taking `S` to
   be `nat`, the set of natural numbers, the integer ordering `<` is a
   well-founded partial order (in fact, it is a total order).

Since the measure strictly decreases on each recursive call, and there
are no infinite descending chains, this guarantees that the function
eventually stops making recursive calls, i.e., it terminates.

The precedes relation
.....................

Given two terms ``v₁:t₁`` and ``v₂:t₂``, we can prove ``v₁ << v₂``
if any of the following are true:

1. **The ordering on integers**:

   ``t₁ = nat`` and ``t₂ = nat`` and ``v₁ < v₂``

   Negative integers are not related by the `<<` relation, which is
   only a _partial_ order.

2. **The sub-term ordering on inductive types**

    If ``v₂ = D u₁ ... uₙ``, where ``D`` is a constructor of an
    inductive type fully applied to arguments ``uₙ`` to ``uₙ``, then
    ``v1 << v2`` if either

    * ``v₁ = uᵢ`` for some ``i``, i.e., ``v₁`` is a sub-term of ``v₂``

    * ``v₁ = uᵢ x`` for some ``i`` and ``x``, i.e., ``v₁`` is the
      result of applying a sub-term of ``v₂`` to some argument ``x``.


Why ``length`` terminates
^^^^^^^^^^^^^^^^^^^^^^^^^

Let's look again at the definition of ``length`` and see how F* checks
that it terminates, i.e.,

.. literalinclude:: exercises/Ch3.fst
   :language: fstar
   :start-after: //SNIPPET_START: length
   :end-before: //SNIPPET_END: length

First off, the definition of ``length`` above makes use of various
syntactic shorthands to hide some details. If we were to write it out
fully, it would be as shown below:

.. code-block:: fstar

   let rec length #a (l:list a)
     : Tot nat (decreases l)
     = match l with
       | [] -> 0
       | _ :: tl -> length tl

The main difference is on the second line. As opposed to just writing
the result type of ``length``, in full detail, we write
``Tot nat (decreases l)``. This states two things

* The ``Tot nat`` part states that ``length`` is a total function
  returning a ``nat``, just as the ``nat`` did before.

* The additional ``(decreases l)`` specifying a *measure*, i.e., the
  quantity that decreases at each recursive call according the
  well-founded relation ``<<``.

To check the definition, F* gives the recursively bound name
(``length`` in this case) a type that's guarded by the measure. I.e.,
for the body of the function, ``length`` has the following type:

.. code-block:: fstar

   #a:Type -> m:list a{ m << l } -> nat

This is to say that when using ``length`` to make a recursive call, we
can only apply it to an argument ``m << l``, i.e., the recursive call
can only be made on an argument ``m`` that precedes the current
argument ``l``. This is enough to ensure that the recursive calls will
eventually bottom out, since there are no infinite descending chains
related by ``<<``.

In the case of ``length``, we need to prove at the recursive call
``length tl`` that ``tl : (m : list a { m << l }``, or, equivalently
that ``tl << l`` is valid. But, from the sub-term ordering on
inductive types, ``l = Cons _ tl``, so ``tl << l`` is indeed provable
and everything checks out.

Lexicographic orderings
^^^^^^^^^^^^^^^^^^^^^^^

F* also provides a convenience to enhane the well-founded ordering
``<<`` to lexicographic combinations of ``<<``. That is, given terms
``v₁, ..., vₙ`` and ``u₁, ..., uₙ``, F* accepts that the
following lexicographic ordering::

   v₁ << u₁ ‌‌\/ (v₁ == u₁ /\ (v₂ << u₂ ‌‌\/ (v₂ == u₂ /\ ( ... vₙ << uₙ))))

is also well-founded. In fact, it is possible to prove in F* that this
ordering is well-founded, provided ``<<`` is itself well-founded.

Lexicographic ordering are common enough that F* provides special
support to make it convenient to use them. Let's have a look at the
classic ``ackermann`` function.

.. literalinclude:: exercises/Termination.fst
   :language: fstar
   :start-after: SNIPPET_START: ackermann
   :end-before: SNIPPET_END: ackermann

Why does it terminate? At each recursive call, it is *not* the case that
all the arguments are strictly less than the arguments at the previous
call, e.g, in the second branch, `n` increases from `0` to `1`. However,
this function does in fact terminate, and F\* proves that it does.

The reason is that although each argument does not decrease in every
recursive call, when taken together, the ordered pair of arguments `(m,n)`
does decrease according to a *lexical ordering* on pairs.

In its standard prelude, F\* defines the following inductive type:
