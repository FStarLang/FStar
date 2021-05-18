.. _Part1_lemmas:

Lemmas and Proofs by Induction
==============================

Let's say you wrote the ``factorial`` function and gave it the type
``nat -> nat``. Later, you care about some other property about
``factorial``, e.g., that if ``x > 2`` then ``factorial x > x``. One
option is to revise the type you wrote for ``factorial`` and get F\*
to reprove that it has this type. But this isn't always feasible. What
if you also wanted to prove that if ``x > 3`` then ``factorial x > 2 *
x``. Clearly, polluting the type of ``factorial`` with all these
properties that you may or may not care about is impractical.

You could write assertions to ask F* to check these properties, e.g.,

.. code-block:: fstar

   let _ = assert (forall (x:nat). x > 2 ==> factorial x > 2)

But, F* complains saying that it couldn't prove this fact. That's not
because the fact isn't true—recall, checking the validity of
assertions in F* is undecidable. So, there are facts that are true
that F* may not be able to prove, at least not without some help.

In this case, proving this property about ``factorial`` requires a
proof by induction. F* and Z3 cannot do proofs by induction
automatically—you will have to help F* here by writing a *lemma*.


Lemmas
^^^^^^^

A lemma is a function in F* that always returns the ``():unit``
value. However, the type of lemma carries useful information about
which facts are provable.

Here's our first lemma:

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_is_positive
   :end-before: //SNIPPET_END: factorial_is_positive

There's a lot of information condensed in that definition. Let's spell
it out in detail:

* ``factorial_is_positive`` is a recursive function with a parameter ``x:nat``

* The return type of ``factorial_is_positive`` is a refinement of
  unit, namely ``u:unit{factorial x > 0}``.  That says that the
  function always returns ``()``, but, additionally, when
  ``factorial_is_postive x`` returns (which it always does, since it
  is a total function) it is safe to conclude that ``factorial x >
  0``.

* The next three lines prove the lemma using a proof by induction on
  ``x``. The basic concept here is that by programming total
  functions, we can write proofs about other pure expressions. We'll
  discuss such proofs in detail in the remainder of this section.

Some syntactic shorthands for Lemmas
....................................

Lemmas are so common in F* that it's convenient to have special syntax
for them. Here's another take at our proof by ``factorial x > 0``

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_is_positive_lemma
   :end-before: //SNIPPET_END: factorial_is_positive_lemma

The type ``x:t -> Lemma (requires pre) (ensures post)`` is the type of
a function

* that can be called with an argument ``v:t``
* the argument must satisfies the precondition ``pre[v/x]``
* the function always returns a ``unit``
* and ensures that the postcondition ``post[v/x]`` is valid

The type is equivalent to ``x:t{pre} -> u:unit{post}``.

A proof by induction, explained in detail
.........................................

Let's look at this lemma in detail again—why does it convince F* that
``factorial x > 0``?

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_is_positive_lemma
   :end-before: //SNIPPET_END: factorial_is_positive_lemma

* It is a proof by induction on ``x``. Proofs by induction in F* are
  represented by total recursive functions. The fact that it is total
  is extremely important—it ensures that the inductive argument is
  well-founded, i.e., that the induction hypothesis is only applied
  correctly on strictly smaller arguments.

* The base case of the induction is when ``x=0``. In this case, F* +
  Z3 can easily prove that ``factorial 0 > 0``, since this just
  requires computing ``factorial 0`` to ``1`` and checking ``1 > 0``.

* What remains is the case where ``x > 0``.

* In the inductive case, the type of the recursively bound
  ``factorial_is_pos`` represents the induction hypothesis. In this
  case, its type is

  .. code-block:: fstar

     y:int {y < x} -> Lemma (requires y >= 0) (ensures factorial y > 0)

  In other words, the type of recursive function tells us that for all
  ``y`` that are smaller than that current argument ``x`` and
  non-negative , it is safe to assume that ``factorial y > 0``.

* By making a recursive call on ``x-1``, F* can conclude that
  ``factorial (x - 1) > 0``.

* Finally, to prove that ``factorial x > 0``, the solver figures out
  that ``factorial x = x * factorial (x - 1)``. From the recursive
  lemma invocation, we know that ``factorial (x - 1) > 0``, and since
  we're in the case where ``x > 0``, the solver can prove that the
  product of two positive numbers must be positive.

Exercises
^^^^^^^^^

Exercise 1
..........

Try proving the following lemmas about ``factorial``:

.. code-block:: fstar

   val factorial_is_greater_than_arg (x:int)
     : Lemma (requires x > 2)
             (ensures factorial x > x)

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: exercises/Ch2.fst
       :language: fstar
       :start-after: SNIPPET_START: factorial_is_greater_than_arg
       :end-before: SNIPPET_END: factorial_is_greater_than_arg


Exercise 2
..........

Try proving the following lemmas about ``fibonacci``:

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: SNIPPET_START: fibonacci_question
   :end-before: SNIPPET_END: fibonacci_question

.. container:: toggle

    .. container:: header

       **Answer** (Includes two proofs and detailed explanations)

    .. literalinclude:: exercises/Ch2.fst
       :language: fstar
       :start-after: SNIPPET_START: fibonacci_answer
       :end-before: SNIPPET_END: fibonacci_answer


    Let's have a look at that proof in some detail. It's much like the
    proof by induction we discussed in detail earlier, except now we
    have two uses of the induction hypothesis.

    * It's a proof by induction on ``n:nat{n >= 2}``, as you can tell from the
      ``let rec``.

    * The base cases are when ``n = 2`` and ``n = 3``. In both these
      cases, the solver can simply compute ``fibonacci n`` and check
      that it is greater than ``n``.

    * Otherwise, in the inductive case, we have ``n >= 4`` and the
      induction hypothesis is the type of the recursive function::

        m:nat{m >= 2 /\ m < n} -> Lemma (fibonacci m >= m)

    * We call the induction hypothesis twice and get::

        fibonacci (n - 1) >= n - 1
        fibonacci (n - 2) >= n - 2

    * To conclude, we show::

        fibonacci n = //by definition
        fibonacci (n - 1) + fibonacci (n - 2) >= //from the facts above
        (n - 1) + (n - 2) = //rearrange
        2*n - 3 >=  //when n >= 4
        n

    As you can see, once you set up the induction, the SMT solver does
    a lot of the work.

    Sometimes, the SMT solver can even find proofs that you might not
    write yourself. Consider this alternative proof of ``fibonacci n
    >= n``.

    .. literalinclude:: exercises/Ch2.fst
       :language: fstar
       :start-after: SNIPPET_START: fibonacci_answer_alt
       :end-before: SNIPPET_END: fibonacci_answer_alt

    This proof works with just a single use of the induction
    hypothesis. How come? Let's look at it in detail.

    1. It's a proof by induction on ``n:nat{n >= 2}``.

    2. The base case is when ``n=2``. It's easy to compute ``fibonacci 2``
       and check that it's greater than or equal to 2.

    3. In the inductive case, we have::

        n >= 3

    4. The induction hypothesis is::

         m:nat{m >= 2 /\ m < n} -> Lemma (fibonacci m >= m)

    5. We apply the induction hypothesis to ``n - 1`` and get ::

        fibonacci (n - 1) >= n - 1

    6. We have::

        fibonacci n = //definition
        fibonacci (n - 1) + fibonacci (n - 2) >= //from 5
        (n - 1) + fibonacci (n - 2)

    7. So, our goal is now::

        (n - 1) + fibonacci (n - 2) >= n

    8. It suffices if we can show ``fibonacci (n - 2) >= 1``

    9. From (2) and the definition of ``fibonacci`` we have::

         fibonacci (n - 1) = //definition
         fibonacci (n - 2) + fibonacci (n - 3) >= //from 5
         n - 1 >= // from 3
         2


    10. Now, suppose for contradiction, that ``fibonacci (n - 2) = 0``.

        10.1. Then, from step 9, we have ``fibonacci (n-3) >= 2``

        10.2  If ``n=3``, then ``fibonacci 0 = 1``, so we have a contradiction.

        10.3  If ``n > 3``, then

           10.3.1. ``fibonacci (n-2) = fibonacci (n-3) + fibonacci (n-4)``, by definition

           10.3.2. ``fibonacci (n-3) + fibonacci (n-4) >= fibonacci (n-3)``, since ``fibonacci (n-4) : nat``.

           10.3.3. ``fibonacci (n-2) >= fibonacci (n-3)``, using 10.3.1 and 10.3.2

           10.3.4. ``fibonacci (n-2) >= 2``, using 10.1

           10.3.5. But, 10.3.4 contradicts 10; so the proof is complete.

    You probably wouldn't have come up with this proof yourself, and
    indeed, it took us some puzzling to figure out how the SMT solver
    was able to prove this lemma with just one use of the induction
    hypothesis. But, there you have it. All of which is to say that
    the SMT solver is quite powerful!
