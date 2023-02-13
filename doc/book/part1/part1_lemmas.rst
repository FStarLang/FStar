.. _Part1_lemmas:

Lemmas and proofs by induction
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


Introducing lemmas
^^^^^^^^^^^^^^^^^^

A lemma is a function in F* that always returns the ``():unit``
value. However, the type of lemma carries useful information about
which facts are provable.

Here's our first lemma:

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_is_positive
   :end-before: //SNIPPET_END: factorial_is_positive

There's a lot of information condensed in that definition. Let's spell
it out in detail:

* ``factorial_is_positive`` is a recursive function with a parameter ``x:nat``

* The return type of ``factorial_is_positive`` is a refinement of
  unit, namely ``u:unit{factorial x > 0}``.  That says that the
  function always returns ``()``, but, additionally, when
  ``factorial_is_positive x`` returns (which it always does, since it
  is a total function) it is safe to conclude that ``factorial x >
  0``.

* The next three lines prove the lemma using a proof by induction on
  ``x``. The basic concept here is that by programming total
  functions, we can write proofs about other pure expressions. We'll
  discuss such proofs in detail in the remainder of this section.

.. _Part1_lemma_syntax:

Some syntactic shorthands for Lemmas
....................................

Lemmas are so common in F* that it's convenient to have special syntax
for them. Here's another take at our proof by ``factorial x > 0``

.. literalinclude:: ../code/Part1.Lemmas.fst
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

When the precondition ``pre`` is trivial, it can be omitted. One can
just write:

.. code-block:: fstar

   Lemma (ensures post)

or even

.. code-block:: fstar

   Lemma post


A proof by induction, explained in detail
.........................................

Let's look at this lemma in detail again—why does it convince F* that
``factorial x > 0``?

.. literalinclude:: ../code/Part1.Lemmas.fst
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

Exercises: Lemmas about integer functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`Click here <../code/exercises/Part1.Lemmas.fst>`_ for the exercise file.

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

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: factorial_is_greater_than_arg
       :end-before: SNIPPET_END: factorial_is_greater_than_arg


Exercise 2
..........

Try proving the following lemmas about ``fibonacci``:

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: fibonacci_question
   :end-before: SNIPPET_END: fibonacci_question

.. container:: toggle

    .. container:: header

       **Answer** (Includes two proofs and detailed explanations)

    .. literalinclude:: ../code/Part1.Lemmas.fst
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

    .. literalinclude:: ../code/Part1.Lemmas.fst
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

Exercise: A lemma about append
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:ref:`Earlier <Part1_inductives_append>`, we saw a definition of
``append`` with the following type:

.. code-block:: fstar

  val append (#a:Type) (l1 l2:list a)
    : l:list a{length l = length l1 + length l2}

Now, suppose we were to define `app``, a version of ``append`` with a
weaker type, as shown below.

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: def append alt
   :end-before: //SNIPPET_END: def append alt

Can you prove the following lemma?

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: //SNIPPET_START: sig app_length
   :end-before: //SNIPPET_END: sig app_length

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: def app_length
       :end-before: SNIPPET_END: def app_length

.. _Part1_intrinsic_extrinsic:

Intrinsic vs extrinsic proofs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As the previous exercise illustrates, you can prove properties either
by enriching the type of a function or by writing a separate lemma
about it---we call these the 'intrinsic' and 'extrinsic' styles,
respectively. Which style to prefer is a matter of taste and
convenience: generally useful properties are often good candidates for
intrinsic specification (e.g, that ``length`` returns a ``nat``); more
specific properties are better stated and proven as lemmas. However,
in some cases, as in the following example, it may be impossible to
prove a property of a function directly in its type---you must resort
to a lemma.

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: reverse
   :end-before: SNIPPET_END: reverse

Let's try proving that reversing a list twice is the identity
function.  It's possible to *specify* this property in the type of
``reverse`` using a refinement type.

.. code-block:: fstar

   val reverse (#a:Type) : f:(list a -> list a){forall l. l == f (f l)}

.. note::

   A subtle point: the refinement on ``reverse`` above uses a
   :ref:`propositional equality
   <Part1_ch2_propositional_equality>`. That's because equality on
   lists of arbitrary types is not decidable, e.g., consider ``list
   (int -> int)``.  All the proofs below will rely on propositional
   equality.

However, F* refuses to accept this as a valid type for ``reverse``:
proving this property requires two separate inductions, neither of
which F* can perform automatically.

Instead, one can use two lemmas to prove the property we care
about. Here it is:

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: reverse_involutive
   :end-before: SNIPPET_END: reverse_involutive

In the ``hd :: tl`` case of ``rev_involutive`` we are explicitly
applying not just the induction hypothesis but also the ``snoc_cons``
auxiliary lemma also proven there.

Exercises: Reverse is injective
...............................

`Click here <../code/exercises/Part1.Lemmas.fst>`_ for the exercise file.

Prove that reverse is injective, i.e., prove the following lemma.

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: sig rev_injective
   :end-before: SNIPPET_END: sig rev_injective

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: def rev_injective
       :end-before: SNIPPET_END: def rev_injective

    That's quite a tedious proof, isn't it. Here's a simpler proof.

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: rev_injective_alt
       :end-before: SNIPPET_END: rev_injective_alt

    The ``rev_injective_alt`` proof is based on the idea that every
    invertible function is injective. We've already proven that
    ``reverse`` is involutive, i.e., it is its own inverse. So, we
    invoke our lemma, once for ``l1`` and once for ``l2``.  This gives
    to the SMT solver the information that ``reverse (reverse l1) =
    l1`` and ``reverse (reverse l2) = l2``, which suffices to complete
    the proof. As usual, when structuring proofs, lemmas are your
    friends!

Exercise: Optimizing reverse
............................

Earlier, we saw how to implement :ref:`a tail-recursive variant
<Part1_termination_reverse>` of ``reverse``.

.. literalinclude:: ../code/Part1.Termination.fst
       :language: fstar
       :start-after: SNIPPET_START: rev
       :end-before: SNIPPET_END: rev

Prove the following lemma to show that it is equivalent to the
previous non-tail-recursive implementation, i.e.,

.. code-block:: fstar

   val rev_is_ok (#a:_) (l:list a) : Lemma (rev [] l == reverse l)

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: rev_is_ok
       :end-before: SNIPPET_END: rev_is_ok

Exercise: Optimizing Fibonacci
..............................


Earlier, we saw how to implement :ref:`a tail-recursive variant
<Part1_termination_fibonacci>` of ``fibonacci``---we show it again below.

.. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: fib_tail$
       :end-before: SNIPPET_END: fib_tail$

Prove the following lemma to show that it is equivalent to the
non-tail-recursive implementation, i.e.,

.. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: val fib_tail_is_ok$
       :end-before: SNIPPET_END: val fib_tail_is_ok$                     

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: fib_is_ok$
       :end-before: SNIPPET_END: fib_is_ok$

.. _Part1_higher_order_functions:

Higher-order functions
^^^^^^^^^^^^^^^^^^^^^^^

Functions are first-class values—they can be passed to other functions
and returned as results. We've already seen some examples in the
section on :ref:`polymorphism
<Part1_polymorphism_and_inference>`. Here are some more, starting with
the ``map`` function on lists.

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: map
   :end-before: SNIPPET_END: map

It takes a function ``f`` and a list ``l`` and it applies ``f`` to
each element in ``l`` producing a new list. More precisely ``map f
[v1; ...; vn]`` produces the list ``[f v1; ...; f vn]``. For example:

.. code-block:: fstar

   map (fun x -> x + 1) [0; 1; 2] = [1; 2; 3]


Exercise: Finding a list element
................................

Here's a function called ``find`` that given a boolean function ``f``
and a list ``l`` returns the first element in ``l`` for which ``f``
holds. If no element is found ``find`` returns ``None``.

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: find
   :end-before: SNIPPET_END: find

Prove that if ``find`` returns ``Some x`` then ``f x = true``. Is it
better to do this intrinsically or extrinsically? Do it both ways.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: sig find
       :end-before: SNIPPET_END: sig find

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: find_alt
       :end-before: SNIPPET_END: find_alt

Exercise: fold_left
...................

Here is a function ``fold_left``, where::

   fold_left f [b1; ...; bn] a = f (bn, ... (f b2 (f b1 a)))

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: def fold_left
   :end-before: SNIPPET_END: def fold_left

Prove the following lemma:

.. literalinclude:: ../code/Part1.Lemmas.fst
   :language: fstar
   :start-after: SNIPPET_START: sig fold_left_Cons_is_rev
   :end-before: SNIPPET_END: sig fold_left_Cons_is_rev

.. container:: toggle

    .. container:: header

       Hint: This proof is a level harder from what we've done so far.
             You will need to strengthen the induction hypothesis, and
             possibly to prove that ``append`` is associative and that
             ``append l [] == l``.

       **Answer**

    .. literalinclude:: ../code/Part1.Lemmas.fst
       :language: fstar
       :start-after: SNIPPET_START: fold_left_Cons_is_rev
       :end-before: SNIPPET_END: fold_left_Cons_is_rev
