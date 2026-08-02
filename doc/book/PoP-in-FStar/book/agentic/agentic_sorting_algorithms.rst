.. _Agentic_sorting:

========================
On Abstraction & Rubrics
========================

`A recent blog post <https://risemsr.github.io/blog/2026-03-06-autoclrs/>`_
describes "AutoCLRS", where agents using F* and Pulse were able to formalize
more than 50 algorithms and data structures from `Introduction to Algorithms
<https://mitpress.mit.edu/9780262046305/>`_, a classic textbook by Cormen,
Leiserson, Rivest, and Stein (CLRS).  The formalization includes functional
correctness and worst-case complexity analysis, with the development
available at this `repository <https://github.com/FStarLang/AlgoStar>`_.  In
this chapter, we review the style of proofs developed in AutoCLRS, particularly
for some of the sorting algorithms, and consider how might do them using better
rubrics, templates, and audits.

--------------
Shared Rubrics
--------------

AutoCLRS includes proofs of several sorting algorithms: insertion sort, merge
sort, heap sort, and quicksort (as well as some counting sort variants, which
we'll get to shortly). These four algorithms make use of some shared definitions
for sortedness and permutations, reusing the notion of permutation from an F*
library (Seq.Properties.permutation).

.. code-block:: fstar
    
    let sorted (s: Seq.seq int) : prop
      = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

    let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

Notice that these definitions are specialized to sequences of mathematical
integers: this is perhaps an artifact of formalizing the CLRS textbook as it is,
where the sorting algorithms are presented for integer arrays only.

Each of the four algorithms is implemented in imperative Pulse code with a
specification showing functional correctness. Here below is the specification of
``insertion_sort`` and ``heapsort`` (slightly simplified):

Insertion sort, which says in its preconditions

* The array ``a`` points to a sequence of integers ``s0``; and,

* The length of the array is ``len``, and ``len`` is less than or equal to the
  length of the sequence ``s0``

Then, the postcondition ensures

* The array ``a`` points to a sequence of integers ``s``; and,

* The sequence ``s`` is sorted, and is a permutation of the original sequence
  ``s0``, and has the same length as ``s0``.

.. code-block:: pulse

    fn insertion_sort
        (a: array int)
        (#s0: Ghost.erased (Seq.seq int))
        (len: SZ.t)
    requires 
        a |-> s0 ** 
        pure (
            SZ.v len == Seq.length s0 /\
            Seq.length s0 <= A.length a)
    ensures
        a |-> s ** 
        pure (
            Seq.length s == Seq.length s0 /\
            sorted s /\
            permutation s0 s)

Now, if we look at the specification of heapsort, it says much the same thing,
but with some small differences. For some reason, ``heapsort`` has an additional
precondition on the length, the provided length ``n`` is a lower bound on the
length of the array, and the postcondition is more complicated too, proving only
that the sub-array up to ``n`` is sorted, and that the rest of the array is
unchanged.

.. code-block:: pulse

    fn heapsort
        (a: A.array int)
        (n: SZ.t)
        (#s0: erased (Seq.seq int) {
            SZ.v n <= A.length a /\
            Seq.length s0 == A.length a /\
            SZ.fits (op_Star 2 (Seq.length s0) + 2)
        })
    requires
        a |-> s0
    ensures exists* s.
        a |-> s **
        pure (
            Seq.length s == Seq.length s0 /\
            sorted_upto s (SZ.v n) /\
            permutation s0 s /\
            (forall (k:nat). SZ.v n <= k /\ k < Seq.length s ==> Seq.index s k == Seq.index s0 k)
        )

Although the agents at least used some common definitions of sortedness and
permutation, these differences in the top-level specifications double the
reviewing work---in fact, all four algorithms have subtly different
specifications. 

Of course, one shouldn't tolerate this. A more uniform specification is easier
to vet and review, and it is also easier to reuse in other proofs. Let's write
one:

.. code-block:: pulse

    class array_sort = {
        sort: 
            (fn (#a:Type)
                (arr:array a)
                (len:SZ.t) 
                (ord:Pulse.Lib.TotalOrder.total_order a)
                (#s:erased (Seq.seq a))
                requires arr |-> s ** pure (A.length arr == SZ.v len) 
                ensures exists* s'. 
                    arr |-> s' **
                    pure (sorted #_ #ord s' /\ permutation s s'))
    }

A few things to note about this specification:

* We use a ``class`` (see :ref:`this section on typeclasses
  <Part3_typeclasses>`) to indicate that we expect to provide multiple instances
  of this signature, one for each sorting algorithm. This is a nice way to group
  together the specifications of all sorting algorithms, and to indicate that
  they should all have the same specification.

* Unlike the types shown previously, this type is *polymorphic* in:

  - The type of elements ``a``

  - And, a total order ``Pulse.Lib.TotalOrder.total_order a``, a pure function
    to compare elements of type ``a`` from the library.

  - The postcondition states that the contents of the array at the end (``s'``)
    is a sorted permutation of the original contents (``s``).

Writing this specification once and having the agents prove that all the sorting
algorithms satisfy this specification makes for a much better rubric. It's also
just good software engineering practice (better, as usual, for common
abstractions to be factored and reused) and it remains good practice for agentic
proof engineering.

But, let's keep going, we can do more with polymorphic specifications.

----------------------------------
Ghost State for Complexity Proofs
----------------------------------

A large part of the CLRS textbook is devoted to the worst-case complexity
analysis of algorithms. Accordingly, the AutoCLRS development also includes such
complexity analysis for many (though not all) of the algorithms. The complexity
analysis is done in a very similar way to the functional correctness proofs,
with the general idea being to

1. Instrument the implementation with a **ghost counter**, incrementing the
   counter for each operation that contributes to the complexity measure (e.g.,
   comparisons, swaps, etc.)

2. Enriching invariants to track bounds on these ghost counters.

3. Proving that the ghost counter is bounded by a function of the input size
   (e.g., ``n log n`` for heapsort).

Note, the proofs do not include any reasoning about asymptotic complexity, e.g.,
the proofs do not say that heapsort is O(n log n), but rather that the ghost
counter is bounded by a specific function of the input size.

Let's look at the complexity enriched version of the ``insertion_sort``:


.. code-block:: pulse

    module GR = Pulse.Lib.GhostReference

    let complexity_bounded (cf c0: nat) (n: nat) : prop =
        cf >= c0 /\
        cf - c0 <= n * (n - 1) / 2

    fn insertion_sort
        (a: array int)
        (#s0: Ghost.erased (Seq.seq int))
        (len: SZ.t)
        (ctr: GR.ref nat)
        (#c0: erased nat)
    requires a |-> s0 ** ctr |-> c0
    requires pure (SZ.v len == Seq.length s0 /\ Seq.length s0 <= A.length a)
    ensures exists* s (cf: nat). 
        a |-> s ** ctr |-> cf **
        pure (Seq.length s == Seq.length s0 /\
              sorted s /\
              permutation s0 s /\
              complexity_bounded cf c0 (SZ.v len))

This type is very similar to the previous type of ``insertion_sort``. The new elements are:

1. The function has an additional parameter, ``ctr : GR.ref nat``, a ghost
   reference to a natural number---we learned about ghost references in
   :ref:`this section <Pulse_Ghost>`. The ghost reference is used to count the
   number of operations we are interested in for the complexity analysis.

2. The precondition includes ownership of the ghost reference, ``ctr |-> c0``,
   where ``c0`` is the initial value of the counter.

3. The postcondition includes the usual functional correctness properties, i.e.,
   that the output is a sorted precondition of the input.

4. And, importantly, the last clause states that the counter has been "ticked"
   ``(cf - c0)`` at most ``n * (n - 1) / 2`` times.

Now, with type shown as the rubric, let's look at what one would have to review
to judge that this is a proper worst-case complexity proof:

* Inspect the implementation of ``insertion_sort`` to check that every
  comparison is accounted for with an increment of the ghost counter.

* The ghost counter is never decremented.

This is sub-optimal since now one must, as part of the review, read the code in
detail, figure out if it is instrumented correctly. The promise of
proof-oriented programming is that one should be able to check the correctness
of a program by reading the specification alone, but in this case, one also has
to read the implementation.

Again, we should do better, and we can do better by embracing principles from
proof engineering to set a better rubric.

-------------------------------
Better Rubrics with Abstraction
-------------------------------

Consider the following typeclass as a rubric for complexity-aware sorting
algorithms---it's a lot to swallow in one go, so we'll describe it slowly piece
by piece.

.. code-block:: pulse

    module MR = Pulse.Lib.MonotonicGhostRef
    module TO = Pulse.Lib.TotalOrder

    let leq_nat (x y:nat) : prop = x <= y

    let ticks_t = MR.mref leq_nat

    let instrumented_total_order (#a:Type) (ord:TO.total_order a) (ctr:ticks_t) =
        fn (x y:a) (#i:erased nat)
        requires MR.pts_to ctr #1.0R i
        returns o:order
        ensures MR.pts_to ctr #1.0R (i + 1)
        ensures pure (o == x `ord.TO.compare` y)

    class array_sort (f: nat -> nat) = {
        sort:
            (fn (a:Type)
                (arr:A.array a)
                (len:SZ.t) 
                (ctr:ticks_t)
                (#ord:erased (TO.total_order a))
                (iord:instrumented_total_order ord ctr)
                (#s:erased (Seq.seq a)) (#i:erased nat)
            requires arr |-> s ** MR.pts_to ctr #1.0R i
            requires pure (A.length arr == SZ.v len)
            ensures exists* s' ticks. 
                arr |-> s' **
                MR.pts_to ctr #1.0R ticks **
                pure (sorted #_ #ord s' /\ permutation s s' /\ ticks <= i + f (Seq.length s)))
    }

Monotonic Ghost State
.....................

A counter for complexity tracking should only be advanced, never decremented. An
ordinary ghost reference (``Pulse.Lib.GhostReference.ref``) allows one to read
and write the reference, but it does not enforce monotonicity. This means that
one needs to carefully read the implementation to ensure that the counter is
only ever incremented. 

Pulse offers more sophisticated forms of ghost state, including something called
*monotonic*  ghost state. Given a reflexive, transitive relation ``rel: preorder
a``, one can build a monotonic ghost reference
(``Pulse.Lib.MonotonicGhostRef.mref rel``) which is a reference to a mutable
cell of type ``a`` which can only be updated in a way that respects the relation
``rel``.

In our rubric above, ``ticks_t`` is a monotonic ghost reference where the
relation is the natural order on natural numbers. This means that a
``ctr:ticks_t`` can only be advanced, never decremented. This is exactly what we
want for a complexity counter: using ``ticks_t`` for the counter means that one
does not have to read the implementation to check that the counter is only ever
incremented, since the type system enforces this property.

Instrumenting Comparisons with Ticks
....................................

Our next step in defining our rubric is to ensure that every comparison is
instrumented with a tick of the counter. To do this, we define the type of an
instrumented total order, a Pulse function that takes two elements of type ``a``
and returns an ``order`` (i.e., a comparison result) with a postcondition
proving that its result is equal to the result given by a *pure* total order
``ord``, but also stating that tick counter has been incremented. (The ``#1.0R``
is to state that we have full permission to the counter and can increment it.)

.. code-block:: pulse

    let instrumented_total_order (#a:Type) (ord:TO.total_order a) (ctr:ticks_t) =
        fn (x y:a) (#i:erased nat)
        requires MR.pts_to ctr #1.0R i
        returns o:order
        ensures MR.pts_to ctr #1.0R (i + 1)
        ensures pure (o == x `ord.TO.compare` y)

Tying it Together with Parametricity
....................................

The final piece of the rubric is to tie together the tick counter with the
instrumented total order, while exploiting parametricity to ensure that the
sorting algorithm respects the instrumentation. Let's have a closer look:

.. code-block:: pulse

    class array_sort (bound: nat -> nat) = {
        sort:
            (fn (a:Type)
                (arr:A.array a)
                (len:SZ.t) 
                (ctr:ticks_t)
                (#ord:erased (TO.total_order a))
                (iord:instrumented_total_order ord ctr)
                (#s:erased (Seq.seq a)) (#i:erased nat)
            requires arr |-> s ** MR.pts_to ctr #1.0R i
            requires pure (A.length arr == SZ.v len)
            ensures exists* s' ticks. 
                arr |-> s' **
                MR.pts_to ctr #1.0R ticks **
                pure (sorted #_ #ord s' /\ permutation s s' /\ ticks <= i + bound (Seq.length s)))
    }

The ``sort`` function is

* Polymorphic in the type of array elements ``a:Type``

* Unlike our previous version, this version of ``sort`` is parametric in a total
  order ``ord`` on the elements,  but this ``ord`` has an ``erased`` type,
  meaning that runtime behavior of ``sort`` cannot depend on ``ord``. 

* Instead of using ``ord``, the function is also parameterized by a tick counter
  ``ctr:ticks_t`` and an instrumented total order
  ``iord:instrumented_total_order ord ctr``. This means, from parametricity,
  that the sorting algorithm is forced to use the instrumented total order for
  comparisons---no other concrete operations on the type ``a`` is available, and
  so every comparison must tick the counter.

* The rest of the rubric is similar to what we had before:

  - we have ownership of the array ``arr`` and the ghost counter ``ctr`` in the
    precondition.

  - The precondition states that the array has length ``len``.
  
  - The postcondition states that the output is a sorted permutation of the
    input, as usual for functional correctness,
    
  - And, importantly, that the final value of the counter ``ticks`` is advanced
    by at most a ``bound`` computed from the length of the input.


Using the Rubric
................

With this rubric in place, one can ask an agent to implement insertion sort,
merge sort, heapsort, and quicksort, and here's what it produces (using GPT-5.5
in GitHub Copilot CLI with the FStarLang/proof-copilot plugin):


.. code-block:: fstar

    instance insertion_sort_array_sort
    : array_sort (fun n -> n * (n - 1) / 2)

    instance merge_sort_array_sort 
    : array_sort (fun n -> if n > 0 then 4 * n * MS.log2_ceil n + 4 * n else 0)

    instance heapsort_array_sort 
    : array_sort (fun n ->
        if n > 0 then
          (n / 2) * (2 * HC.log2_floor n) +
          (n - 1) * (2 * HC.log2_floor n)
        else 0)

    instance quicksort_array_sort 
    : array_sort (fun n -> n * (n - 1) / 2)

This is all that one has to audit to convince oneself that we have algorithms
that are functionally correct with the appropriate complexity bounds, a
substantial improvement than before.

The main point here is that by careful design of a rubric, applying principles
from software and proof-engineering practice, one can reduce the amount of human
effort needed to comprehend the results produced by an agentic proof-oriented
programmer.

Note, there is still room for improvement, e.g., for merge sort and heap sort,
the agent could have simplified away the special handling of the case when ``n =
0``---one could ask the agent to do that, but this is what was produced by the
agent, so we show it as is.

Also, importantly, rubrics are not absolute, as we will soon see. For starters,
this rubric does not cover space complexity at all. What would it take to track
and bound space complexity? We will get to this in a subsequent chapter.

-----------------------------------------------
Auditing Implementations: What is an Algorithm?
-----------------------------------------------

Simply knowing that say, ``insertion_sort_array_sort`` has the type of a
correct, quadratic-time sorting algorithm doesn't tell us that what is
implemented is actually an insertion sort. Notice that ``quicksort_array_sort``
has exactly the same type, so the rubric alone does not have the power to
distinguish the two. For this, we need to audit the implementation itself.

Auditing a piece of code for fidelity to a particular algorithm is a thorny
problem. In fact, even the notion of an algorithm itself is a deep conceptual
question, let alone whether or not a given implementation is faithful to a
particular algorithm. Indeed, in our experience, agents are prone to cheating in
this regard, e.g., producing an implementation of insertion sort and claiming
that it is quicksort. For this, we offer nothing more than a plain old code
review.

You can find the full implementations here:

* `Insertion sort <https://github.com/FStarLang/AlgoStar/blob/rubrics/autoclrs/ch02-getting-started/CLRS.Ch02.InsertionSort.Rubric.fst>`__

* `Merge sort <https://github.com/FStarLang/AlgoStar/blob/rubrics/autoclrs/ch02-getting-started/CLRS.Ch02.MergeSort.Rubric.fst>`__

* `Heap sort <https://github.com/FStarLang/AlgoStar/blob/rubrics/autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Rubric.fst>`__

* `Quicksort <https://github.com/FStarLang/AlgoStar/blob/rubrics/autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Rubric.fst>`__

And the rubric itself:

* `CLRS.Common.Complexity.Sorting.Class <https://github.com/FStarLang/AlgoStar/blob/rubrics/autoclrs/common/CLRS.Common.Complexity.Sorting.Class.fst>`__