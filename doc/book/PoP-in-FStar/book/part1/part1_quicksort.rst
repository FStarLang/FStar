.. _Part1_quicksort:

Case Study: Quicksort
=====================

We'll now put together what we've learned about defining recursive
functions and proving lemmas about them to prove the correctness of
`Quicksort <https://en.wikipedia.org/wiki/Quicksort>`_, a classic
sorting algorithm.

We'll start with lists of integers and describe some properties that
we'd like to hold true of a sorting algorithm, starting with a
function ``sorted``, which decides when a list of integers is sorted
in increasing order, and ``mem``, which decides if a given element is
in a list. Notice that ``mem`` uses an ``eqtype``, :ref:`the type of
types that support decidable equality <Part1_equality>`.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sorted mem
       :end-before: SNIPPET_END: sorted mem

Given a sorting algorithm ``sort``, we would like to prove the
following property, meaning that for all input list ``l``, the
resulting list ``sort l`` is sorted and has all the elements that
``l`` does.

.. code-block:: fstar

    forall l. sorted (sort l) /\ (forall i. mem i l <==> mem i (sort l))

This specification is intentionally a bit weak, e.g., in case there
are multiple identical elements in ``l``, this specification does not
prevent ``sort`` from retaining only one of them.

We will see how to improve this specification below, as part of an
exercise.

If you're unfamiliar with the algorithm, you can `read more about it
here <https://en.wikipedia.org/wiki/Quicksort>`_. We'll describe
several slightly different implementations and proofs of Quicksort in
detail—you may find it useful to follow along interactively with the
`entire code development <../code/Part1.Quicksort.fst>`_ of this
sequence.

Implementing ``sort``
^^^^^^^^^^^^^^^^^^^^^

Our implementation of Quicksort is pretty simple-minded. It always
picks the first element of the list as the pivot; partitions the rest
of the list into those elements greater than or equal to the pivot,
and the rest; recursively sorts the partitions; and slots the pivot in
the middle before returning. Here it is:

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sort-impl
       :end-before: SNIPPET_END: sort-impl

There are a few points worth discussing in detail:

1. The notation ``((<=) pivot)`` may require some explanation: it is
   the *partial application* of the ``<=`` operator to just one
   argument, ``pivot``. It is equivalent to ``fun x -> pivot <= x``.

2. We have to prove that ``sort`` terminates. The measure we've
   provided is ``length l``, meaning that at each recursive call,
   we're claiming that the length of input list is strictly
   decreasing.

3. Why is this true? Well, informally, the recursive calls ``sort lo``
   and ``sort hi`` are partitions of the ``tl`` of the list, which is
   strictly shorter than ``l``, since we've removed the ``pivot``
   element. We'll have to convince F* of this fact by giving
   ``partition`` an interesting type that we'll see below.

Implementing ``partition``
^^^^^^^^^^^^^^^^^^^^^^^^^^

Here's an implementation of ``partition``. It's a :ref:`higher-order
function <Part1_higher_order_functions>`, where ``partition f l``
returns a pair of lists ``l₁`` and ``l₂``, a partitioning of the
elements in ``l`` such that the every element in ``l₁`` satisfies
``f`` and the elements in ``l₂`` do not.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: partition
       :end-before: SNIPPET_END: partition

The specification we've given ``partition`` is only partial—we do not
say, for instance, that all the elements in ``l₁`` satisfy ``f``. We
only say that the sum of the lengths of the ``l₁`` and ``l₂`` are
equal to the length of ``l``. That's because that's the only property
we need (so far) about ``partition``—this property about the lengths
is what we need to prove that on the recursive calls ``sort lo`` and
``sort hi``, the arguments ``lo`` and ``hi`` are strictly shorter than
the input list.

This style of partial specification should give you a sense of the art
of program proof and the design choices between :ref:`intrinsic and
extrinsic proof <Part1_intrinsic_extrinsic>`. One tends to specify
only what one needs, rather than specifying all properties one can
imagine right up front.

Proving ``sort`` correct
^^^^^^^^^^^^^^^^^^^^^^^^

Now that we have our definition of ``sort``, we still have to prove it
correct. Here's a proof—it requires three auxiliary lemmas and we'll
discuss it in detail.

Our first lemma relates ``partition`` to ``mem``: it proves what we
left out in the intrinsic specification of ``partition``, i.e., that
all the elements in ``l₁`` satisfy ``f``, the elements in ``l₂`` do
not, and every element in ``l`` appears in either ``l₁`` or ``l₂``.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: partition_mem
       :end-before: SNIPPET_END: partition_mem

Our next lemma is very specific to Quicksort. If ``l₁`` and ``l₂`` are
already sorted, and partitioned by ``pivot``, then slotting ``pivot``
in the middle of ``l₁`` and ``l₂`` produces a sorted list. The
specification of ``sorted_concat`` uses a mixture of refinement types
(e.g., ``l1:list int{sorted l1}``) and ``requires`` / ``ensures``
specifications–this is just a matter of taste.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sorted_concat
       :end-before: SNIPPET_END: sorted_concat

Our third lemma is a simple property about ``append`` and ``mem``.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: append_mem
       :end-before: SNIPPET_END: append_mem

Finally, we can put the pieces together for our top-level statement
about the correctness of ``sort``.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sort_correct
       :end-before: SNIPPET_END: sort_correct

The structure of the lemma is mirrors the structure of ``sort``
itself.

* In the base case, the proof is automatic.

* In the inductive case, we partition the tail of the list and
  recursively call the lemma on the the ``hi`` and ``lo`` components,
  just like ``sort`` itself. The intrinsic type of ``partition`` is
  also helpful here, using the ``length`` measure on the list to prove
  that the induction here is well-founded.

  - To prove the ``ensures`` postcondition, we apply our three
    auxiliary lemmas.

    + ``partition_mem ((<=) pivot) tl`` gives us the precondition of
      needed to satisfy the ``requires`` clause of
      ``sorted_concat``.

    + We also need to prove the ``sorted`` refinements on ``sort lo``
      and ``sort hi`` in order to call ``sorted_concat``, but the
      recursive calls of the lemma give us those properties.

    + After calling ``sorted_concat``, we have proven that the
      resulting list is sorted. What's left is to prove that all the
      elements of the input list are in the result, and ``append_mem``
      does that, using the postcondition of ``partition_mem`` and the
      induction hypothesis to relate the elements of ``append (sort
      lo) (pivot :: sort hi)`` to the input list ``l``.

Here's another version of the ``sort_correct`` lemma, this time
annotated with lots of intermediate assertions.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sort_correct_annotated
       :end-before: SNIPPET_END: sort_correct_annotated

This is an extreme example, annotating with assertions at almost every
step of the proof. However, it is indicative of a style that one often
uses to interact with F* when doing SMT-assisted proofs. At each point
in your program or proof, you can use ``assert`` to check what the
prover "knows" at that point. See what happens if you move the
assertions around, e.g., if you move ``assert (sort_ok lo)`` before
calling ``sort_correct_annotated lo``, F* will complain that it is not
provable.

Limitations of SMT-based proofs at higher order
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

You may be wondering why we used ``(<=) pivot`` instead of ``fun x ->
pivot <= x`` in our code. Arguably, the latter is more readable,
particularly to those not already familiar with functional programming
languages. Well, the answer is quite technical.

We could indeed have written ``sort`` like this,

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sort_alt
       :end-before: SNIPPET_END: sort_alt

And we could have tried to write our main lemma this way:

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sort_alt_correct
       :end-before: SNIPPET_END: sort_alt_correct

However, without further assistance, F*+SMT is unable to prove the
line at which the ``assume`` appears. It turns out, this is due to a
fundamental limitation in how F* encodes its higher-order logic into
the SMT solver's first-order logic. This encoding comes with some loss
in precision, particularly for lambda terms. In this case, the SMT
solver is unable to prove that the occurrence of ``fun x -> pivot <=
x`` that appears in the proof of ``sort_alt_correct_annotated`` is
identical to the occurrence of the same lambda term in ``sort_alt``,
and so it cannot conclude that ``sort_alt l`` is really equal to
``append (sort_alt lo) (pivot :: sort_alt hi))``.

This is unfortunate and can lead to some nasty surprises when trying
to do proofs about higher order terms. Here are some ways to avoid
such pitfalls:

* Try to use named functions at higher order, rather than lambda
  literals. Named functions do not suffer a loss in precision when
  encoded to SMT. This is the reason why ``(<=) pivot`` worked out
  better than the lambda term here—the ``(<=)`` is a name that
  syntactically appears in both the definition of ``sort`` and the
  proof of ``sort_alt_correct`` and the SMT solver can easily see that
  the two occurrences are identical.

* If you must use lambda terms, sometimes an intrinsic proof style can
  help, as we'll see below.

* If you must use lambda terms with extrinsic proofs, you can still
  complete your proof, but you will have to help F* along with tactics
  or proofs by normalization, more advanced topics that we'll cover in
  later sections.

* Even more forward looking, recent `higher-order variants of SMT
  solvers <https://matryoshka-project.github.io/>`_ are promising and
  may help address some of these limitations.

An intrinsic proof of ``sort``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As we observed earlier, our proof of ``sort_correct`` had essentially
the same structure as the definition of ``sort`` itself—it's tempting
to fuse the definition of ``sort`` with ``sort_correct``, so that we
avoid the duplication and get a proof of correctness of ``sort``
built-in to its definition.

So, here it is, a more compact proof of ``sort``, this time done
intrinsically, i.e., by enriching the type of ``sort`` to capture the
properties we want.

.. literalinclude:: ../code/Part1.Quicksort.fst
       :language: fstar
       :start-after: SNIPPET_START: sort_intrinsic
       :end-before: SNIPPET_END: sort_intrinsic

We still use the same three auxiliary lemmas to prove the properties
we want, but this time the recursive calls to sort the partitioned
sub-lists also serve as calls to the induction hypothesis for the
correctness property we're after.

Notice also that in this style, the use of a lambda literal isn't
problematic—when operating within the same scope, F*'s encoding to SMT
is sufficiently smart to treat the multiple occurrences of ``fun x ->
pivot <= x`` as identical functions.

Runtime cost?
.............

You may be concerned that we have just polluted the definition of
``sort_intrinsic`` with calls to three additional recursive
functions–will this introduce any runtime overhead when executing
``sort_intrinsic``? Thankfully, the answer to that is "no".

As we'll learn in the section on :ref:`effects <effects>`, F* supports
of notion of *erasure*—terms that can be proven to not contribute to
the observable behavior of a computation will be erased by the
compiler before execution. In this case, the three lemma invocations
are total functions returning unit, i.e., these are functions that
always return in a finite amount of time with the constant value
``()``, with no other observable side effect. So, there is no point in
keeping those function calls around—we may as well just optimize them
away to their result ``()``.

Indeed, if you ask F* to extract the program to OCaml (using
``fstar --codegen OCaml``), here's what you get:

.. code-block:: fstar

  let rec (sort_intrinsic : Prims.int Prims.list -> Prims.int Prims.list) =
    fun l ->
      match l with
      | [] -> []
      | pivot::tl ->
         let uu___ = partition (fun x -> pivot <= x) tl in
         (match uu___ with
          | (hi, lo) ->
            append (sort_intrinsic lo) (pivot :: (sort_intrinsic hi)))

The calls to the lemmas have disappeared.

Exercises
^^^^^^^^^

Generic sorting
...............

Here's `a file with the scaffolding for this exercise
<../code/exercises/Part1.Quicksort.Generic.fst>`_.

The point of this exercise is to define a generic version of ``sort``
that is parameterized by any total order over the list elements,
rather than specializing ``sort`` to work on integer lists only. Of
course, we want to prove our implementations correct. So, let's do it
in two ways, both intrinsically and extrinsically. Your goal is to
remove the all the occurrences of ``admit`` in the development below.

.. literalinclude:: ../code/exercises/Part1.Quicksort.Generic.fst
       :language: fstar

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Quicksort.Generic.fst
       :language: fstar


Proving that ``sort`` is a permutation
......................................

We promised at the beginning of this section that we'd eventually give
a better specification for ``sort``, one that proves that it doesn't
drop duplicate elements in the list. That's the goal of the exercise
in this section—we'll prove that our generic Quicksort is returns a
permutation of the input list.

Let's start by defining what it means for lists to be permutations of
each other—we'll do this using occurrence counts.

.. literalinclude:: ../code/exercises/Part1.Quicksort.Permutation.fst
       :language: fstar
       :start-after: //SNIPPET_START: count permutation
       :end-before: //SNIPPET_END: count permutation

The definitions should be self-explanatory. We include one key lemma
``append_count`` to relate occurrence to list concatenations.

The next key lemma to prove is ``partition_mem_permutation``.

.. code-block:: fstar

  val partition_mem_permutation (#a:eqtype)
                                (f:(a -> bool))
                                (l:list a)
    : Lemma (let l1, l2 = partition f l in
             (forall x. mem x l1 ==> f x) /\
             (forall x. mem x l2 ==> not (f x)) /\
             (is_permutation l (append l1 l2)))

You will also need a lemma similar to the following:

.. code-block:: fstar

  val permutation_app_lemma (#a:eqtype) (hd:a) (tl l1 l2:list a)
    : Lemma (requires (is_permutation tl (append l1 l2)))
            (ensures (is_permutation (hd::tl) (append l1 (hd::l2))))

Using these, and adaptations of our previous lemmas, prove:

.. code-block:: fstar

   val sort_correct (#a:eqtype) (f:total_order_t a) (l:list a)
     : Lemma (ensures
               sorted f (sort f l) /\
               is_permutation l (sort f l))

Load the `exercise script
<../code/exercises/Part1.Quicksort.Permutation.fst>`_ and give it a
try.


.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Quicksort.Permutation.fst
       :language: fstar




