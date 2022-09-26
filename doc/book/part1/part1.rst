.. _Part1:

############################################
Programming and Proving with Total Functions
############################################


The core design philosophy of F* is that the type of a term (a program
fragment) is a specification of its runtime behavior. We write ``e :
t`` to mean that a term ``e`` has type ``t``. Many terms can have the
same type and the same term can have many types.

One (naive but useful) mental model is to think of a type as
describing a set of values. For instance, the type ``int`` describes
the set of terms which compute integer results, i.e., when you have
``e : int``, then when ``e`` is reduced fully it produces a value in
the set ``{..., -2, -1, 0, 1, 2, ...}``. Similarly, the type ``bool``
is the type of terms that compute or evaluate to one of the values in
the set ``{true,false}``. Unlike many other languages, F* allows
defining types that describe arbitrary sets of values, e.g., the type
that contains only the number ``17``, or the type of functions that
factor a number into its primes.

When proving a program ``e`` correct, one starts by specifying the
properties one is interested in as a type ``t`` and then trying to
convince F* that ``e`` has type ``t``, i.e., deriving ``e : t``.

The idea of using a type to specify properties of a program has deep
roots in the connections between logic and computation. You may find
it interesting to read about `propositions as types
<https://cacm.acm.org/magazines/2015/12/194626-propositions-as-types/fulltext>`_,
a concept with many deep mathematical and philosophical
implications. For now, it suffices to think of a type ``t`` as a
specification, or a statement of a theorem, and ``e : t`` as
computer-checkable claim that the term ``e`` is a proof of the theorem
``t``.

In the next few chapters we'll learn about how to program total
functions and prove them correct.

.. toctree::
   :maxdepth: 1
   :caption: Contents:

   part1_getting_off_the_ground
   part1_polymorphism
   part1_equality
   part1_prop_assertions
   part1_inductives
   part1_termination
   part1_lemmas
   part1_quicksort
   part1_execution   
   part1_wrap
