.. _Part2:

################################################################
Representing Data, Proofs, and Computations with Inductive Types
################################################################


..
   In this second part of the book, we'll dive deeper into F*, focusing
   on *inductive definitions*, the main mechanism in F* for the user to
   define new types.

Earlier, we learned about :ref:`defining new data types <Part1_ch3>`
in F*. For example, here's the type of lists parameterized by a type
``a`` of the list elements.

.. code-block:: fstar

   type list a =
     | Nil  : list a
     | Cons : hd:a -> tl:list a -> list a

We also saw that it was easy to define basic functions over these
types, using pattern matching and recursion. For example, here's
a function to compute the length of a list.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: length
   :end-before: //SNIPPET_END: length

The function ``length`` defines some property of a ``list`` (its
length) separately from the definition of the ``list`` type itself.
Sometimes, however, it can be convenient to define a property of a
type together with the type itself. For example, in some situations,
it may be natural to define the length of the list together with the
definition of the list type itself, so that every list is structurally
equipped with a notion of its length. Here's how:

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: SNIPPET_START: vec
   :end-before: SNIPPET_END: vec

What we have here is our first indexed type, ``vec a n``. One way to
understand this definition is that ``vec a : nat -> Type`` describes a
family of types, ``vec a 0``, ``vec a 1``, ... etc., all representing
lists of ``a``-typed elements, but where the *index* ``n`` describes
the length of the list. With this definition of ``vec``, the function
``length`` is redundant: given a ``v : vec a n`` we know that its
``length v`` is ``n``, without having to recompute it.

This style of enriching a type definition with indexes to state
properties of the type is reminiscent of what we learned earlier about
:ref:`intrinsic versus extrinsic proofs
<Part1_intrinsic_extrinsic>`. Rather than defining a single type
``list a`` for all lists and then separatately (i.e., extrinsically)
defining a function ``length`` to compute the length of a list, with
``vec`` we've enriched the type of the list intrinsically, so that
type of ``vec`` immediately tells you its length.

Now, you may have seen examples like this length-indexed ``vec`` type
before---it comes up often in tutorials about dependently typed
programming. But, indexed types can do a lot more. In this section we
learn about indexed inductive types from three related perspectives:

  * Representing data: Inductive types allow us to build new data
    types, includes lists, vectors, trees, etc. in several flavors.
    We present two case studies: :ref:`vectors <Part2_vectors>` and
    :ref:`Merkle trees <Part2_merkle>`, a binary tree data structure
    equipped with cryptographic proofs.

  * Representing proofs: The core logic of F* rests upon several
    simple inductive type definitions. We revisit the logical
    connectives we've seen before (including the :ref:`propositional
    connectives <Part2_connectives>` and :ref:`equality
    <Part2_equality>`) and show how rather than being primitive
    notions in F*, their definitions arise from a few core
    constructions involving inductive type. Other core notions in the
    language, including the handling of :ref:`termination proofs
    <Part1_termination>`, can also be understood in terms of inductive
    types that :ref:`model well-founded recursion
    <Part2_well_founded_recursion>`.

  * Representing computations: Inductive type definitions allow
    embedding other programming languages or computational models
    within F*. We develop two case studies.

    + We develop a :ref:`deep embedding of the simply-typed lambda
      calculus <Part2_stlc>` with several reduction strategies, and a
      proof of its syntactic type soundness. The example showcases the
      use of several inductive types to represent the syntax of a
      programming language, a relation describing its type system, and
      another relation describing its operational semantics.

    + We also show how to use :ref:`higher-order abstract syntax
      <Part2_phoas>` to represent well-typed lambda terms, a concise
      style that illustrates how to use inductive types that store
      functions.

    + Finally, we look at a :ref:`shallow embedding of an imperative
      programming language with structured concurrency <Part2_par>`,
      representing computations as infinitely branching inductively
      defined trees. The example introduces modeling computational
      effects as monads and showcases the use of inductive types
      at higher order.

This section is somewhat more advanced than the first. It also
interleaves some technical material about F*'s core logic with case
studies showing some of those core concepts at work. You can certainly
work through the material sequentially, but depending on your
interests, you may find the following paths through the material to be
more accessible.

If you're familiar with dependent types but are new to F* and want a
quick tour, the following path might work for you:

  * :ref:`Length-indexed lists <Part2_vectors>`, F*-specific notations

  * :ref:`Equality <Part2_equality>`

  * :ref:`Logical connectives <Part2_connectives>`

  * Any of the case studies, depending on your interest.

If you're unfamiliar with dependent types and are more curious to
learn how to use F* by working through examples, following path might
work for you:

  * :ref:`Inductive type definitions <Part2_inductives>`, basic concepts

  * :ref:`Length-indexed lists <Part2_vectors>`, F*-specific notations in the simplest setting

  * :ref:`Merkle trees <Part2_merkle>`, a more interesting example, with applications to cryptographic security

  * :ref:`Logical connectives <Part2_connectives>`, some utilities to manipulate F*'s logical connectives

  * Any of the case studies, depending on your interest, with the :ref:`Simply Typed Lambda Calculus <Part2_stlc>` perhaps the easiest of them.

But, by the end of this section, through several exercises, we expect
the reader to be familiar enough with inductive types to define their
own data structures and inductively defined relations, while also
gaining a working knowledge of some core parts of F*'s type theory.


.. toctree::
   :maxdepth: 1
   :caption: Contents:

   part2_inductive_type_families
   part2_vectors
   part2_merkle
   part2_equality
   part2_logical_connectives
   part2_stlc
   part2_phoas
   part2_well_founded
   part2_par
   part2_universes

..
  Vectors for basics
    - But vectors are too simple, we can do them with just refined lists

  Merkle trees to capture more interesting invariants of a type

  Higher-order inductive types: infinitely branching trees
    - Free monads and computation trees

  Representing proof terms: Simply-typed lambda calculus

  Representing proof terms: Accessibility predicates and termination proofs
