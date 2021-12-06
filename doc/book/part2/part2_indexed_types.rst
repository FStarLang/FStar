.. _Part2_indexed_types:

Inductive type families
=======================


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

What we've done here is to define some property of a ``list`` (its
length) independently of the definition of the ``list`` type itself.
However, sometimes it can be convenient to define a property of a type
together with the type itself. For example, in some situations, it may
be natural to define the length of the list together with the
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
programming. But, indexed types can do a lot more than just capture
properties like lengths of vectors. In this section, we'll work out
the vector example in detail, and then look at three more examples,
each of which use indexed types in various interesting ways to state
and prove invariants about data structures.

We start, however, by describing the general form of inductive type
definitions, for which we'll need a bit of mathematical notation.

..
   * Inductive type definitions: Their general form

   * Examples

     - Length-indexed vectors
     - Red-black trees
     - Merkle trees
     - Interleaved sequences

Parameters, indexes, and positivity
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An inductive type definition, sometimes called a *datatype*, has the
following general structure.

.. math::

   \mathsf{type}~T₁~\overline{(x₁:p₁)} : \overline{y₁:q₁} → \mathsf{Type} = \overline{| D₁ : t₁} \\
   \mathsf{and}~Tₙ~\overline{(xₙ:pₙ)} : \overline{yₙ:qₙ} → \mathsf{Type} =  \overline{| Dₙ : tₙ} \\

This defines :math:`n` mutually inductive types, named :math:`T₁ …
Tₙ`, called the *type constructors*. Each type constructor :math:`Tᵢ`
has a number of *parameters*, the :math:`\overline{xᵢ : pᵢ}`, and a
number of *indexes*, the :math:`\overline{yᵢ:qᵢ}`.

Each type constructor :math:`Tᵢ` has zero or more *data constructors*
:math:`\overline{Dᵢ:tᵢ}`. For each data constructor :math:`Dᵢⱼ`, its
type :math:`tᵢⱼ` must be of the form :math:`\overline{z:s} →
Tᵢ~\bar{xᵢ}~\bar{e}`, i.e., it must be a function type returning an
instance of :math:`Tᵢ` with *the same parameters*
:math:`\overline{xᵢ}` as in the type constructor's signature, but with
any other well-typed terms :math:`\overline{e}` for the index
arguments. This is the main difference between a parameter and an
index—a parameter of a type constructor *cannot* vary in the result
type of the data constructors, while the indexes can.

Further, in each of the arguments :math:`\overline{z:s}` of the data
constructor, none of the mutually defined type constructors
:math:`\overline{T}` may appear to the left of an arrow. That is, all
occurrences of the type constructors must be *strictly positive*. This
is to ensure that the inductive definitions are well-founded. As we
will see shortly, without this restriction, it is easy to break
soundness by writing non-terminating functions with ``Tot`` types.

Also related to ensuring logical consistency is the *universe* level
of an inductive type definition. We'll return to that later, once
we've done a few examples.

Length-indexed vectors
^^^^^^^^^^^^^^^^^^^^^^

Let's look again at the definition of the ``vec`` type, trying to make
concretesome aspects of the formal definition above.

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: vec
   :end-before: //SNIPPET_END: vec

Here, we're defining just a single type constructor called ``vec``
(i.e, just :math:`T_1`), which a single parameter ``(a:Type)`` and one
index ``nat``.

``vec`` has to data constructors: ``Nil`` builds an instance of ``vec
a 0``, the empty vector; and ``Cons hd tl`` builds an instance of
``vec a (n + 1)`` from a head element ``hd:a`` and a tail ``tl : vec a
n``. That is, the two constructors build different instances of
``vec``---those instances have the same parameter (``a``), but
different indexes (``0`` and ``n + 1``).

.. note::

   Datatypes in many languages in the ML family, including OCaml and
   F#, have parameters but no indexes. So, all the data construtors
   construct the same instance of the type constructor. Further, all
   data constructors take at most one argument. If your datatype
   happens to be simple enough to fit these restrictions, you can use
   a notation similar to OCaml or F* for those types in F*. For
   example, here's the ``option`` type defined in F* using an
   OCaml-like notation.

   .. code-block:: fstar

      type option a =
        | None
        | Some of a

   This is equivalent to

   .. code-block:: fstar

      type option a =
        | None : option a
        | Some : a -> option a

Getting an element from a vector
................................

With our length-indexed ``vec`` type, one can write functions with
types that make use of the length information to ensure that they are
well-defined. For example, to get the ``i`` th element of a vector, one
can write:

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: long_get
   :end-before: //SNIPPET_END: long_get

The type of ``get i v`` says that ``i`` must be less than ``n``, where
``n`` is the length of ``v``, i.e., that ``i`` is within bounds of the
vector, which is enough to prove that ``get i v`` can always return an
element of type ``a``. Let's look a bit more closely at how this
function is typechecked by F*.

The first key bit is pattern matching ``v``:

.. code-block:: fstar

   match v with
   | Nil -> false_elim()
   | Cons hd tl ->

In case ``v`` is ``Nil``, we use the library function
``Prims.false_elim : squash False -> a`` to express that this case is
impossible. Intuitively, since the index ``i`` is a natural number
strictly less than the length of the list, we should be able to
convince F* that ``n <> 0``.

The way this works is that F* typechecks the branch in a context that
includes an *equation*, namely that the ``v : vec a n`` equals the
pattern ``Nil : vec a 0``. With the assumption that ``v == Nil`` in
the context, F* tries to check that ``false_elim`` is well-typed,
which in turn requires ``() : squash False``. This produces an proof
obligation sent to the SMT solver, which is able to prove ``False`` in
this case, since from ``v = Nil`` we must have that ``n = 0`` which
contradicts ``i < n``. Put another way, the branch where ``v = Nil``
is unreachable given the precondition ``i < n``.

.. note::

   When a branch is unreachable, F* allows you to just omit the branch
   altogether, rather than writing it an explicitly calling
   ``false_elim``. For example, it is more common to write:

   .. literalinclude:: ../code/Vec.fst
      :language: fstar
      :start-after: //SNIPPET_START: get
      :end-before: //SNIPPET_END: get

   where ``let Cons hd tl = v`` pattern matches ``v`` against just
   ``Cons hd tl``. F* automatically proves that the other cases of
   the match are unreachable.

Now, turning to the second case, we have a pattern like this:

.. code-block:: fstar

   match v with
   | Cons hd tl ->

But, recall that ``Cons`` has an implicit first argument describing
the length of ``tl``. So, more explicitly, our pattern is of the form
below, where ``tl : vec a m``.

.. code-block:: fstar

   match v with
   | Cons #m hd tl ->

F* typechecks the branch in a context that includes the equation that
``v == Cons #m hd tl``, which lets the solve conclude that ``n == m +
1``, from the type of ``Cons``.

If ``i=0``, we've found the element we want and return it.

Otherwise, we make a recursive call ``get (i - 1) tl`` and now F* has
to:

  * Instantiate the implicit argument of ``get`` to ``m``, the length
    of ``tl``. That is, in explicit form, this recursive call is
    really ``get #m (i - 1) tl``. F* does this by relying on a
    unification algorithm implemented as part of its type inference
    procedure.

  * Prove that ``(i - 1) < m``, which follows from ``i < m`` and ``n
    == m + 1``.

  * Prove that the recursive call terminates, by proving that ``m <<
    n``, or, equivalently, since ``m`` and ``n`` are natural numbers,
    ``m < n``. This is easy, since we have ``n == m + 1``.

Let's try a few exercises. The main work is to find a type for the
functions in question. Once you do, the rest of the code will "write
itself".

--------------------------------------------------------------------------------

Exercise: Concatenating vectors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`Click here <../code/exercises/Part2.Vec.fst>`_ for the exercise file.

Implement a function to concatenate vectors. It should have the
following signature:

.. code-block:: fstar

   val append #a #n #m (v1:vec a n) (v2:vec a m)
     : vec a (n + m)

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Vec.fst
       :language: fstar
       :start-after: SNIPPET_START: append
       :end-before: SNIPPET_END: append

--------------------------------------------------------------------------------

Exercise: Splitting a vector
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Write a function called ``split_at`` to split a vector ``v : vec a n``
at index ``i`` into its ``i`` -length prefix from position ``0`` and a
suffix starting at ``i``.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Vec.fst
       :language: fstar
       :start-after: SNIPPET_START: split_at
       :end-before: SNIPPET_END: split_at

--------------------------------------------------------------------------------

Write a tail-recursive version of ``split_at``. You will need a
``reverse`` function as a helper

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Vec.fst
       :language: fstar
       :start-after: SNIPPET_START: reverse
       :end-before: SNIPPET_END: reverse

    .. literalinclude:: ../code/Vec.fst
       :language: fstar
       :start-after: SNIPPET_START: split_at_tail
       :end-before: SNIPPET_END: split_at_tail

Bonus: Prove ``split_at`` and ``split_at_tail`` are equivalent.
