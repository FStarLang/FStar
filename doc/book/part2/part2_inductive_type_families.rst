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
