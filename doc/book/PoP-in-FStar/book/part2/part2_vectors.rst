.. _Part2_vectors:

Length-indexed Lists
====================

To make concrete some aspects of the formal definitions above, we'll
look at several variants of a parameterized list datatype augmented
with indexes that carry information about the list's length.

Even and Odd-lengthed Lists
...........................

Our first example is bit artifical, but helps illustrate a usage of
mutually inductive types.

Here, we're defining two types constructors called ``even`` and
``odd``, (i.e, just :math:`T_1` and :math:`T_2` from our formal
definition), both with a single parameter ``(a:Type)``, for the type
of the lists' elements, and no indexes.

All lists of type ``even a`` have an even number of elements---zero
elements, using its first constructor ``ENil``, or using ``ECons``,
one more than the number of elements in an ``odd a``, a list with an
odd number of elements. Elements of the type ``odd a`` are constructed
using the constructor ``OCons``, which adds a single element to an
``even a`` list. The types are mutually inductive since their
definitions reference each other.


.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: even_and_odd
   :end-before: //SNIPPET_END: even_and_odd

Although closely related, the types ``even a`` and ``odd a`` are from
distinct inductive types. So, to compute, say, the length of one of
these lists one generally write a pair of mutually recursive
functions, like so:

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: elength_and_olength
   :end-before: //SNIPPET_END: elength_and_olength

Note, we can prove that the length of an ``even a`` and ``odd a`` are
really even and odd.

Now, say, you wanted to map a function over an ``even a``, you'd have
to write a pair of mutually recursive functions to map simultaneoulsy
over them both. This can get tedious quickly. Instead of rolling out
several mutually inductive but distinct types, one can instead use an
*indexed* type to group related types in the same inductive family of
types.

The definition of ``even_or_odd_list`` below shows an inductive type
with one parameter ``a``, for the type of lists elements, and a single
boolean index, which indicates whether the list is even or odd. Note
how the index varies in the types of the constructors, whereas the
parameter stays the same in all instances.

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: even_or_odd_list
   :end-before: //SNIPPET_END: even_or_odd_list

Now, we have a single family of types for both even and odd lists, and
we can write a single function that abstracts over both even and odd
lists, just by abstracting over the boolean index. For example,
``eo_length`` computes the length of an ``even_or_odd_list``, with its
type showing that it returns an even number with ``b`` is true and an
odd number otherwise.

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: eo_length
   :end-before: //SNIPPET_END: eo_length

.. note::

   Note, in ``eo_length`` we had to explicitly specify a decreases
   clause to prove the function terminating. Why? Refer back to the
   section on :ref:`default
   measures<Part1_termination_default_measures>` to recall that by
   default is the lexicographic ordering of all the arguments in
   order. So, without the decreases clause, F* will try to prove that
   the index argument ``b`` decreases on the recursive call, which it
   does not.

This is our first type with with both parameters and indices. But why
stop at just indexing to distinguish even and odd-lengthed lists? We
can index a list by its length itself.

Vectors
.......

Let's look again at the definition of the ``vec`` type, first shown in
:ref:`the introduction<Intro_Vec>`.

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: vec
   :end-before: //SNIPPET_END: vec

Here, we're defining just a single type constructor called ``vec``
(i.e, just :math:`T_1`), which a single parameter ``(a:Type)`` and one
index ``nat``.

``vec`` has two data constructors: ``Nil`` builds an instance of ``vec
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
   a notation similar to OCaml or F# for those types in F*. For
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

  * Prove that ``(i - 1) < m``, which follows from ``i < n`` and ``n
    == m + 1``.

  * Prove that the recursive call terminates, by proving that ``m <<
    n``, or, equivalently, since ``m`` and ``n`` are natural numbers,
    ``m < n``. This is easy, since we have ``n == m + 1``.

Let's try a few exercises. The main work is to find a type for the
functions in question. Once you do, the rest of the code will "write
itself".

Exercises
.........


Exercise: Concatenating vectors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`Click here <../code/exercises/Part2.Vec.fst>`_ for the exercise file.

Implement a function to concatenate vectors. It should have the
following signature:

.. code-block:: fstar

   val append (#a:Type) (#n #m:nat) (v1:vec a n) (v2:vec a m)
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
``reverse`` function as a helper.

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

--------------------------------------------------------------------------------

Vectors: Probably not worth it
..............................

Many texts about dependent types showcase length-indexed vectors, much
as we've done here. Although useful as a simple illustrative example,
the ``vec`` type we've seen is probably not what you want to use in
practice. Especially in F*, where regular lists can easily be used
with refinement types, length-indexed vectors are redundant because we
simply refine our types using a ``length`` function. The code below
shows how:

    .. literalinclude:: ../code/LList.fst
       :language: fstar

In the next few sections, we'll see more useful examples of indexed
inductive types than just mere length-indexed vectors.
