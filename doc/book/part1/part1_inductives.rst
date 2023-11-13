.. _Part1_ch3:

Inductive types and pattern matching
====================================

In this chapter, you'll learn how to define new types in F*. These
types are called *inductive types*, or, more informally,
datatypes. We'll also learn how to define functions over these
inductive types by pattern matching and to prove properties about
them.

.. note::

   We'll only cover the most basic forms of inductive types here. In
   particular, the types we show here will not make use of indexing or
   any other form of dependent types---we'll leave that for a later
   chapter.

Enumerations
^^^^^^^^^^^^

We've seen that ``unit`` is the type with just one element ``()`` and
that ``bool`` is the type with two elements, ``true`` and ``false``.

You can define your own types with an enumeration of elements, like so.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: three
   :end-before: //SNIPPET_END: three

This introduces a new type ``three : Type``, and three *distinct*
constants ``One_of_three : three``, ``Two_of_three : three``,
``Three_of_three : three``. These constants are also called
"constructors" or "data constructors". The name of a constructor must
begin with an uppercase letter.

.. note::

   In this case, it may seem redundant to have to write the type of
   each constructor repeatedly—of course they're all just constructors
   of the type ``three``. In this case, F* will allow you to just
   write

   .. code-block:: fstar

      type three =
        | One_of_three
        | Two_of_three
        | Three_of_three

   However, in general, as we start to use indexed types, each
   constructor can build a different instance of the defined type, so
   it will be important to have a way to specify the result type of
   each constructor. For uniformity, throughout this book, we'll
   always annotate the types of constructors, even when not strictly
   necessary.

F* can prove that they are distinct and that these are the only terms
of type ``three``.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: assert
   :end-before: //SNIPPET_END: assert

To write functions that case analyze these new types, one uses the
``match`` construct. The syntax of ``match`` in F* is very similar to
OCaml or F#. We'll assume that you're familiar with its basics. As we
go, we'll learn about more advanced ways to use ``match``.

Here are some examples.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: disc_handrolled
   :end-before: //SNIPPET_END: disc_handrolled

Discriminators
..............

These functions test whether ``x : three`` matches a given
constructor, returning a ``bool`` in each case. Since it's so common
to write functions that test whether a value of an inductive type
matches one of its constructors, F* automatically generates these
functions for you. For example, instead of writing

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: three_as_int
   :end-before: //SNIPPET_END: three_as_int

One can write:

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: three_as_int'
   :end-before: //SNIPPET_END: three_as_int'

In other words, for every constructor ``T`` of an inductive type
``t``, F* generates a function named ``T?`` (called a "discriminator")
which tests if a ``v:t`` matches ``T``.

Exhaustiveness
..............

Of course, an even more direct way of writing ``three_as_int`` is

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: three_as_int''
   :end-before: //SNIPPET_END: three_as_int''

Every time you use a ``match``, F* will make sure to prove that you
are handling all possible cases. Try omitting one of the cases in
``three_as_int`` above and see what happens.

Exhaustiveness checking in F* is a semantic check and can use the SMT
solver to prove that all cases are handled appropriately. For example,
you can write this:

.. code-block:: fstar

   let only_two_as_int (x:three { not (Three_of_three? x) })
     : int
     = match x with
       | One_of_three -> 1
       | Two_of_three -> 2

The refinement on the argument allows F* to prove that the
``Three_of_three`` case in the pattern is not required, since that
branch would be unreachable anyway.

.. _Part1_tuples:

Tuples
^^^^^^

The next step from enumerations is to define composite types, e.g.,
types that are made from pairs, triples, quadruples, etc. of other
types. Here's how

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: tup
   :end-before: //SNIPPET_END: tup

The type definition for ``tup2 a b`` states that for any types ``a :
Type`` and ``b : Type``, ``Tup2 : a -> b -> tup2 a b``. That is,
``Tup2`` is a constructor of ``tup2``, such that given ``x:a`` and
``y:b``, ``Tup2 x y : tup2 a b``.

The other types ``tup3`` and ``tup4`` are similar---the type
annotations on the bound variables can be inferred.

These are inductive types with just one case---so the discriminators
``Tup2?``, ``Tup3?``, and ``Tup4?`` aren't particularly useful. But,
we need a way to extract, or *project*, the components of a tuple. You
can do that with a ``match``.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: proj_handrolled
   :end-before: //SNIPPET_END: proj_handrolled

Projectors
..........

These projectors are common enough that F* auto-generates them for
you. In particular, for any data constructor ``T`` of type
``x1:t1 -> ... -> xn:tn -> t``, F* auto-generates the following function:

   * ``T?.xi : y:t{T? y} -> ti``

That is, ``T?.xi`` is a function which when applied to a ``y:t`` in
case ``T? y``, returns the ``xi`` component of ``T x1 ... xn``.

In the case of our ``tup2`` and ``tup3`` types, we have

   * ``Tup2?.fst``, ``Tup2?.snd``
   * ``Tup3?.fst``, ``Tup3?.snd``, ``Tup3?.thd``

Syntax for tuples
.................

Since tuples are so common, the module ``FStar.Pervasives.Native.fst``
defines tuple types up to arity 14. So, you shouldn't have to define
``tup2`` and ``tup3`` etc. by yourself.

The tuple types in ``FStar.Pervasives.Native`` come with syntactic
sugar.

* You can write ``a & b`` instead of the ``tup2 a b``; ``a & b & c``
  instead of ``tup3 a b c``; and so on, up to arity 14.

* You can write ``x, y`` instead of ``Tup2 x y``; ``x, y, z`` instead
  of ``Tup3 x y z``; an so on, up to arity 14.

* You can write ``x._1``, ``x._2``, ``x._3``, etc. to project the
  field ``i`` of a tuple whose arity is at least ``i``.

That said, if you're using tuples beyond arity 4 or 5, it's probably a
good idea to define a *record*, as we'll see next—since it can be hard
to remember what the components of a large tuple represent.

.. _Part1_records:

Records
.......

A record is just a tuple with user-chosen names for its fields and
with special syntax for constructing then and projecting their
fields. Here's an example.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: point
   :end-before: //SNIPPET_END: point

* A record type is defined using curly braces ``{}``. See ``type
  point3D``

* A record value is also constructed using curly braces, with an
  assignment for each field of the record. The fields need not be
  given in order. See ``origin``.

* To access the fields of a record, you can use the dot notation
  ``p.x``; See ``dot``, which computes a dot product using dot
  notation.

* Records also support the ``with`` notation to construct a new record
  whose fields are the same as the old record, except for those fields
  mentioned after the ``with``. That is, ``translate_X p shift``
  returns ``{ x = p.x + shift; y = p.y; z = p.z}``.

* Records can also be used to pattern match a value. For example, in
  ``is_origin``, we match the fields of the record (in any order)
  against some patterns.

Options
^^^^^^^

Another common type from F*'s standard library is the ``option`` type,
which is useful to represent a possibly missing value.

.. code-block::fstar

   type option a =
     | None : option a
     | Some : a -> option a

Consider implementing a function to divide ``x / y``, for two integers
``x`` and ``y``. This function cannot be defined when ``y`` is zero,
but it can be defined partially, by excluding the case where ``y =
0``, as shown below. (Of course, one can also refine the domain of the
function to forbid ``y = 0``, but we're just trying to illustrate the
``option`` type here.)

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: option
   :end-before: //SNIPPET_END: option

Like most other functional languages, F* does not have a ``null``
value. Whenever a value may possibly be ``null``, one typically uses
the ``option`` type, using ``None`` to signify null and ``Some v`` for
the non-null case.

Unions, or the ``either`` type
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

``FStar.Pervasives`` also defines the ``either`` type, shown below.

.. code-block:: fstar

   type either a b =
     | Inl : v: a -> either a b
     | Inr : v: b -> either a b

The type ``either a b`` represents a value that could either be ``Inl
v`` with ``v:a``, or ``Inr v`` with ``v:b``. That is, ``either a b``
is a tagged union of the ``a`` and ``b``. It's easy to write functions
to analyze the tag ``Inl`` (meaning it's "in the left case") or
``Inr`` ("in the right case") and compute with the underlying
values. Here's an example:

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: either
   :end-before: //SNIPPET_END: either

The ``same_case x y`` function decides if the two unions are both
simultaneously in the left or right case.

Then, in ``sum x y``, with a refinement that ``x`` and ``y`` are in
the same case, we can handle just two cases (when they are both in
left, or both in right) and F* can prove that the case analysis is
exhaustive. In the left case, the underlying values are boolean, so we
combine them with ``||``; in the right case, the underlying values are
integers, so we combine them with ``+``; and return them with the
appropriate tag. The type of the result ``z:either bool int{ Inl? z <==>
Inl? x}`` shows that the result has the same case as ``x`` (and hence
also ``y``). We could have written the result type as ``z:either bool
int { same_case z x }``.

.. _Part1_inductives_list:

Lists
^^^^^

All the types we've see far have been inductive only in a degenerate
sense—the constructors do not refer to the types they construct. Now,
for our first truly inductive type, a list.

Here's the definition of ``list`` from ``Prims``:

.. code-block:: fstar

   type list a =
     | Nil  : list a
     | Cons : hd:a -> tl:list a -> list a

The ``list`` type is available implicitly in all F* programs and we
have special (but standard) syntax for the list constructors:

* ``[]`` is ``Nil``
* ``[v1; ...; vn]`` is ``Cons v1 ... (Cons vn Nil)``
* ``hd :: tl`` is ``Cons hd tl``.

You can always just write out the constructors like `Nil` and `Cons`
explicitly, if you find that useful (e.g., to partially apply ``Cons
hd : list a -> list a``).

.. _Part1_inductives_length:

Length of a list
................

Let's write some simple functions on lists, starting with computing
the length of a list.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: length
   :end-before: //SNIPPET_END: length

The ``length`` function is recursive and implicitly polymorphic in a
type ``a``. For any list ``l : list a``, ``length l`` returns a
``nat``. The definition pattern matches on the list and calls
``length`` recursively on the tail of list, until the ``[]`` case is
reached.

.. _Part1_inductives_append:

Exercises
^^^^^^^^^

`Click here <../code/exercises/Part1.Inductives.fst>`_ for the exercise file.

Here's the definition of ``append``, a function that concatenates two
lists. Can you give it a type that proves it always returns a list
whose length is the sum of the lengths of its arguments?

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: def append
   :end-before: //SNIPPET_END: def append

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Inductives.fst
       :language: fstar
       :start-after: SNIPPET_START: sig append
       :end-before: SNIPPET_END: sig append
