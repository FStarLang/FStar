.. _Part1_equality:

Equality
========

Equality is a subtle issue that pervades the design of all dependent
type theories, and F* is no exception. In this first chapter, we
briefly touch upon two different kinds of equality in F*, providing
some basic information sufficient for the simplest usages. In a
:ref:`subsequent chapter <Part2_equality>`, we'll cover equality in
much greater depth.

Decidable equality and ``eqtype``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We've implicitly used the equality operator ``=`` already (e.g., when
defining ``factorial``). This is the *boolean* equality
operator. Given two terms ``e₁ : t`` and ``e₂ : t``, so long as ``t``
supports a notion of decidable equality, ``(e₁ = e₂) : bool``.

To see why not all types support decidably equality, consider ``t`` to
be a function type, like ``int -> int``. To decide if two functions
``f₁, f₂ : int -> int`` are equal, we'd have to apply them to all the
infinitely many integers and compare their results—clearly, this is
not decidable.

The type ``eqtype`` is the type of types that support decidably
equality. That is, given ``e₁ : t`` and ``e₂ : t``, it is only
permissible to compare ``e₁ = e₂`` if ``t : eqtype``.

For any type definition, F* automatically computes whether or not that
type is an ``eqtype``. We'll explain later exactly how F* decides
whether or not a type is an ``eqtype``. Roughly, for F* has built-in
knowledge that various primitive types like integers and booleans
support decidable equality. When defining a new type, F* checks
that all values of the new type are composed structurally of terms
that support decidable equality. In particular, if an ``e : t`` may
contain a sub-term that is a function, then ``t`` cannot be an
``eqtype``.

As such, the type of the decidable equality operator is

.. code-block:: fstar

   val ( = ) (#a:eqtype) (x:a) (y:a) : bool

That is, ``x = y`` is well-typed only when ``x : a`` and ``y : a`` and
``a : eqtype``.

.. note::

   We see here a bit of F* syntax for defining infix operators. Rather
   than only using the ``val`` or ``let`` notation with alphanumeric
   identifiers, the notation ``( = )`` introduces an infix operator
   defined with non-alphanumeric symbols. You can read more about this
   `here
   <https://github.com/FStarLang/FStar/wiki/Parsing-and-operator-precedence>`_.



Propositional equality
^^^^^^^^^^^^^^^^^^^^^^

F* offers another notion of equality, propositional equality, written
``==``. For *any type* ``t``, given terms ``e₁, e₂ : t``, the
proposition ``e₁ == e₂`` asserts the (possibly undecidable) equality
of ``e₁`` and ``e₂``. The type of the propositional equality operator
is shown below:

.. code-block:: fstar

   val ( == ) (#a:Type) (x:a) (y:a) : prop

Unlike decidable equality ``(=)``, propositional equality is defined
for all types. The result type of ``(==)`` is ``prop``, the type of
propositions. We'll learn more about that in the :ref:`next chapter
<Part1_prop_assertions>`.
