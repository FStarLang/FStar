.. _Part3_typeclasses:

Typeclasses
===========

Consider writing a program using bounded unsigned integers while being
generic in the actual bounded integer type, E.g., a function that sums
a list of bounded integers while checking for overflow, applicable to
both ``UInt32`` and ``UInt64``. Since F*'s interfaces are not
first-class, one can't easily write a program that abstracts over
those interfaces. Typeclasses can help.

Some background reading on typeclasses:

  * Phil Wadler and Stephen Blott introduced the idea in 1989 in a
    paper titled "`How to make ad hoc polymorphism less ad hoc
    <https://dl.acm.org/doi/10.1145/75277.75283>`_." Their work, with
    many extensions over the years, is the basis of Haskell's
    typeclasses.

  * A tutorial on typeclasses in the Coq proof assistant is available
    `here
    <https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html>`_.

  * Typeclasses are used heavily in the Lean proof assistant to
    structure its `math library
    <https://arxiv.org/pdf/1910.09336.pdf>`_.

Printable
---------

A typeclass associates a set of *methods* to a tuple of types,
corresponding the operations that can be performed using those
types.

For instance, some types may support an operation that enables them to
be printed as strings. A typeclass ``printable (a:Type)`` represent
the class of all types that support a ``to_string : a -> string``
operation.

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: printable$
   :end-before: //SNIPPET_END: printable$

The keyword ``class`` introduces a new typeclass, defined as a
:ref:`record type <Part1_records>` with each method represented as a
field of the record.

To define instances of a typeclass, one uses the ``instance`` keyword,
as shown below.

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: printable_bool_and_int$
   :end-before: //SNIPPET_END: printable_bool_and_int$

The notation ``instance printable_bool : printable bool = e`` states
that the value ``e`` is a record value of type ``printable bool``, and
just as with a ``let``-binding, the term ``e`` is bound to the
top-level name ``printable_bool``.

The convenience of typeclasses is that having defined a class, the
typeclass method is automatically overloaded for all instances of the
class, and the type inference algorithm finds the suitable instance to
use. This is original motivation of typeclasses---a principled
approach to operator overloading.

For instance, we can now write ``printb`` and ``printi`` and use
``to_string`` to print both booleans and integers, since we shown that
they are instances of the class ``printable``.

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: printb and printi$
   :end-before: //SNIPPET_END: printb and printi$

Instances need not be only for base types. For example, all lists are
printable so long as their elements are, and this is captured by what
follows.

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: printable_list$
   :end-before: //SNIPPET_END: printable_list$

That is, ``printable_list`` constructs a ``to_string`` method of type
``list a -> string`` by mapping the ``to_string`` method of the
``printable a`` instance over the list. And now we can use
``to_string`` with lists of booleans and integers too.

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: printis and printbs$
   :end-before: //SNIPPET_END: printis and printbs$

There's nothing particularly specific about the ground instances
``printable bool`` and ``printable int``. It's possible to write
programs that are polymorphic in printable types. For example, here's
a function ``print_any_list`` that is explicitly parameterized by a
``printable a``---one can call it by passing in the instance that one
wishes to use explicitly:

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: print_any_list_explicit$
   :end-before: //SNIPPET_END: print_any_list_explicit$

However, we can do better and have the compiler figure out which
instance we intend to use by using a bit of special syntax for a
typeclass parameter, as shown below.

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: print_any_list$
   :end-before: //SNIPPET_END: print_any_list$

The parameter ``{| _ : printable a |}`` indicates an implicit argument
that, at each call site, is to be computed by the compiler by finding
a suitable typeclass instance derivable from the instances in
scope. In the first example above, F* figures out that the instance
needed is ``printable_list printable_int : printable (list
int)``. Note, you can always pass the typeclass instance you want
explicitly, if you really want to, as the second example ``_ex2``
above shows.

In many cases, the implicit typeclass argument need not be named, in
which case one can just omit the name and write:

.. literalinclude:: ../code/Typeclasses.fst
   :language: fstar
   :start-after: //SNIPPET_START: print_any_list_alt$
   :end-before: //SNIPPET_END: print_any_list_alt$

Under the hood
..............

When defining a ``class``, F* automatically generates generic
functions corresponding to the methods of the class. For instance, in
the case of ``printable``, F* generates:

.. code-block:: fstar

   let to_string #a {| i : printable a |} (x:a) = i.to_string x

Having this in scope overloads ``to_string`` for all instance of the
``printable`` class. In the implementation of ``to_string``, we use
the instance ``i`` (just a record, sometimes called a dictionary in
the typeclass literature) and project its ``to_string`` field and
apply it to ``x``.

When declaring an ``instance p x1..xn : t = e`` declaration is just
like an ordinary let binding ``let p x1..xn : t = e``, however the
``instance`` keyword instructs F*'s type inference algorithm to
consider to use ``p`` when trying to instantiate implicit arguments
for typeclass instances.

For example, at the call site ``to_string (x:bool)``, having unified
the implicit type arguments ``a`` with ``bool``, what remains is to
find an instance of ``printable bool``. F* looks through the current
context for all variable bindings in the local scope, and ``instance``
declarations in the top-level scope, for a instance of ``printable
bool``, taking the first one it is able to construct.

The resolution procedure for ``to_string [[1;2;3]]`` is a bit more
interesting, since we need to find an instance ``printable (list
int)``, although no such ground instance exists. However, the
typeclass resolution procedure finds the ``printable_list`` instance
function, whose result type ``printable (list a)`` matches the goal
``printable (list int)``, provided ``a = int``. The resolution
procedure then spaws a sub-goal of ``printable int``, which it solves
easily and completes the derivation of ``printable (list int)``.

This backwards, goal-directed search for typeclass resolution is a
kind of logic programming. An interesting implementation detail is
that most of the typeclass machinery is defined as a metaprogran in
``FStar.Tactics.Typeclasses``, outside of the core of F*'s compiler. As
such, the behavior of typeclass resolution is entirely
user-customizable, simply by revising the metaprogram in use. Some
details about how this works can be found in a paper on `Meta F*
<http://fstar-lang.org/papers/metafstar/>`_

Exercises
.........

Define instances of ``printable`` for ``string``, ``a & b``, ``option
a``, and ``either a b``. Check that you can write ``to_string [Inl (0,
1); Inr (Inl (Some true)); Inr (Inr "hello") ]`` and have F* infer the
typeclass instance needed. Also write the typeclasss instance you need
explicitly, just to check that you understand how things work.


.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Typeclasses.fst
       :language: fstar
       :start-after: //SNIPPET_START: print_answer$
       :end-before: //SNIPPET_END: print_answer$

--------------------------------------------------------------------------------

Bounded Unsigned Integers
-------------------------

The ``printable`` typeclass is fairly standard and can be defined in
almost any language that supports typeclasses. We now turn to a
typeclass that leverages F*'s dependent types by generalizing the
interface of bounded unsigned integers that we developed in the
:ref:`previous chapter <Part3_interfaces>`.

A type ``a`` is in the class ``bounded_unsigned_int``, when it
admits:

  * An element ``bound : a``, representing the maximum value

  * A pair of function ``from_nat`` and ``to_nat`` that form a
    bijection between ``a`` and natural numbers less that ``to_nat
    bound``

This is captured by the ``class`` below:

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: bounded_unsigned_int$
   :end-before: //SNIPPET_END: bounded_unsigned_int$

.. note ::

   The attribute ``FStar.Tactics.Typeclasses.no_method`` on the
   ``properties`` field instructs F* to not generate a typeclass
   method for this field.

For all ``bounded_unsigned_ints``, one can define a generic ``fits``
predicate, corresponding to the bounds check condition that we
introduced in the ``UInt32`` interface.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: fits$
   :end-before: //SNIPPET_END: fits$

Likewise, the predicate ``related_ops`` defines when an operation
``bop`` on bounded integers is equivalent to an operation on
mathematical integers.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: related_ops$
   :end-before: //SNIPPET_END: related_ops$

Typeclass Inheritance
.....................

Our ``bounded_unsigned_int a`` class just showed that ``a`` is in a
bijection with natural numbers below some bound. Now, we can define a
separate class, extending ``bounded_unsigned_int`` with the operations
we want, like addition, subtraction, etc.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: bui_ops$
   :end-before: //SNIPPET_END: bui_ops$

The class above makes use of *typeclass inheritance*. The ``base``
field stores an instance of the base class ``bounded_unsigned_int``,
while the remaining fields extend it with a

  * ``add``: a bounded addition operation
  * ``sub``: a bounded subtraction operation
  * ``lt`` : a comparison function
  * ``properties``, which show that
      - ``add`` is related to integer addition ``+``
      - ``sub`` is related to integer subtraction ``-``
      - ``lt`` is related to ``<``
      - and that ``sub bound x`` is always safe

Typeclass inheritance in the form of additional fields like ``base``
is completely flexible, e.g., multiple inheritance is permissible
(though, as we'll see below, should be used with care, to prevent
surprises).

Treating an instance of a class as an instance of one its base classes
is easily coded as instance-generating function. The code below says
that an instance from ``bounded_unsigned_int a`` can be derived from
an instance of ``d : bounded_unsigned_int_ops a`` just by projecting
its ``base`` field.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: ops_base$
   :end-before: //SNIPPET_END: ops_base$


Infix Operators
...............

F* does not allows the fields of a record to be named using infix
operator symbols. This will likely change in the future. For now,
to use custom operations with infix notation for typeclass methods,
one has to define them by hand:

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: ops$
   :end-before: //SNIPPET_END: ops$

Derived Instances
.................

We've already seen how typeclass inheritance allows a class to induce
an instance of its base class(es). However, not all derived instances
are due to explicit inheritance---some instances can be *computed*
from others.

For example, here's a class ``eq`` for types that support a decidable
equality.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: eq$
   :end-before: //SNIPPET_END: eq$

We'll write ``x =?= y`` for an equality comparison method from this
class, to not confuse it with F*'s built-in deciadble equality ``(=)``
on ``eqtype``.

Now, from from an instance of ``bounded_unsigned_int_ops a`` we can
compute an instance of ``eq a``, since we have ``<^``, a strict
comparison operator that we know is equivalent to ``<`` on natural
numbers. F*, from all the properties we have on
``bounded_unsigned_int_ops`` and its base class
``bounded_unsigned_int``, can automatically prove that ``not (x <^ y)
&& not (y <^ x)`` is valid if and only if ``x == y``. This instance of
``eq`` now also lets us easily implement in non-strict comparison
operation on bounded unsigned ints.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: bui_eq$
   :end-before: //SNIPPET_END: bui_eq$

Ground Instances
................

We can easily provide ground instances of ``bounded_unsigned_int_ops``
for all the F* bounded unsigned int types---we show instances for
``FStar.UInt32.t`` and ``FStar.UInt64.t``, where the proof of all the
properties needed to construct the instances is automated.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: ground_instances$
   :end-before: //SNIPPET_END: ground_instances$

And one can check that typeclass resolution works well on those ground
instances.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: ground_tests$
   :end-before: //SNIPPET_END: ground_tests$

Finally, as promised at the start, we can write functions that are
generic over all bounded unsigned integers, something we couldn't do
with interfaces alone.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: sum$
   :end-before: //SNIPPET_END: sum$

F* can prove that the bounds check in ``sum`` is sufficient to prove
that the addition does not overflow, and further, that the two tests
return ``Some _`` without failing due to overflow.

However, the proving that ``Some? (sum [0x01ul; 0x02ul; 0x03ul]
0x00ul)`` using the SMT solver alone can be expensive, since it
requires repeated unfolding of the recursive function ``sum``--such
proofs are often more easily done using F*'s normalizer, as shown
below.

.. literalinclude:: ../code/TypeclassesAlt3.fst
   :language: fstar
   :start-after: //SNIPPET_START: testsum32'$
   :end-before: //SNIPPET_END: testsum32'$

.. note::

   We saw the ``assert_norm`` construct in a :ref:`previous section
   <Part2_par>`.

.. note ::

   That said, by using dependently typed generic programming (which we
   saw a bit of :ref:`earlier <Part2_phoas_denotation>`), it is
   possible to write programs that abstract over all machine integer
   types without using typeclasses. The F* library ``FStar.Integers``
   shows how that works. Though, the typeclass approach shown here is
   more broadly applicable an extensible.

Dealing with Diamonds
---------------------

One may be tempted to factor our ``bounded_unsigned_int_ops``
typeclass further, separating out each operation into a separate
class. After all, it may be the case that some instances of
``bounded_unsigned_int`` types support only addition while others
support only subtraction. However, when designing typeclass
hierarchies one needs to be careful to not introduce coherence
problems that result from various forms of multiple inheritance.

Here's a typeclass that captures only the subtraction operation,
inheriting from a base class.

.. literalinclude:: ../code/TypeclassesAlt2.fst
   :language: fstar
   :start-after: //SNIPPET_START: subtractable$
   :end-before: //SNIPPET_END: subtractable$

And here's another typeclass that, say, provides only the comparison
operation, also inheriting from the base class.

.. literalinclude:: ../code/TypeclassesAlt2.fst
   :language: fstar
   :start-after: //SNIPPET_START: comparable$
   :end-before: //SNIPPET_END: comparable$

However, now when writing programs that expect both subtractable and
comparable integers, we end up with a coherence problem.

The ``sub`` operation fails to verify, with F* complaining that it
cannot prove ``fits op_Subtraction bound acc``, i.e., this ``sub`` may
underflow.

.. literalinclude:: ../code/TypeclassesAlt2.fst
   :language: fstar
   :start-after: //SNIPPET_START: try_sub_fail$
   :end-before: //SNIPPET_END: try_sub_fail$

At first, one may be surprised, since the ``s :
subtractable_bounded_unsigned_int a`` instance tells us that
subtracting from the ``bound`` is always safe. However, the term
``bound`` is an overloaded (nullary) operator and there are two ways
to resolve it: ``s.base.bound`` or ``c.base.bound`` and these two
choices are not equivalent. In particular, from ``s :
subtractable_bounded_unsigned_int a``, we only know that
``s.base.bound `sub` acc`` is safe, not that ``c.base.bound `sub`
acc`` is safe.

Slicing type typeclass hierarchy too finely can lead to such coherence
problems that can be hard to diagnose. It's better to avoid them by
construction, if at all possible. Alternatively, if such problems do
arise, one can sometimes add additional preconditions to ensure that
the multiple choices are actually equivalent. There are many ways to
do this, ranging from indexing typeclasses by their base classes, to
adding equality hypotheses---the equality hypothesis below is
sufficient.

.. literalinclude:: ../code/TypeclassesAlt2.fst
   :language: fstar
   :start-after: //SNIPPET_START: try_sub$
   :end-before: //SNIPPET_END: try_sub$

Typeclasses at Higher-order
---------------------------
