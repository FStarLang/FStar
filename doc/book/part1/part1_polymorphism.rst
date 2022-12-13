.. _Part1_polymorphism_and_inference:

Polymorphism and type inference
===============================

In this chapter, we'll learn about defining type polymorphic
functions, or how to work with generic types.

.. _Part1_type_of_types:

Type: The type of types
^^^^^^^^^^^^^^^^^^^^^^^

One characteristic of F* (and many other dependently typed languages)
is that it treats programs and their types uniformly, all within a
single syntactic class. A type system in this style is sometimes
called a *Pure Type System* or `PTS
<https://en.wikipedia.org/wiki/Pure_type_system>`_.

In F* (as in other PTSs) types have types too, functions can take
types as arguments and return types as results, etc. In particular,
the type of a type is ``Type``, e.g., ``bool : Type``, ``int : Type``,
``int -> int : Type`` etc. In fact, even ``Type`` has a type---as
we'll see when we learn about *universes*.

Parametric polymorphism or generics
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Most modern typed languages provide a way to write programs with
generic types. For instance, C# and Java provide generics, C++ has
templates, and languages like OCaml and Haskell have several kinds of
polymorphic types.

In F*, writing functions that are generic or polymorphic in types
arises naturally as a special case of the :ref:`arrow types
<Part1_ch1_arrows>` that we have already learned about. For example,
here's a polymorphic identity function::

  let id : a:Type -> a -> a = fun a x -> x

There are a several things to note here:

* The type of ``id`` is an arrow type, with two arguments. The first
  argument is ``a : Type``; the second argument is a term of type
  ``a``; and the result also has the same type ``a``.

* The definition of ``id`` is a lambda term with two arguments ``a :
  Type`` (corresponding to the first argument type) and ``x : a``. The
  function returns ``x``---it's an identity function on the second
  argument.

Just as with any function, you can write it instead like this:

.. literalinclude:: ../code/Part1.Poly.fst
   :language: fstar
   :start-after: //SNIPPET_START: id
   :end-before: //SNIPPET_END: id

To call ``id``, one can apply it first to a type and then to a value of that type, as shown below.

.. literalinclude:: ../code/Part1.Poly.fst
   :language: fstar
   :start-after: //SNIPPET_START: id applications
   :end-before: //SNIPPET_END: id applications

We've defined a function that can be applied to a value ``x:a`` for
any type ``a``. The last line there maybe requires a second read: we
instantiated ``id`` to ``int -> int`` and then applied it to ``id``
instantiated to ``int``.

Exercises
^^^^^^^^^

Let's try a few simple exercises. `Click here
<../code/exercises/Part1.Poly.fst>`_ for the exercise file.


Try defining functions with the following signatures:

.. literalinclude:: ../code/Part1.Poly.fst
   :language: fstar
   :start-after: //SNIPPET_START: sig apply_and_compose
   :end-before: //SNIPPET_END: sig apply_and_compose

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Poly.fst
       :language: fstar
       :start-after: //SNIPPET_START: apply_and_compose
       :end-before: //SNIPPET_END: apply_and_compose

How about writing down a signature for ``twice``:

.. literalinclude:: ../code/Part1.Poly.fst
   :language: fstar
   :start-after: //SNIPPET_START: def twice
   :end-before: //SNIPPET_END: def twice

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Poly.fst
       :language: fstar
       :start-after: SNIPPET_START: sig twice
       :end-before: SNIPPET_END: sig twice

It's quite tedious to have to explicitly provide that first type
argument to ``id``. Implicit arguments and type inference will help,
as we'll see, next.


Type inference: Basics
^^^^^^^^^^^^^^^^^^^^^^
.. _inference:

Like many other languages in the tradition of
`Milner's ML <https://en.wikipedia.org/wiki/ML_%28programming_language%29>`_,
type inference is a central component in F*'s design.

You may be used to type inference in other languages, where one can
leave out type annotations (e.g., on variables, or when using
type-polymorphic (aka generic) functions) and the compiler determines
an appropriate type based on the surrounding program context. F*'s
type inference includes such a feature, but is considerably more
powerful. Like in other dependently typed language, F*'s inference
engine is based on `higher-order unification
<https://en.wikipedia.org/wiki/Unification_(computer_science)#Higher-order_unification>`_
and can be used to infer arbitrary fragments of program text, not just
type annotations on variables.

Let's consider our simple example of the definition and use of the
identity function again

.. literalinclude:: ../code/Part1.Poly.fst
   :language: fstar
   :start-after: //SNIPPET_START: id
   :end-before: //SNIPPET_END: id

.. literalinclude:: ../code/Part1.Poly.fst
   :language: fstar
   :start-after: //SNIPPET_START: id applications
   :end-before: //SNIPPET_END: id applications

Instead of explicitly providing that first type argument when applying
``id``, one could write it as follows, replacing the type arguments
with an underscore ``_``.

.. literalinclude:: ../code/Part1.Poly.fst
   :language: fstar
   :start-after: //SNIPPET_START: implicit id applications
   :end-before: //SNIPPET_END: implicit id applications

The underscore symbols is a wildcard, or a hole in program, and it's
the job of the F* typechecker to fill in the hole.

.. note::

   Program holes are a very powerful concept and form the basis of
   Meta-F*, the metaprogramming and tactics framework embedded in
   F*---we'll see more about holes in a later section.

Implicit arguments
^^^^^^^^^^^^^^^^^^

Since it's tedious to write an ``_`` everywhere, F* has a notion of
*implicit arguments*. That is, when defining a function, one can add
annotations to indicate that certain arguments can be omitted at call
sites and left for the typechecker to infer automatically.

For example, one could write

.. literalinclude:: ../code/Part1.Poly2.fst
   :language: fstar
   :start-after: //SNIPPET_START: id
   :end-before: //SNIPPET_END: id

decorating the first argument ``a`` with a ``#``, to indicate that it is
an implicit argument. Then at call sites, one can simply write:

.. literalinclude:: ../code/Part1.Poly2.fst
   :language: fstar
   :start-after: //SNIPPET_START: id applications
   :end-before: //SNIPPET_END: id applications


And F* will figure out instantiations for the missing first argument
to ``id``.

In some cases, it may be useful to actually provide an implicit
argument explicitly, rather than relying on the F* to pick one. For
example, one could write the following:

.. literalinclude:: ../code/Part1.Poly2.fst
   :language: fstar
   :start-after: //SNIPPET_START: explicit id applications
   :end-before: //SNIPPET_END: explicit id applications

In each case, we provide the first argument of ``id`` explicitly, by
preceding it with a ``#`` sign, which instructs F* to take the user's
term rather than generating a hole and trying to fill it.
