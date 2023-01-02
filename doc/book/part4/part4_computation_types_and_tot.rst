.. _Part4_Computation_Types_And_Tot:

Computation Types and the Tot effect
=====================================

To specify effectful computations, F* has a notion of *computation
types*. A computation type, denoted with ``C``, takes the form ``M t``
where ``M`` is an effect label and ``t`` is the return type of the
computation. Roughly, an expression ``e`` can be typed as ``M t`` when
executing ``e`` exhibits *at-most* the effect ``M`` and returns a
value of type ``t``. We will refine this intuition as we go along. The
types that we have seen so far (``unit``, ``bool``, ``int``, inductive
types, etc.) are called *value types*.


The default ``Tot`` effect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Every expression in F* is typechecked to have a computation type. This
includes the total expressions we have been working with. Such
expressions are classified in the default effect called ``Tot``, the
effect of total computations that do not have any observable effect
other than the input-output behavior. Any meaning or intuition that we
have ascribed to ``e:t`` extends to ``e:Tot t``. For example,
if ``e:Tot t``, then at runtime, ``e`` terminates and produces a value
of type ``t``.

In fact, as we have already :ref:`seen <Part1_ch1_arrow_notations>`,
notationally ``x:t0 -> t1`` is a shorthand for ``x:t0 -> Tot t1``
(where ``t1`` could itself be an arrow type). More generally,
arrow types in F* take the form ``x:t0 -> C``, representing a function
with argument type ``t0`` and body computation type ``C``.

Similarly, the return type annotation that we have seen in the ``let``
definitions is also a shorthand, e.g., the :ref:`id function
<Part1_polymorphism_and_inference>`::

  let id (a:Type) (x:a) : a = x

is a shorthand for::

  let id (a:Type) (x:a) : Tot a = x

and the type of ``id`` is ``a:Type -> a -> Tot a``. More generally,
the return type annotations on ``let`` definitions are computation
types ``C``.


Function argument types
^^^^^^^^^^^^^^^^^^^^^^^^

Since all the expressions in F* have computation types, in general,
whereever a type annotation appears that types an expression, it is a
computation type annotation ``C``. When the effect label is omitted,
it defaults to ``Tot``. We have seen such examples of arrow co-domains
and return type annotations on ``let``.

.. note::

   One exception to this rule is the :ref:`explicit annotation syntax
   <Part1_ch1_named_function>` ``e <: t``. F* allows writing ``e <:
   C``, and checks that ``e`` indeed has type ``C``. But when the
   effect label is omitted, ``e <: t``, it is interpreted as ``e <: _
   t``, where the omitted effect label is inferred by F* and does not
   default to ``Tot``.


However, the function argument types in F* are always value
types. This is because F* has a `call-by-value
<https://en.wikipedia.org/wiki/Evaluation_strategy/>`_ semantics. It
means that the function arguments are evaluated at the function call
sites, and the resulting value is then passed on to the callee
functions. For example, if a function ``f`` is called as ``f e``,
then ``e`` is first evaluated to a value---which also means that the
effects of ``e`` happen at the call site---and then the
resulting value is passed to ``f``.

.. note::

   We can think of ``f e`` when ``e`` is effectful, as ``let x = e in
   f x``. In fact, this is what F* elaborates ``f e`` to, when ``e``
   has a non-trivial effect.

.. note::

   Since functions are first-class values in F*, including functions
   whose body have non-trivial effects, an effectful computation may
   be thunked and then passed as a value to a function.
