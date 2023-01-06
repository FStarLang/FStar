.. _Part4_Computation_Types_And_Tot:

Computation Types and the Tot effect
=====================================

At its core, a main goal for F*'s effect system is to *track
dependences* among the various parts of a program. For example, the
effect system needs to ensures that the total part of a program that
is proven to always terminate never calls a function in the divergent
fragment (since that function call may loop forever). Or, that the
runtime behavior of a compiled program does not depend on ghost
computations that get erased by the compiler.

In a paper from 1999 called `A Core Calculus of Dependency
<https://dl.acm.org/doi/pdf/10.1145/292540.292555>`_, Abadi, Banerjee,
Heintze, and Riecke present DCC, a language with a very generic way to
track dependences. DCC's type system has a family of computation types
arranged in hierarchy (a partial order induced by lattice), where a
computations can only depend on other computations whose type is less
than (or at the same level as) it in the partial order.

Very briefly, DCC includes a family of *computation types* :math:`T_l`,
where the label :math:`l` ranges over the elements of a lattice
:math:`L`, where some pairs of labels may be related by :math:`l_1
\leq l_2`. The key typing rule in DCC defines how computations compose
sequentially using ``bind x = e1 in e2``: if ``e1`` has type
:math:`T_{l_1}(t)`, then assuming that ``x`` has type :math:`t`,
``e2`` must have a type like :math:`T_{l_2}(t_2)`, where :math:`l_1
\leq l_2`. That is, since ``e2`` *depends* on the result of a
computation ``e1`` at level :math:`l_1`, ``e2``'s type must be at
least at the same level.

The design of F*'s effect system draws inspiration from DCC.
Computation types in F* take the form ``M t`` where ``M`` is an
*effect label* and ``t`` is the return type of the computation.  The
effect label of an F* computation type is drawn from an open-ended,
user-extensible set of labels, where the labels are organized in a
user-chosen partial order. The rule for composing computations that
have different effect labels are based on a rule similar to DCC's,
though things become more involved due to F*'s dependent types. The
spirit of DCC's main result remains: computations can only depend on
other computations at the same level or lower than it in the effect
label hierarchy.

Roughly, a term ``e`` can be given the computation type ``M t`` when
executing ``e`` exhibits *at-most* the effect ``M`` and (possibly)
returns a value of type ``t``. We will refine this intuition as we go
along. In contrast with computation types, the types that we have seen
so far (``unit``, ``bool``, ``int``, ``list int``, other inductive
types, refinement types, and arrows) are called *value types*.


The default ``Tot`` effect
^^^^^^^^^^^^^^^^^^^^^^^^^^

At the very bottom of the effect label hierarchy is ``Tot``, used to
describe pure, total functions. Since they are at the bottom of the
hierarchy, ``Tot`` computations can only depend on other ``Tot``
computations, ensuring that F*'s logical core remains total.

Every term in F* is typechecked to have a computation type. This
includes the total terms we have been working with. Such terms are
classified in the default effect called ``Tot``, the effect of total
computations that do not have any observable effect, aside from the
value they return. Any meaning or intuition that we have ascribed to
typing ``e:t`` extends to ``e:Tot t``. For example, if ``e:Tot t``,
then at runtime, ``e`` terminates and produces a value of type
``t``. In addition, since its effect label is ``Tot``, it has no
side-effect.

In fact, as we have already :ref:`seen <Part1_ch1_arrow_notations>`,
notationally ``x:t0 -> t1`` is a shorthand for ``x:t0 -> Tot t1``
(where ``t1`` could itself be an arrow type). More generally, arrow
types in F* take the form ``x:t -> C``, representing a function with
argument type ``t0`` and body computation type ``C`` (which may depend
on ``x``).

Similarly, the return type annotation that we have seen in the ``let``
definitions is also a shorthand, e.g., the :ref:`id function
<Part1_polymorphism_and_inference>`

.. code-block:: fstar
                
  let id (a:Type) (x:a) : a = x

is a shorthand for

.. code-block:: fstar
                
  let id (a:Type) (x:a) : Tot a = x  //the return type annotation is a computation type

and the type of ``id`` is ``a:Type -> a -> Tot a``. More generally,
the return type annotations on ``let`` definitions are computation
types ``C``.

The :ref:`explicit annotation syntax <Part1_ch1_named_function>` ``e
<: t`` behaves a little differently. F* allows writing ``e <: C``, and
checks that ``e`` indeed has computation type ``C``. But when the
effect label is omitted, ``e <: t``, it is interpreted as ``e <: _
t``, where the omitted effect label is inferred by F* and does not
default to ``Tot``.


Evaluation order
^^^^^^^^^^^^^^^^

For pure functions, the evaluation order is irrelevant. [#]_ F*
provides abstract machines to interpret pure terms using either a lazy
evaluation strategy or a call-by-value strategy (see a
:ref:`forthcoming chapter on F*'s normalizers
<Under_the_hood>`). Further, compiling pure programs to OCaml, F*
inherits the OCaml's call-by-value semantics for pure terms.

When evaluating function calls with effectful arguments, the arguments
are reduced to values first, exhibiting their effects, if any, prior
to the function call. That is, where ``e1`` and ``e2`` may be
effectful, the application ``e1 e2`` is analogous to ``bind f = e1 in
bind x = e2 in f x``: in fact, internally this is what F* elaborates
``e1 e2`` to, when either of them may have non-trivial effects.  As
such, for effectful terms, F* enforces a left-to-right, `call-by-value
<https://en.wikipedia.org/wiki/Evaluation_strategy/>`_ semantics for
effectful terms.

Since only the value returned by a computation is passed as an
argument to a function, function argument types in F* are always value
types. That is, they always have the form ``t -> C``. To pass a
computation as an argument to another function, you must encapsulate
the computation in a function, e.g., in place of ``C -> C``, one can
write ``(unit -> C) -> C'``. Since functions are first-class values in
F*, including functions whose body may have non-trivial effects, one
can always do this.

.. [#] Since F* is an extensional type theory, pure F* terms are only
       *weakly* normalizing. That is, some evaluation strategies need
       (e.g., repeatedly reducing a recursive function deep in an
       infeasible code path) need not terminate. However, for every
       closed, pure F*, there is a reduction strategy that will reduce
       it fully. As such, the evaluation order for pure functions is
       irrelevant, except that some choices of evaluation order may
       lead to non-termination.
       
