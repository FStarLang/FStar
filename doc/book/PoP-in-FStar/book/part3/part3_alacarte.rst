.. _Part3_alacarte:

Fun with Typeclasses: Datatypes a la Carte
===========================================

In a classic 1998 post, Phil Wadler describes a difficulty in language and
library design: how to modularly extend a data type together with the operations
on those types. Wadler calls this the `Expression Problem
<https://homepages.inf.ed.ac.uk/wadler/papers/expression/expression.txt>`_,
saying:

   The Expression Problem is a new name for an old problem.  The goal is to
   define a datatype by cases, where one can add new cases to the datatype and
   new functions over the datatype, without recompiling existing code, and while
   retaining static type safety (e.g., no casts).

There are many solutions to the Expression Problem, though a particularly
elegant one is Wouter Swierstra's `Data Types a la Carte
<https://www.cambridge.org/core/journals/journal-of-functional-programming/article/data-types-a-la-carte/14416CB20C4637164EA9F77097909409>`_.
Swierstra's paper is a really beautiful functional pearl and is highly
recommended---it's probably useful background to have before diving into this
chapter, though we'll try to explain everything here as we go. His solution is a
great illustration of extensibility with typeclasses: so, we show how to apply
his approach using typeclasses in F*. More than anything, it's a really fun
example to work out.

Swierstra's paper uses Haskell: so he does not prove his functions terminating.
One could do this in F* too, using the effect of :ref:`divergence <Part4_div>`.
However, in this chapter, we show how to make it all work with total functions
and strictly positive inductive definitions. As a bonus, we also show how to do
proofs of correctness of the various programs that Swierstra develops. 

Getting Started
---------------

To set the stage, consider the following simple type of arithmetic expressions
and a function ``evaluate`` to evaluate an expression to an integer:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: exp$
   :end-before: //SNIPPET_END: exp$

This is straightforward to define, but it has an extensibility problem.

If one wanted to add another type of expression, say ``Mul : exp -> exp ->
exp``, then one needs to redefine both the type ``exp`` adding the new case and
to redefine ``evaluate`` to handle that case.

A solution to the Expression Problem would allow one to add cases to the ``exp``
type and to progressively define functions to handle each case separately.

Swierstra's idea is to define a single generic data type that is parameterized
by a type constructor, allowing one to express, in general, a tree of finite
depth, but one whose branching structure and payload is left generic. A first
attempt at such a definition in F* is shown below:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: expr-fail$
   :end-before: //SNIPPET_END: expr-fail$

Unfortunately, this definition is not accepted by F*, because it is not
necessarily well-founded. As we saw in a previous section on :ref:`strictly
positive definitions <Part2_strictly_positive_annotations>`, if we're not
careful, such definitions can allow one to prove ``False``. In particular, we
need to constrain the type constructor argument ``f`` to be *strictly positive*,
like so:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: expr$
   :end-before: //SNIPPET_END: expr$

This definition may bend your mind a little at first, but it's actually quite
simple. It may help to consider an example: the type ``expr list`` has values of
the form ``In of list (expr list)``, i.e., trees of arbitrary depth with a
variable branching factor such as in the example shown below.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: elist$
   :end-before: //SNIPPET_END: elist$

Now, given two type constructors ``f`` and ``g``, one can take their *sum* or
coproduct. This is analogous to the ``either`` type we saw in :ref:`Part 1
<Part1_ch3>`, but at the level of type constructors rather than types: we write
``f ++ g`` for ``coprod f g``.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: coprod$
   :end-before: //SNIPPET_END: coprod$

Now, with these abstractions in place, we can define the following, where ``expr
(value ++ add)`` is isomorphic to the ``exp`` type we started with. Notice that
we've now defined the cases of our type of arithmetic expressions independently
and can compose the cases with ``++``.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: value add$
   :end-before: //SNIPPET_END: value add$

Of course, building a value of type ``expr (value ++ add)`` is utterly horrible:
but we'll see how to make that better using typeclasses, next .

Smart Constructors with Injections and Projections
--------------------------------------------------

A data constructor, e.g., ``Inl : a -> either a b`` is an injective function
from ``a`` to ``either a b``, i.e., each element ``x:a`` is mapped to a unique
element ``Inl x : either a b``. One can also project back that ``a`` from an
``either a b``, though this is only a partial function. Abstracting injections
and projections will give us a generic way to construct values in our extensible
type of expressions.

First, we define some abbreviations:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: inj_proj$
   :end-before: //SNIPPET_END: inj_proj$

A type constructor ``f`` is less than or equal to another constructor ``g`` if
there is an injection from ``f a`` to ``g a``. This notion is captured by the
typeclass below: We have an ``inj`` and a ``proj`` where ``proj`` is an inverse
of ``inj``, and ``inj`` is a partial inverse of ``proj``.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: leq$
   :end-before: //SNIPPET_END: leq$

We can now define some instances of ``leq``. First, of course, ``leq`` is
reflexive, and F* can easily prove the inversion lemma with SMT.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: leq_refl$
   :end-before: //SNIPPET_END: leq_refl$

More interestingly, we can prove that ``f`` is less than or equal to the
extension of ``f`` with ``g`` on the left:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: leq_ext_left$
   :end-before: //SNIPPET_END: leq_ext_left$

We could also prove the analogous ``leq_ext_right``, but we will explicitly not
give an instance for it, since as we'll see shortly, the instances we give are
specifically chosen to allow type inference to work well. Additional instances
will lead to ambiguities and confuse the inference algorithm.

Instead, we will give a slightly more general form, including  a congruence rule
that says that if ``f`` is less than or equal to ``h``, then ``f`` is also less
than or equal to the extension of ``h`` with ``g`` on the right.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: leq_cong_right$
   :end-before: //SNIPPET_END: leq_cong_right$

Now, for any pair of type constructors that satisfy ``leq f g``, we can lift the
associated injections and projections to our extensible expression datatype and
prove the round-trip lemmas 

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: inject project$
   :end-before: //SNIPPET_END: inject project$

Now, with this machinery in place, we get to the fun part. For each of the cases
of the ``expr`` type, we can define a generic smart constructor, allowing one to
lift it to any type more general than the case we're defining. 

For instance, the smart constructor ``v`` lifts the constructor ``Val x`` into
the type ``expr f`` for any type greater than or equal to ``value``. Likewise,
``(+^)`` lifts ``Add x y`` into any type greater than or equal to ``add``.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: v and +^$
   :end-before: //SNIPPET_END: v and +^$

And now we can write our example value so much more nicely than before:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: ex1$
   :end-before: //SNIPPET_END: ex1$

The type annotation on ``ex1 : expr (value ++ add)`` is crucial: it allows the
type inference algorithm to instantiate the generic parameter ``f`` in each
``v`` and in ``(+^)`` to ``(value ++ add)`` and then the search for typeclass
instances finds ``value `leq` (value ++ add)`` by using ``leq_cong_right`` and
``leq_left``; and  ``add `leq` (value ++ add)`` using ``leq_ext_left``.

With this setup, extensibility works out smoothly: we can add a multiplication
case, define a smart constructor for it, and easily use it to build expressions
with values, addition, and multiplication.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: mul$
   :end-before: //SNIPPET_END: mul$

Evaluating Expressions
----------------------

Now that we have a way to construct expressions, let's see how to define an
interpreter for expressions in an extensible way. An interpreter involves
traversing the expression tree, and applying operations to an accumulated
result, and returning the final accumulated value. In other words, we need a way
to *fold* over an expression tree, but to do so in an extensible, generic way.

The path to doing that involves defining a notion of a functor: we saw functors
briefly in a :ref:`previous section <Part3_monadic_syntax>`, and maybe you're
already familiar with it from Haskell. 

Our definition of functor below is slightly different than what one might
normally see. Usually, a type constructor ``t`` is a functor if it supports an
operation ``fmap: (a -> b) -> t a -> t b``. In our definition below, we flip the
order of arguments and require ``fmap x f`` to guarantee that it calls ``f``
only on subterms of ``x``---this will allow us to build functors over
inductively defined datatypes in an extensible way, while still proving that all
our functions termination.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: functor$
   :end-before: //SNIPPET_END: functor$

Functor instances for ``value``, ``add``, and ``mul`` are easy to define:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: functor_value$
   :end-before: //SNIPPET_END: functor_value$

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: functor_add$
   :end-before: //SNIPPET_END: functor_add$

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: functor_mul$
   :end-before: //SNIPPET_END: functor_mul$

Maybe more interesting is a functor instance for co-products, or sums of
functors, i.e., if ``f`` and ``g`` are both functors, then so is ``f ++ g``.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: functor_coprod$
   :end-before: //SNIPPET_END: functor_coprod$

With this in place, we can finally define a generic way to fold over an
expression. Given a function ``alg`` to map an ``f a`` to a result value ``a``,
``fold_expr`` traverses an ``expr f`` accumulating the results of ``alg``
applied to each node in the tree. Here we see why it was important to refine the
type of ``fmap`` with the precondition ``x << t``: the recursive call to
``fold_expr`` terminates only because the argument ``x`` is guarantee to precede
``t`` in F*'s built-in well-founded order.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: fold_expr$
   :end-before: //SNIPPET_END: fold_expr$

Now that we have a general way to fold over our expression trees, we need an
extensible way to define the evaluators for each type of node in a tree. For
that, we can define another typeclass, ``eval f`` for an evaluator for nodes of
type ``f``. It's easy to give instances of eval for our three types of nodes,
separately from each other.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: eval$
   :end-before: //SNIPPET_END: eval$

With evaluators for ``f`` and ``g``, one can build an evaluator for ``f++g``.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: eval_coprod$
   :end-before: //SNIPPET_END: eval_coprod$

Finally, we can build a generic evaluator for expressions:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: eval_expr$
   :end-before: //SNIPPET_END: eval_expr$

And, hooray, it works! We can ask F* to normalize and check that the result
matches what we expect:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: eval_test$
   :end-before: //SNIPPET_END: eval_test$

Provably Correct Optimizations
------------------------------

Now, let's say we wanted to optimize our expressions, rewriting them by
appealing to the usual arithmetic rules, e.g., distributing multiplication over
addition etc. Swierstra shows how to do that, but in Haskell, there aren't any
proofs of correctness. But, in F*, we can prove our expression rewrite rules
correct, in the sense that they preserve the semantics of expression evaluation.

Let's start by defining the type of a rewrite rule and what it means for it to
be sound:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: rewrite_rule$
   :end-before: //SNIPPET_END: rewrite_rule$

A rewrite rule may fail, but if it rewrites ``x`` to ``y``, then both ``x`` and
``y`` must evaluate to the same result. We can package up a rewrite rule and its
soundness proof into a record, ``rewrite_t``.

Now, to define some rewrite rules, it's convenient to have a bit of syntax to
handle potential rewrite failures---we'll use the monadic syntax :ref:`shown
previously <Part3_monadic_syntax>`.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: error_monad$
   :end-before: //SNIPPET_END: error_monad$

Next, in order to define our rewrite rules for each case, we define what we
expect to be true for the expression evaluator for an expession tree that has
that case.

For instance, if we're evaluating an ``Add`` node, then we expect the result to
the addition of each subtree.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: expected_semantics$
   :end-before: //SNIPPET_END: expected_semantics$

We can now define two example rewrite rules. The first rewrites ``(a * (c +
d))`` to ``(a * c + a * d)``; and the second rewrites ``(c + d) * b`` to ``(c *
b + d * b)``. Both of these are easily proven sound for any type of expression
tree whose nodes ``f`` include ``add`` and ``mul``, under the hypothesis that
the evaluator behaves as expected.

We can generically compose rewrite rules:

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: compose_rewrites$
   :end-before: //SNIPPET_END: compose_rewrites$

Then, given any rewrite rule ``l``, we can fold over the expression applying the
rewrite rule bottom up whenever it is eligible.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: rewrite_expr$
   :end-before: //SNIPPET_END: rewrite_expr$

As with our evaluator, we can test that it works, by asking F* to evaluate the
rewrite rules on an example. We first define ``rewrite_distr`` to apply both
distributivity rewrite rules. And then assert that rewrite ``ex6`` produces
``ex6'``.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: rewrite_test$
   :end-before: //SNIPPET_END: rewrite_test$

Of course, more than just testing it, we can prove that it is correct. In fact,
we can prove that applying any rewrite rule over an entire expression tree
preserves its semantics.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: rewrite_soundness$
   :end-before: //SNIPPET_END: rewrite_soundness$

This is the one part of this development where the definition is not completely
generic in the type of expression nodes. Instead, this is proof for the specific
case of expressions that contain values, additions, and multiplications. I
haven't found a way to make this more generic. One would likely need to define a
generic induction principle similar in structure to ``fold_expr``---but that's
for another day's head scratching. If you know an easy way, please let me know!

That said, the proof is quite straightforward and pleasant: We simply match on
the cases, use the induction hypothesis on the subtrees if any, and then apply
the soundness lemma of the rewrite rule. F* and Z3 automates much of the
reasoning, e.g., in the last case, we know we must have a ``Mul`` node, since
we've already matched the other two cases.

Of course, since rewriting is sound for any rule, it is also sound for rewriting
with our distributivity rules.

.. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
   :language: fstar
   :start-after: //SNIPPET_START: rewrite_distr_soundness$
   :end-before: //SNIPPET_END: rewrite_distr_soundness$

Exercises
---------

This `file <../code/exercises/Part3.DataTypesALaCarte.fst>`_ provides
the definitions you need.

Exercise 1
++++++++++

Write a function ``to_string_specific`` whose type is ``expr (value ++ add ++
mul) -> string`` to print an expression as a string.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
       :language: fstar
       :start-after: //SNIPPET_START: functor$
       :end-before: //SNIPPET_END: functor$

Exercise 2
++++++++++

Next, write a class ``render f`` with a ``to_string`` function to generically
print any expression of type ``expr f``.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
       :language: fstar
       :start-after: //SNIPPET_START: to_string$
       :end-before: //SNIPPET_END: to_string$

Exercise 3
++++++++++

Write a function ``lift`` with the following signature

.. code-block:: fstar

   let lift #f #g
      {| ff: functor f |} 
      {| fg: leq f g |}
      (x: expr f)
   : expr g

Use it to reuse an expression defined for one type to another, so that the
assertion below success

.. code-block:: fstar

   let ex3 : expr (value ++ add ++ mul) = lift addExample *^ v 2
   
   [@@expect_failure]
   let test_e3 = assert_norm (eval_expr ex3 == (1337 * 2))

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part3.DataTypesALaCarte.fst
       :language: fstar
       :start-after: //SNIPPET_START: lift$
       :end-before: //SNIPPET_END: lift$

