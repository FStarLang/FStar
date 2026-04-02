.. _Part4_Div:

Divergence, or Non-Termination
==============================

Most dependently typed languages are not `Turing complete
<https://en.wikipedia.org/wiki/Turing_completeness>`_. This is
because, as explained :ref:`earlier <Part1_termination>`, it is
crucial to the soundness of a type theory to have all functions
terminate. This means that you cannot program, say, an interpreter for
a general-purpose programming language in a language like Coq, since
such an interpreter would not be able to handle programs that
intentionally loop forever. [#]_

F*'s logical core of total (and ghost) functions can only express
terminating computations. However, F*'s also allows expressing
non-terminating or *divergent* computations, relying on the effect
system to isolate divergent computations from the logical core. In
particular, the computation type ``Dv t`` describes a computation that
may loop forever, but if it completes, it returns a value of type
``t``.

Relying on the effect system as a dependency tracking mechanism, F*
ensures that ``Tot`` computations cannot rely on ``Dv`` computations
by placing ``Dv`` above ``Tot`` in the effect hierarchy, while,
conversely, a total computation ``Tot t`` can be silently promoted to
``Dv t``, the type of computations that may not terminate, i.e., ``Tot
< Dv`` in the effect partial order.

Recursive functions that return computations in the ``Dv`` effect are
not checked for termination.  As such, using the ``Dv`` effect, one
can write programs such as the one below, which computes `Collatz
sequences
<https://en.wikipedia.org/wiki/Collatz_conjecture>`_---whether or not
this program terminates for all inputs is an open problem.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: collatz$
   :end-before: //SNIPPET_END: collatz$

In this chapter, we'll look in detail at the ``Dv`` effect and how it
interacts with other features of the language, including the other
effects, recursive type definitions, and the styles of programming and
proving it enables.

.. [#] In place of general recursion and potential non-termination,
       other dependently typed languages like Coq and Agda offer
       features like corecursion and coinduction. Coinduction can be
       used to express a class of *productive* non-terminating
       programs. For instance, using coinduction, one could program a
       web server that loops forever to handle an infinite stream of
       requests, while producing a response for each request in a
       finite amount of time. Even the ``collatz`` function can be
       given a corecursive definition that computes a potentially
       infinite stream of numbers. However, not all non-terminating
       computations can be implemented with
       coinduction/corecursion. F* does not yet support coinduction.
       

The ``Dv`` effect
^^^^^^^^^^^^^^^^^^^

The effect ``Dv`` (for divergence) is a primitive effect in F*.
Computations in ``Dv`` may not terminate, even with infinite
resources. In other words, computations in the ``Dv`` effect have the
observational behavior of non-termination. For example, the following
``loop`` function has type ``unit -> Dv unit`` and it always diverges
when called:

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: loop$
   :end-before: //SNIPPET_END: loop$

If we remove the ``Dv`` effect label annotation, then F* treats the
function as total and will try to prove that the recursive call
terminates, according to its usual termination checking rules, i.e.,
F* will attempt to prove ``() << ()`` which fails, as expected.

Since the ``Dv`` effect admits divergence, F* essentially turns-off
the termination checker when typechecking ``Dv`` computations. So the
recursive ``loop ()`` call does not require a decreasing termination
metric.

Partial correctness semantics of ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``Tot`` effect in F* has a *total correctness* semantics. That is,
if a term has type ``e:Tot t``, then ``e`` terminates terminates and
produces a value of type ``t``.

Terms with type ``Dv t`` have a *partial correctness* semantics. That
is, a term ``e:Dv t``, ``e`` may either run forever, but if it
terminates then the resulting value has type ``t``.

Another perspective is that aside from disabling the termination
checking features of F*, all other type-checking constraints are
enforced on ``Dv`` term. This means that one can still give
interesting sound, specifications to ``Dv`` programs, e.g., the type
below proves that if the Collatz function terminates, then the last
element of the sequence is ``1``.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: collatz_ends_in_one$
   :end-before: //SNIPPET_END: collatz_ends_in_one$

If, for example, in the base case we were to return the empty list
``[]`` rather than ``[n]``, then F* would refuse to accept the
program, since the program could terminate while returning a value
that is not an element of the annotated return type.

Isolating ``Dv`` from the logical core
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Since ``Dv`` terms need not terminate, a program that always loops
forever can be given any return type. For instance, the program below
has return type ``False``:

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: loop_false$
   :end-before: //SNIPPET_END: loop_false$

Importantly, a term of type ``Dv False`` should not be confused as a
*proof* of ``False``, since that would lead immediately to unsoundness
of F*'s logical core. In particular, it should be impossible to turn a
``e:Dv t`` into a term of type ``Tot t``. This is achieved by F*'s
effect system, which treats ``Tot`` as a sub-effect of ``Dv``, i.e.,
``Tot < Dv``, in the effect order. As explained in :ref:`earlier
<Part4_Background>`, this ensures that no ``Tot`` term can depend on a
``Dv`` term, maintaining soundness of the total correctness
interpretation of ``Tot``.

As an example, the following attempt to "cast" ``dv_false`` to ``Tot``
fails, as does trying to use ``dv_false`` to produce incorrect proofs
of other types.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: loop_false_failures$
   :end-before: //SNIPPET_END: loop_false_failures$


While F* does not allow ``Tot`` computations to depend on ``Dv``
computations, going the other way is perfectly fine. Intuitively,
always terminating computations are potentially non-terminating. We
can think of it like a *weakening* of the specification:

.. code-block:: fstar
                
   let add_one (x:int) : int = x + 1
   let add_one_div (x:int) : Dv int = add_one x

The effect system of F* automatically *lifts* ``Tot`` computations
into ``Dv``, meaning that ``Tot`` functions can be seamlessly used in
``Dv`` functions.

The weakening of ``Tot`` terms to other effects is so pervasive in F*
that one hardly even thinks about it, e.g., in the ``collatz``
program, sub-terms like ``n / 2`` are in ``Tot`` but are easily used
within a computation in the ``Dv`` effect.
   
No extrinsic proofs for ``Dv`` computations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

One important consequence of any effectful code, including ``Dv``,
being outside the logical core of F* is that it is not possible to do
:ref:`extrinsic proofs <Part1_intrinsic_extrinsic>` about effectful
code. One cannot even state properties of ``Dv`` computations in
specifications, since even specifications must be total. For example,
even stating the following lemma is illegal:

.. code-block:: fstar

   [@@expect_failure]
   val collatz_property (n:pos)
     : Lemma (Cons? (collatz n) /\ last (collatz n) = 1)

This is nonsensical in F* since writing ``Cons? (collatz n)`` supposes
that ``collatz n`` is *defined*, whereas it might actually just loop
forever.

The only way to state properties about divergent programs is to encode
the property intrinsically in the computation type, as we saw above.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: val collatz_ends_in_one$
   :end-before: //SNIPPET_END: val collatz_ends_in_one$

Exercise
++++++++

Define a predicate ``collatz_spec (n:pos) (l:list pos) : bool`` that
decides if ``l`` is a valid Collatz sequence starting at ``n``.

Implement ``val collatz' (n:pos) : Dv (l:list pos { collatz_spec n l })``.

What does this type mean? Are there other ways to implement
``collatz'`` with the same type?


.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Divergence.fst
       :language: fstar
       :start-after: //SNIPPET_START: collatz_spec$
       :end-before: //SNIPPET_END: collatz_spec$

--------------------------------------------------------------------------------

General Recursive Types and Impredicativity with ``Dv``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Aside from disabling the decreases metric on recursive functions in
``Dv``, F* also disables two other forms of termination checking on
``Dv`` computations.

Recall from a :ref:`previous chapter <Part2_strict_positivity>` that
inductive type definitions are subject to the *strict positivity*
condition, since non-positive definitions allow the definition of
recursive types and non-terminating computations. However, since
computations in the ``Dv`` effect are already allowed to loop forever,
the strict positivity condition can be relaxed when ``Dv`` types are
involved. For example, one can define this:

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: nonpos$
   :end-before: //SNIPPET_END: nonpos$

The type ``nonpos`` is not strictly positive, since it appears to the
left of an arrow in a field of one of its constructors. Indeed, usingn
``nonpos`` it is possible to define (without using ``let rec``) an
infinitely looping program ``loop_nonpos()``---however, the type ``Dv
False`` tells us that this program may loop forever, and the infinite
loop is safely isolated from F*'s logical core.

The other place in F*'s type system where termination checking comes
into play is in the :ref:`universe levels <Part2_universes>`. As we
learned previously, the logical core of F* is organized into an
infinite hierarchy with copies of the F* type system arranged in a
tower of universes. This stratification is necessary to prevent
inconsistencies within the logical core. However, terms in the ``Dv``
effect are outside the logical core and, as such, restrictions on the
universe levels no longer apply. As the snippet below shows a total
function returning a type in universe ``u#a`` resides in universe
``u#(a + 1)``. However, a ``Dv`` function returning a type in ``u#a``
is just in universe ``0``, since the only way to obtain the type
``dv_type`` returns is by incurring a ``Dv`` effect and moving outside
F*'s logical core.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: universe_dv$
   :end-before: //SNIPPET_END: universe_dv$

Top-level Effects
^^^^^^^^^^^^^^^^^

A top-level F* term is not meant to be effectful. If one defines the
following term, F* accepts the term but raises a warning saying
"Top-level let bindings must be total---this term may have effects".

.. code-block:: fstar

   let inconsistent : False = loop_nonpos()                

Top-level effects can be problematic for a few reasons:

  1. The order of evaluation of the effects in top-level terms is
     undefined for programs with multiple modules---it depends on the
     order in which modules are loaded at runtime.

  2. Top-level effects, particularly when divergence is involved, can
     render F*'s typechecking context inconsistent. For example, once
     ``inconsistent`` is defined, then any other assertion can be
     proven.

     .. code-block :: fstar

         let _  = let _ = FStar.Squash.return_squash inconsistent in
                  assert false

Nevertheless, when used carefully, top-level effects can be useful,
e.g., to initialize the state of a module, or to start the main
function of a program. So, pay attention to the warning F* raises when
you have a top-level effect and make sure you really know what you're
doing.

Example: Untyped Lambda Calculus
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In this section, we put together the various things we've learned
about ``Dv`` computations to define several variants of an untyped
lambda calculus.

You can refer back to our prior development of the :ref:`simply typed
lambda calculus <Part2_stlc>` if you need some basic background on the
lambda calculus.

Interpreting Deeply Embedded Lambda Terms
+++++++++++++++++++++++++++++++++++++++++

We start by defining the syntax of untyped lambda terms, below.  The
variables use the de Bruijn convention, where a index of a variable
counts the number of lambda-binders to traverse to reach its binding
occurrence. The ``Lam`` case just has the body of the lambda term,
with no type annotation on the binder, and no explicit name for the
variable.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: deep_embedding_syntax$
   :end-before: //SNIPPET_END: deep_embedding_syntax$

As usual, we can define what it means to substitute a variable ``x``
with a (closed) term ``v`` in ``t``---this is just a regular ``Tot``
function.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: deep_embedding_subst$
   :end-before: //SNIPPET_END: deep_embedding_subst$

Finally, we can define an interpreter for ``term``, which can
(intentionally) loop infinitely, as is clear from the ``Dv`` type
annotation.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: deep_embedding_interpreter$
   :end-before: //SNIPPET_END: deep_embedding_interpreter$
                
Exercise
........

This exercise is designed to show how you can prove non-trivial
properties of ``Dv`` computations by giving them interesting dependent
types.

The substitution function defined here is only sound when the term
being substituted is closed, otherwise, any free variables it has can
be captured when substituted beneath a lambda.

A term is closed if it satisfies this definition:

.. literalinclude:: ../code/Part4.UTLCEx1.fst
   :language: fstar
   :start-after: //SNIPPET_START: closed$
   :end-before: //SNIPPET_END: closed$

Restrict the type of ``subst`` so that its argument is ``v : term {
closed v }``---you will have to also revise the type of its other
argument for the proof to work.

Next, give the following type to the interpreter itself, proving that
interpreting closed terms produces closed terms, or loops forever.

.. literalinclude:: ../code/Part4.UTLCEx1.fst
   :language: fstar
   :start-after: //SNIPPET_START: interpret$
   :end-before: //SNIPPET_END: interpret$

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part4.UTLCEx1.fst
       :language: fstar

--------------------------------------------------------------------------------


Denoting Lambda Terms into an F* Recursive Type
+++++++++++++++++++++++++++++++++++++++++++++++

We now look at a variation on the interpreter above to illustrate how
(non-positive) recursive types using ``Dv`` can also be used to give a
semantics to untyped lambda terms.

Consider the type ``dyn`` shown below---it has a non-positive
constructor ``DFun``. We can use this type to interpret untyped lambda
terms into dynamically typed, potentially divergent, F* terms,
showing, in a way, that untyped lambda calculus is no more expressive
than F* with the ``Dv`` effect.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: dyn$
   :end-before: //SNIPPET_END: dyn$

The program ``denote`` shown below gives a semantics to ``term`` using
``dyn``. It is parameterized by a ``ctx : ctx_t``, which interprets
the free variables of the term into ``dyn``. 

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: denote$
   :end-before: //SNIPPET_END: denote$

We look at the cases in detail:

  * In the ``Var`` case, the intepretation just refers to the context.

  * Integers constants in ``term`` are directly interpreted to
    integers in ``dyn``.

  * The case of ``Lam`` is the most interesting: An lambda abstraction
    in ``term`` is interpreted as an F* function ``dyn -> Dv dyn``,
    recursively calling the denotation function on the body when the
    function is applied. Here's where we see the non-positivity of
    ``DFun`` at play---it allows us to inject the function into the
    ``dyn`` type.

  * Finally, in the application case, we interpret a syntactic
    application in ``term`` as function application in F* (unless the
    head is not a function, in which case we have a type error).

Exercise
........

This exercise is similar in spirit to the previous one and designed to
show that you can prove some simple properties of ``denote`` by
enriching its type.

Can you prove that a closed term can be interpreted in an empty
context?

First, let's refine the type of contexts so that it only provides an
interpretation to only some variables:

.. literalinclude:: ../code/Part4.UTLCEx2.fst
   :language: fstar
   :start-after: //SNIPPET_START: ctx_t$
   :end-before: //SNIPPET_END: ctx_t$

Next, let's define ``free t`` to compute the greatest index of a free
variable in a term.

.. literalinclude:: ../code/Part4.UTLCEx2.fst
   :language: fstar
   :start-after: //SNIPPET_START: free$
   :end-before: //SNIPPET_END: free$

Can you give the same ``denote`` function shown earlier the following
type?

.. code-block:: fstar

   val denote (t:term) (ctx:ctx_t (free t))
     : Dv dyn  

Next, define the empty context as shown below:

.. literalinclude:: ../code/Part4.UTLCEx2.fst
   :language: fstar
   :start-after: //SNIPPET_START: empty_context$
   :end-before: //SNIPPET_END: empty_context$

Given a closed term ``t : term { closed t }``, where ``closed t =
(free t = -1)``, can you use ``denote`` to give an interpretation to
closed terms in the empty context?
                

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part4.UTLCEx2.fst
       :language: fstar

--------------------------------------------------------------------------------

Shallowly Embedded Dynamically Typed Programming
++++++++++++++++++++++++++++++++++++++++++++++++

In the previous example, we saw how the syntax of untyped lambda terms
can be interpreted into the F* type ``dyn``. In this example, rather
than going via the indirection of the syntax of lambda terms, we show
how the type ``dyn`` can be used directly to embed within F* a small
Turing complete, dynamically typed programming language.

We can start by lifting the F* operations on integers and functions to
(possibly failing) operations on ``dyn``.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: lift_int$
   :end-before: //SNIPPET_END: lift_int$

We also encode provide operations to compare dyn-typed integers and to
branch on them, treating ``0`` as ``false``.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: branch_eq$
   :end-before: //SNIPPET_END: branch_eq$

For functions, we can provide combinators to apply functions and,
importantly, a combinator ``fix`` that provides general recursion.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: app_fix$
   :end-before: //SNIPPET_END: app_fix$

An aside on the arity of recursive functions: You may wonder why
``fix`` is defined as shown, rather than ``fix_alt`` below, which
removes a needless additional abstraction. The reason is that with
``fix_alt``, to instruct F* to disable the termination checker on the
recursive definition, we need an additional ``Dv`` annotation: indeed,
evaluating ``fixalt f`` in a call-by-value semantics would result,
unconditionally, in an infinite loop, whereas ``fix f`` would
immediately return the lambda term ``fun n -> f (fix f) n``. In other
words, eta reduction (or removing redundant function applications)
does not preserve semantics in the presence of divergence.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: fix_alt$
   :end-before: //SNIPPET_END: fix_alt$
                
With that, we can program non-trivial dynamically typed, general
recursive programs within F* itself, as seen below.

.. literalinclude:: ../code/Divergence.fst
   :language: fstar
   :start-after: //SNIPPET_START: collatz_dyn$
   :end-before: //SNIPPET_END: collatz_dyn$

All of which is to illustrate that with general recursion and
non-positive datatypes using ``Dv``, F* is a general-purpose
programming language like ML, Haskell, Lisp, or Scheme, or other
functional languages you may be familiar with. 


