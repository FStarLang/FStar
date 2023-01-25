.. _Part4_Pure:

Primitive Effect Refinements
==============================

.. note:: 

   This chapter provides some background on Floyd-Hoare logic and
   weakest-precondition-based verification condition generation. This
   is necessary if you want to understand a bit about how F* infers
   the logical constraints needed to prove the correctness of a
   program. It is also useful background for more advanced material in
   subsequent chapters about defining custom effects in F*, e.g.,
   effects to model state, exceptions, or concurrency.

Refinement types ``x:t{p}`` *refine* value types ``t`` and allow us to
make more precise assertions about the values in the program. For
example, when we have ``v : x:int{x >= 0}``, then not only we know
that ``v`` is an ``int``, but also that ``v >= 0``.

In a similar manner, F* allows refining computation types with
specifications that describe some aspects of a program's computational
behavior. These *effect refinements* can, in general, be defined by
the user in a reasoning system of their chosing, e.g., the refinements
may use separation logic, or they may count computation steps.

However, F* has built-in support for refining the specification of
pure programs with effect refinements that encode the standard
reasoning principles of Floyd-Hoare Logic and weakest
precondition-based calculi. Foreshadowing what's about to come in this
chapter, we can write the following specification for the
``factorial`` function:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial$
   :end-before: //SNIPPET_END: factorial$
                
Intuitively, this type states that ``factorial x`` is a computation
defined only when ``x >= 0`` and always terminates returning a value
``r >= 1``. In a way, this type is closely related to other, more
familiar, types we have given to ``factorial`` so far, e.g., ``nat ->
pos``, and, indeed, ``factorial`` can be used at this type.

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: fact$
   :end-before: //SNIPPET_END: fact$

Actually, in all the code we've seen so far, what's happening under
the covers is that F* infers a type for a pure program similar to
``Pure t pre post`` and then checks that that type can be subsumed to
user-provided specification of the form ``Tot t'``.

In this chapter, we look into how these ``Pure`` specifications work,
starting with a primer on Floyd-Hoare Logic and weakest precondition
calculi. If the reader is familiar with these, they may safely skip
the next subsections.


A Primer on Floyd-Hoare Logic and WP-calculi
--------------------------------------------

Floyd-Hoare Logic is a system of specifications and reasoning
principles to reason about the logical properties of programs.  The
ideas were introduced by Robert Floyd in a paper titled `Assigning
Meaning to Programs
<https://link.springer.com/chapter/10.1007/978-94-011-1793-7_4>`_ and
by Tony Hoare in `An axiomatic basis for computer programming
<https://dl.acm.org/doi/10.1145/363235.363259>`_. The notation used in
most modern presentations (called Hoare triples) is due to Hoare.

Let's consider a small imperative language with the following grammar.

.. code-block:: none

   Expression e ::= x | ...

   Statement s ::= skip | x := e | s1; s2 | if e then s1 else s2 | while e s

The language consists of expressions ``e``, which include global
variables ``x, y, z, ...``.  We leave the rest of the expression forms
unspecified, as the core reasoning rules are agnostic to them, e.g.,
they may include arithmetic expressions. The statements ``s`` consist
of ``skip`` (a no-op), assignment, sequencing, conditionals, and while
loops with guard ``e`` and loop body ``s``.

Floyd-Hoare Logic provides a reasoning system for such a language,
sometimes called its *axiomatic semantics*. The unit of reasoning is a
*Hoare triple* of the form ``{P} s {Q}``, where ``P`` and ``Q`` are
assertions (logical formulas) about the state of the program. In its
simplest form, program state is just a mapping of variables to values.

A Hoare triple ``{P} s {Q}`` is valid, if executing ``s`` in a state
that satisfies ``P`` results in a state that satisfies ``Q``. ``P``
and ``Q`` are also called precondition and postcondition of ``s``,
respectively. There are both total correctness and partial correctness
interpretations of the triple, depending on whether the termination of
``s`` is ensured by the logical rules that manipulate the triples.

Inference rules provide axioms for valid Hoare triples for each of the
statement forms, reflecting their logical reasoning principles. A
triple ``{P} s {Q}`` is *derivable* in the system if these axioms can
be instantiated and arranged together in a *derivation tree* with
``{P} s {Q}`` at the root. We first look at each individual axiom, and
then examples of such derivation trees.


Skip
^^^^

The inference rule for ``skip`` is as shown below.

.. code-block:: none
                
  ---------------- :: [Skip]
    {P} skip {P}


Inference rules are a general technique of specifying a reasoning
system. An inference rule has two parts, premises and a conclusion,
separated by a horizontal line. The interpretation of an inference
rule is that, given the premises, the rule can be applied to derive
the conclusion. An inference rule may optionally be named, the ``::
[Skip]`` part here.

The ``[Skip]`` rule has no premises, meaning that it can be applied
unconditionally, and the conclusion says that the triple ``{P} skip
{P}`` is valid for all ``P`` (*meta variables* that denote assertions,
statements, variables, etc., are implicitly universally
quantified). Intuitively this reflects the no-op semantics of
``skip``: for any assertion ``P``, if ``P`` holds for the current
state, then it also holds after executing ``skip``, since ``skip``
does not change the state.

Assignment
^^^^^^^^^^^^

The assignment rule is a little more interesting.

.. code-block:: none

  ----------------------- :: [Assign]
    {P[e/x]} x := e {P}


This rule also does not have any premises. It says that, ``P`` holds
after
executing ``x := e``, if ``P[e/x]``, i.e. ``P`` with ``x`` substituted
by ``e``, holds before executing the statement.

For example, to prove that after ``z := y + 1``, ``z >
0`` holds, the rule says that ``(z > 0)[(y + 1)/z]`` should hold
before the assigment. That is ``y + 1 > 0`` or ``y > -1``, which is
what we would expect. So, applying this rule, with instantiations of
the metavariables ``P``, ``x``, and ``e``, we
can derive that the Hoare triple ``{y > -1} x := y + 1 {x > 0}`` is
valid.


Sequence
^^^^^^^^^^^^

The sequencing rule stitches together triples for the two statements:

.. code-block:: none

  {P} s1 {R}    {R} s2 {Q}
  ------------------------- :: [Seq]
    {P} s1; s2 {Q}


The rule has two premises. It says that, if we can derive the Hoare
triples of the two statements such that postcondition of ``s1``
matches the precondition of ``s2``, then we can derive the Hoare
triple for ``s1; s2`` as written in the conclusion.
    

Conditional
^^^^^^^^^^^^^

The rule for conditionals is as follows:

.. code-block:: none

  {P /\ e} s1 {Q}    {P /\ ~e} s2 {Q}
  ------------------------------------- :: [If]
     {P} if e then s1 else s2 {Q}

The rule says that to derive the postcondition ``Q``
from the conditional statement, we should be able to derive it from
each of the branch. In addition, since we know that ``s1`` executes
only when ``e`` is true, ``e`` can be added to the precondition of
``s1``, and similarly for ``s2``.


While
^^^^^^^^

The rule for ``while`` requires a *loop invariant*:

.. code-block:: none


  {I /\ e} s {I}
  ------------------------ :: [While]
  {I} while e s {I /\ ~e}


The loop invariant ``I`` is an assertion that holds before the loop
starts, is maintained by each iteration of the loop, and is provided
as the postcondition of the loop. While the rule uses the loop
invariant *declaratively*, without worrying about where the invariant
comes from, an actual tool that implements Hoare Logic has to either
infer or require it as an annotation from the user.

This rule establishes partial correctness, it does not ensure that
the loop terminates. It may be augmented with a
termination metric to ensure total correctness, see `here
<https://en.wikipedia.org/wiki/Hoare_logic/>`_ for example.

Consequence
^^^^^^^^^^^^^^

The final inference rule is the rule of consequence that allows
strengthening the precondition and weakening the postcondition:

.. code-block:: none


  P ==> P1    {P1} s {Q1}    Q1 ==> Q
  ------------------------------------- :: [Cons]
              {P} s {Q}      

One way to think of the precondition of a statement is as an
obligation before the statement is executed. So if ``s`` requires
``P1``, we can always strengthen the precondition to ``P``, provided
``P ==> P1``, i.e. it is logically valid to require more than
necessary in the precondition. Similarly, postcondition is what a
statement guarantees. So if ``s`` guarantees ``Q1``, we can always
weaken it to guarantee less, i.e. some ``Q`` where ``Q1 ==> Q``.

Derivation trees
^^^^^^^^^^^^^^^^^^

We can now try to construct some derivation trees. Suppose we want to
derive the triple ``{y > 3} x := y + 1; z := x + 1 {z > 2}``. Using
two applications of the assignment rule, we can derive ``{y > 3} x :=
y + 1 {x > 4}`` and ``{x > 1} z := x + 1 {z > 2}``. But to combine
these using the sequencing rule, we need to match the postcondition of
the first assignment with the precondition of the second
assignment. We can do that by weakening the postcondition of the
first assignment, using the rule of consequence, resulting in the
following derivation. Here each of the dashed line represents
instantiation of one of the rules above:

.. code-block:: none

                    ------------------------------ [Assign]
   y > 3 ==> y > 3    {y > 3} x := y + 1 {x > 4}    x > 4 ==> x > 1
   ----------------------------------------------------------------- [Cons]    --------------------------- [Assign]
                      {y > 3} x:= y + 1 {x > 1}                                 {x > 1} z := x + 1 {z > 2}
                      -------------------------------------------------------------------------------------------- [Seq]
                                   {y > 3} x := y + 1; z := x + 1 {z > 2}


   
There may be multiple derivations possible for the same Hoare
triple. For example, another way to combine the two assignments in the
example above would be to strengthen the precondition of the second
assignment. This source of non-determinism comes from the *non syntax
directed* rule of consequence. For every other rule, the shape of the
conclusion uniquely determines when the rule may be applied. For
example, the assignment rule is only applicable for statements of the
form ``x := e``. Whereas the rule of consequence may be
non-deterministically applied anywhere.

Weakest Precondition Calculus
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A closely related reasoning system based on *weakest preconditions*
was given by `Edsger W. Dijkstra
<https://www.cs.utexas.edu/users/EWD/ewd04xx/EWD472.PDF>`_. While
Hoare Logic is declarative and defines a set of non syntax-directed
inference rules, weakest precondition calculus takes a more
*algorithmic* approach, and defines a function ``WP (s, Q)``, that
computes a unique, weakest precondition ``P`` for the statement ``s``
and postcondition ``Q``. The semantics of ``WP`` is that ``WP (s, Q)``
is the weakest precondition that should hold before executing ``s``
for the postcondition ``Q`` to be valid after executing ``s``. Thus,
the weakest precondition calculus assigns meaning to programs as a
transformer of postconditions ``Q`` to preconditions ``WP (s, Q)``.

The ``WP`` function is defined as follows for our imperative
language:

.. code-block:: none

  WP (skip,   Q)               = Q
  WP (x := e, Q)               = Q[e/x]
  WP (s1; s2, Q)               = WP (s1, WP (s2, Q))
  WP (if e then s1 else e2, Q) = (e ==> WP (s1, Q)) /\ (~e ==> WP (s2, Q))
  WP (while e s, Q)            = I /\ ((I /\ e) ==> WP (s, I)) /\ ((I /\ ~e) ==> Q)

The ``while`` rule uses ``I``, the loop invariant as we introduced in
the Hoare Logic. Since it does not ensure termination, the rules
presented here are for partial correctness. The ``WP`` function for
partial correctness is also known as *weakest liberal
precondition*.

Revisiting our example from the previous chapter, we have ``WP
(x := y + 1; z := x + 1, z > 2) = y > 0``. Thus ``y > 0`` is the
weakest precondition for the command to end up in a state with ``z >
2``.

The following propositions relate the Hoare triples and ``WP``:

* ``{WP (s, Q)} s {Q}`` is a valid Hoare triple.
* If ``{P} s {Q}`` then ``P ==> WP (s, Q)``.

With this background on Floyd-Hoare Logic and weakest preconditions,
we now return to F* and its support for a similar reasoning style.

  
The ``PURE`` Effect: A Dijkstra Monad for Pure Computations
------------------------------------------------------------

F* provides a weakest precondition calculus for reasoning about pure
computations. The calculus is based on a *Dijkstra Monad*, a
construction first introduced in `this paper
<https://www.microsoft.com/en-us/research/publication/verifying-higher-order-programs-with-the-dijkstra-monad/>`_. In
this chapter, we will learn about Dijkstra Monad and its usage in
specifying and proving pure programs in F*.

Let's begin by adapting the weakest precondition calculus from the
previous section to a functional language rather than a language with
global, mutable variables:

.. code-block:: none

  Expression e ::= x | c | let x = e1 in e2 | if e then e1 else e2

For this language, the postcondition that we may want to prove about
an expression ``e`` is a predicate on the result of computing ``e``,
while the precondition is simply a proposition. Adapting the ``WP``
function from the imperative setting to this is straightforward, where
``WP`` is a function, applied to an expression ``e`` that returns a
value of type ``t``, and a predicate ``Q`` on that returned value (a
postcondition), computes a precondition.

.. code-block:: none

  WP c Q                      = Q c 
  WP x Q                      = Q x
  WP (let x = e1 in e2) Q     = WP e1 (fun x -> WP e2 Q)
  WP (if e then e1 else e2) Q = (e ==> WP e1 Q) /\ (~e ==> WP e2 Q)

The F* type system internalizes and generalizes this WP construction
to apply it to all F* terms, rather than just to this small expression
language shown here. The form this takes is as a computation type in
F*: ``PURE a wp``, where in ``prims.fst``, ``PURE`` is defined as an
F* primitive effect with a signature as shown below--we'll see much
more of the ``new_effect`` syntax as we look at user-defined effects
in subsequent chapters; for now, just see it as a reserved syntax in
F* to introduce a computation type constructor.

.. code-block:: fstar

   new_effect PURE (a:Type) (w:wp a) { ... }

where

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: wp$
   :end-before: //SNIPPET_END: wp$                 

A program ``e`` of type ``PURE a wp`` is a computation which

  * Is defined only when ``wp (fun _ -> True)`` is valid

  * If ``wp post`` is valid, then ``e`` terminates without any side
    effects and returns a value ``v:a`` satisfying ``post v``.
    
Notice that ``wp a`` is the type of a function transforming
postconditions (``a -> Type0``) to preconditions (``Type0``). [#]_ The
``wp`` argument is also called an *index* of the ``PURE`` effect.
   
It turns out that ``wp a`` is a also monad. :ref:`Recall
<Part2_monad_intro>` that a monad consists of a type operator
(``wp``), a return, and bind operator, together satisfying some laws. [#]_

The return operator for ``wp a`` is shown below: it is analogous to
the ``WP c Q`` and ``WP x Q`` rules for variables and constants that
we showed earlier:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: return_wp$
   :end-before: //SNIPPET_END: return_wp$                 
                
The bind operator for ``wp a`` is analogous to the rule for sequencing
WPs, i.e., the rule for ``WP (let x = e1 in e2) Q`` above:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: bind_wp$
   :end-before: //SNIPPET_END: bind_wp$                 

Finally, analogous to the WP rule for conditionals, one can write a
combinator for composing ``wp a`` in a branch:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: if_then_else_wp$
   :end-before: //SNIPPET_END: if_then_else_wp$                 


This is the essence of the Dijkstra monad construction for pure
programs: the rule for computing weakest preconditions for a
computation *returning* a value ``x`` is ``return_wp``; the rule for
computing the WP of the sequential composition of terms is the
sequential composition of WPs using ``bind_wp``; the rule for
computing the WP of a conditional term is the conditional composition
of WPs using ``if_then_else_wp``.

If fact, if one thinks of pure computations as the identity monad,
``tot a`` as shown below:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: tot$
   :end-before: //SNIPPET_END: tot$                 

then the parallel between the ``tot`` monad and ``wp`` becomes even
clearer---the WP analog of ``return_tot`` is ``return_wp`` and of
``bind_tot`` is ``bind_wp``.

It turns out that ``wp a`` (for monotonic weakest preconditions) is
itself a monad, as shown below by a proof of the monad laws:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: mwp_laws$
   :end-before: //SNIPPET_END: mwp_laws$                 


.. [#] It is also possible to define ``post a = a -> prop`` and ``pre
       = prop``. However, the F* libraries for pure WPs using
       ``Type0`` instead of ``prop``, so we remain faithful to that
       here.
                
.. [#] Dijkstra monads are also related to the continuation
       monad. Continuation monad models `Continuation Passing Style
       <https://en.wikipedia.org/wiki/Continuation-passing_style/>`_
       programming, where the control is passed to the callee
       explicitly in the form of a continuation. For a result type
       ``r``, the continuation monad is defined as follows:

       .. literalinclude:: ../code/Pure.fst
          :language: fstar
          :start-after: //SNIPPET_START: cont$
          :end-before: //SNIPPET_END: cont$                 

       If we squint a bit, we can see that the ``wp`` monad we defined
       earlier, is nothing but a continuation into ``Type0``, i.e.,
       ``wp a = cont Type0 a`` (or ``cont prop a``, if one prefers to
       use ``prop``).
                
``PURE`` and ``Tot``
---------------------

When typechecking a program, F* computes a weakest precondition which
characterizes a necessary condition for the program to satisfy all its
typing constraints. This computed weakest precondition is usually
hidden from the programmer, but if you annotate your program suitably,
you can get access to it, as shown in the code snippet below:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: square$
   :end-before: //SNIPPET_END: square$

The type says that ``square n`` is a pure function, which for any
postcondition ``q:nat -> prop``,

  * Is defined only when ``n * n >= 0`` and when ``q (n * n)`` is valid
    
  * And returns a value ``m:nat`` satisfying ``q m``

Let's look at another example:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: maybe_incr$
   :end-before: //SNIPPET_END: maybe_incr$

Notice how the ``wp`` index of ``PURE`` mirrors the structure of the
computation itself---it starts with an ``if_then_else_wp``, then in
the first branch, uses a ``bind_wp`` followed by a return; and in the
else branch it returns ``x``.

As such, the wp-index simply "lifts" the computation into a
specification in a form amenable to logical reasoning, e.g., using the
SMT solver. For pure programs this may seem like overkill, since the
pure term itself can be reasoned about directly, but when the term
contains non-trivial typing constraints, e.g., such as those that
arise from refinement type checking, lifting the entire program into a
single constraint structures and simplifies logical reasoning.

Of course, one often writes specifications that are more abstract than
the full logical lifting of the program, as in the example below,
which says that to prove ``post`` of the return value, the
precondition is to prove ``post`` on all ``y >= x``. This is a
valid, although weaker, characterization of the function's return
value.

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: maybe_incr2$
   :end-before: //SNIPPET_END: maybe_incr2$

The ``PURE`` computation type comes with a built-in weakening rule. In
particular, if a term is computed to have type ``PURE a wp_a`` and it is
annotated to have type ``PURE b wp_b``, then F* does the following:

  1. It computes a constraint ``p : a -> Type0``, which is sufficient
     to prove that ``a`` is a subtype of ``b``, e.g., is ``a = int``
     and ``b = nat``, the constraint ``P`` is ``fun (x:int) -> x >=
     0``.

  2. Next, it strengthens ``wp_a`` to assert that the returned value
     validates the subtyping constraints ``p x``, i.e., it builds
     ``assert_wp wp_a p``, where

     .. literalinclude:: ../code/Pure.fst
        :language: fstar
        :start-after: //SNIPPET_START: assert_wp$
        :end-before: //SNIPPET_END: assert_wp$

  3. Finally, it produces the verification condition ``stronger_wp #b
     wp_b (assert_wp wp_a p)``, where ``stronger_wp`` is defined as
     shown below:

     .. literalinclude:: ../code/Pure.fst
        :language: fstar
        :start-after: //SNIPPET_START: stronger_wp$
        :end-before: //SNIPPET_END: stronger_wp$
     
     That is, for any postcondition ``post``, the precondition ``wp_b
     post`` implies the original precondition ``wp_a post`` as well as
     the subtyping constraint ``p x``. This matches the intuition
     about preconditions that we built earlier: it is always sound to
     require more in the precondition.

Thus, when we have ``e:PURE a wp`` in F*, the ``wp`` is *a* predicate
transformer for ``e``, not necessarily the weakest one.

Of course, even ``maybe_incr2`` is not particularly idiomatic in
F*. One would usually annotate a program with a refinement type, such
as the one below:

.. literalinclude:: ../code/Pure.fst
   :language: fstar
   :start-after: //SNIPPET_START: maybe_incr_tot$
   :end-before: //SNIPPET_END: maybe_incr_tot$

Internally to the compiler, F* treats ``Tot t`` as the following
instance of ``PURE``:

.. code-block:: fstar

   Tot t = PURE t (fun post -> forall (x:t). post x)                 

Once ``Tot t`` is viewed as just an instance of ``PURE``, checking if
a user annotation ``Tot t`` is stronger than the inferred
specification of a term ``PURE a wp`` is just as explained before.

``Pure``: Hoare Triples for ``PURE``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Although specification are easier to *compute* using WPs, they are
more natural to read and write when presented as Hoare triples, with a
clear separation between precondition and postconditions. Further,
when specifications written as Hoare triples naturally induce
monotonic WPs.

F* provides an effect abbreviation called ``Pure`` for writing and
typechecking Hoare-style specifications for pure programs, and is
defined as shown below in ``prims.fst``:

.. code-block:: fstar

   effect Pure (a:Type) (req:Type0) (ens:a -> Type0) =
          PURE a (fun post -> req /\ (forall x. ens x /\ post x))

The signature of ``Pure`` is ``Pure a req ens``, where ``req`` is the
precondition and ``ens:a -> Type0`` is the postcondition. Using
``Pure``, we can write the ``factorial`` function we saw at the top of
this chapter---F* infers a ``PURE a wp`` type for it, and relates it
to the annotated ``Pure int req ens`` type, proving that the latter is
stronger.

One may wonder when one should write specifications using the notation
``x:a -> Pure b req ens`` versus ``x:a{req} -> Tot (y:b { ens y
})``. The two styles are closely related and choosing between them is
mostly a matter of taste. As you have seen, until this point in the
book, we have not used ``Pure a req ens`` at all. However, when a
function has many pre and postconditions, it is sometimes more
convenient to use the ``Pure a req ens`` notation, rather than
stuffing all the constraints in refinement types.


``GHOST`` and ``DIV``
---------------------

Just as ``PURE`` is an wp-indexed refinement of ``Tot``, F* provides
two more primitive wp-indexed effects:

  * ``GHOST (a:Type) (w:wp a)`` is a refinement of ``GTot a``

  * ``DIV (a:Type) (w:wp a)`` is a refinement of ``Dv a``    

That is, F* uses the ``GHOST`` effect to infer total correctness WPs
for ghost computations, where, internally, ``GTot a`` is equivalent to
``GHOST a (fun post -> forall x. post x)``

Likewise, F* uses the ``DIV`` effect to infer *partial correctness*
WPs for potentially non-terminating computations, where, internally,
``Dv a`` is equivalent to ``DIV a (fun post -> forall x. post x)``.

As with ``Tot`` and ``PURE``, F* automatically relates ``GTot`` and
``GHOST`` computations, and ``Dv`` and ``DIV`` computations. Further,
the effect ordering ``Tot < Dv`` and ``Tot < GTot`` extends to ``PURE
< DIV`` and ``PURE < GHOST`` as well.

The ``prims.fst`` library also provides Hoare-triple style
abbreviations for ``GHOST`` and ``DIV``, i.e.,

.. code-block:: fstar

   effect Ghost a req ens = GHOST a (fun post -> req /\ (forall x. ens x /\ post x))
   effect Div a req ens = DIV a (fun post -> req /\ (forall x. ens x /\ post x))   

These Hoare-style abbreviations are more convenient to use than their
more primitive WP-based counterparts.

The tradeoffs of using ``Ghost`` vs. ``GTot`` or ``Div`` vs. ``Dv``
are similar to those for ``Pure`` vs ``Tot``---it's mostly a matter of
taste. In fact, there are relatively few occurrences of ``Pure``,
``Ghost``, and ``Div`` in most F* codebases. However, there is one
important exception: ``Lemma``.

The ``Lemma`` abbreviation
--------------------------

We can finally unveil the definition of the ``Lemma`` syntax, which we
introduced as a syntactic shorthand in :ref:`an early chapter
<Part1_lemma_syntax>`. In fact, ``Lemma`` is defined in ``prims.fst``
as follows:

.. code-block:: fstar

   effect Lemma (a: eqtype_u)
                (pre: Type)
                (post: (squash pre -> Type))
                (smt_pats: list pattern) =
          Pure a pre (fun r -> post ())

That is, ``Lemma`` is an instance of the Hoare-style refinement of
pure computations ``Pure a req ens``.  So, when you write a proof term
and annotate it as ``e : Lemma (requires pre) (ensures post)``, F*
infers a specicification for ``e : PURE a wp``, and then, as with all
PURE computations, F* tries to check that the annotated ``Lemma``
specification has a stronger WP-specification than the computed
weakest precondition.x

Of course, F* still includes syntactic sugar for ``Lemma``, e.g.,
``Lemma (requires pre) (ensures post)`` is desugared to ``Lemma unit
pre (fun _ -> post) []``. The last argument of a lemma, the
``smt_pats`` are used to introduce lemmas to the SMT solver for proof
automation---a :ref:`later chapter <UTH_smt>` covers that in detail.

Finally, notice the type of the ``post``, which assumes ``squash pre``
as an argument--this is what allows the ``ensures`` clause of a
``Lemma`` to assume that what was specified in the ```requires``
clause.

