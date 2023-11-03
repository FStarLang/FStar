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
the user in a reasoning system of their choosing, e.g., the
refinements may use separation logic, or they may count computation
steps.

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
a user-provided specification of the form ``Tot t'``.

In this chapter, we look into how these ``Pure`` specifications work,
starting with a primer on Floyd-Hoare Logic and weakest precondition
calculi. If the reader is familiar with these, they may safely skip
the next subsections, though even if you are an expert, if may be of
interest to see how such program logics can be formalized in F*.


A Primer on Floyd-Hoare Logic and Weakest Preconditions
-------------------------------------------------------

Floyd-Hoare Logic is a system of specifications and rules to reason
about the logical properties of programs, introduced by Robert Floyd
in a paper titled `Assigning Meaning to Programs
<https://link.springer.com/chapter/10.1007/978-94-011-1793-7_4>`_ and
by Tony Hoare in `An axiomatic basis for computer programming
<https://dl.acm.org/doi/10.1145/363235.363259>`_. The notation used in
most modern presentations (called Hoare triples) is due to Hoare.  An
algorithm to compute Hoare triples was developed by Edsger Dijkstra
`presented first in this paper
<https://www.cs.utexas.edu/users/EWD/ewd04xx/EWD472.PDF>`_ , using a
technique called *weakest preconditions*. All of them received Turing
Awards for their work on these and other related topics.

For an introduction to these ideas, we'll develop a small imperative
language with global variables, presenting

* An operational semantics for the language, formalized as an
  interpreter.

* A Floyd-Hoare program logic proven sound with respect to the
  operational semantics.

* And, finally, an algorithm to compute weakest preconditions proved
  sound against the Floyd-Hoare logic.

Our language has the following abstract syntax:


.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: syntax$
   :end-before: //SNIPPET_END: syntax$

Expressions includes integer constants, global variables (represented
just as natural numbers), and some other forms, e.g., arithmetic
expressions like addition.

A program includes:

* Assignments, ``EAssign x e``, representing the assignment of the
  result of an expression ``e`` to a global variable ``x``, i.e., ``x := e``

* ``Seq``, to compose programs sequentially

* ``If`` to compose programs conditionally

* And ``Repeat n p``, which represents a construct similar to a
  ``for``-loop (or primitive recursion), where the program ``p`` is
  repeated ``n`` times, where ``n`` evaluates to a non-negative
  integer.

Our language does not have ``while`` loops, whose semantics are a bit
more subtle to develop. We will look at a semantics for ``while`` in a
subsequent chapter.

Operational Semantics
^^^^^^^^^^^^^^^^^^^^^

Our first step in giving a semantics to programs is to define an
interpreter for it to run a program while transforming a memory that
stores the values of the global variables.

To model this memory, we use the type ``state`` shown below:

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: state$
   :end-before: //SNIPPET_END: state$

Writing a small evaluator for expressions is easy:

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: eval_expr$
   :end-before: //SNIPPET_END: eval_expr$

The interpreter for programs itself takes a bit more work, since
programs can both read and write the state. To structure our
interpreter, we'll introduce a simple state monad ``st a``. We've seen
this construction before in :ref:`a previous chapter
<Part2_monad_intro>`---so, look there if the state monad is unfamiliar
to you. Recall that F* has support for monadic let operators: the
``let!`` provides syntactic sugar to convenient compose ``st`` terms.  

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: monad$
   :end-before: //SNIPPET_END: monad$

Now, the interpreter itself is a total, recursive function ``run`` which
interprets a program ``p`` as a state-passing function of type ``st
unit``, or ``state -> unit & state``.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: run$
   :end-before: //SNIPPET_END: run$

Let's look at its definition in detail:

   * ``Assign x e``: Evaluate ``e`` in the current state and then
     update the state with a new value of ``x``.

   * ``Seq p1 p2``: Simply run ``p1`` and then run ``p2``, where
     ``;!`` is syntactic sugar for ``let! _ = run p1 in run p2``.

   * ``If e p1 p2``: Evaluate ``e`` in the current state, branch on
     its result and run either ``p1`` or ``p2``

   * ``Repeat e p``: Evaluate ``e`` to ``n``, and if ``n`` is
     greater than zero, call the mutually recursive ``run_repeat n
     p``. Most of the subtlety here is in convincing F* that this
     mutually recursive function terminates, but this is fairly
     straightforward once you know how---we discussed
     :ref:`termination proofs for mutually recursive functions earlier
     <Part1_mutual_recursion>`.

These operational semantics are the ground truth for our programming
language---it defines how programs execute. Now that we have that
settled, we can look at how a Floyd-Hoare logic makes it possible to
reason about programs in a structured way.

Floyd-Hoare Logic
^^^^^^^^^^^^^^^^^

The goal of a Floyd-Hoare logic is to provide a way to reason about a
program based on the structure of its syntax, rather than reasoning
directly about its operational semantics. The unit of reasoning is
called a *Hoare triple*, a predicate of the form ``{P} c {Q}``, where
``P`` and ``Q`` are predicates about the state of the program, and
``c`` is the program itself.

We can *define* Hoare triples for our language by interpreting them as
an assertion about the operational semantics, where ``triple p c q``
represents, formally, the Hoare triple ``{ p } c { q }``.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: triple$
   :end-before: //SNIPPET_END: triple$

The predicate ``triple p c q`` is valid, if when executing ``c`` in a
state that satisfies ``p`` results in a state that satisfies ``q``.
The predicates ``p`` and ``q`` are also called precondition and
postcondition of ``c``, respectively.

For each syntactic construct of our language, we can prove a lemma
that shows how to build an instance of the ``triple`` predicate for
that construct. Then, to build a proof of program, one stitches
together these lemmas to obtain a ``triple p main q``, a statement of
correctess of the ``main`` program.

Assignment
++++++++++

Our first rule is for reasoning about variable assignment:

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: assignment$
   :end-before: //SNIPPET_END: assignment$

This lemma says that ``post`` holds after executing ``x := e`` in the
initial state ``s0``, if ``post`` holds on the initial state updated
at ``x`` with the value of ``e``.

For example, to prove that after executing ``z := y + 1`` in ``s0``,
if we expect the value of ``z`` to be greater than zero`, then the
assignment rule says that ``read s0 y + 1 > 0`` should hold before the
assignment, which is what we would expect.

Sequence
++++++++

Our next lemma about triples stitches together triples for two
programs that are sequentially composed:

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: sequence$
   :end-before: //SNIPPET_END: sequence$

The lemma says that if we can derive the Hoare triples of the two
statements such that postcondition of ``p1`` matches the precondition
of ``p2``, then we can compose them.


Conditional
+++++++++++

The lemma for conditionals is next:

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: conditional$
   :end-before: //SNIPPET_END: conditional$

It says that to derive the postcondition ``post`` from the ``If e p1
p2``, we should be able to derive it from each of the branches with the
same precondition ``pre``. In addition, since we know that ``p1``
executes only when ``e`` is non-zero, we can add these facts to the
preconditions of each branch.

Repeat
++++++

In all the cases so far, these lemmas are proved automated by F* and
Z3. In the case of repeats, however, we need to do a little more work,
since an inductive argument is involved.

The rule for ``repeat`` requires a *loop invariant* ``inv``.  The loop
invariant is an assertion that holds before the loop starts, is
maintained by each iteration of the loop, and is provided as the
postcondition of the loop.

The lemma below states that if we can prove that ``triple inv p inv``,
then we can also prove ``triple inv (Repeat e p) inv``.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: repeat$
   :end-before: //SNIPPET_END: repeat$

The auxiliary lemma ``repeat_n`` proves that ``run_repeat p n``
preserves ``inv``, if ``p`` preserves ``inv``.

To call this lemma from the main ``repeat`` lemma, we need to "get
our hands on" the initial state ``s0``, and the :ref:`syntactic sugar
to manipulate logical connectives <Part2_connectives>` makes this
possible.


Consequence
+++++++++++

The final lemma about our Hoare triples is called the rule of
consequence. It allows strengthening the precondition and weakening
the postcondition of a triple.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: consequence$
   :end-before: //SNIPPET_END: consequence$

A precondition of a program is an obligation before the statement
is executed. So if ``p`` requires ``pre``, we can always strengthen
the precondition to ``pre'``, provided ``pre' ==> pre``, i.e. it is
logically valid to require more than necessary in the
precondition. Similarly, postcondition is what a statement
guarantees. So if ``p`` guarantees ``post``, we can always weaken it
to guarantee less, i.e. some ``post'`` where ``post ==> post'``.

Weakest Preconditions
^^^^^^^^^^^^^^^^^^^^^

The rules of Floyd-Hoare logic provide an abstract way to reason about
programs. However, the rules of the logic are presented
declaratively. For example, to apply the ``sequence`` rule, one has
derive triples for each component in a way that they prove exactly the
same assertion (``pre_mid``) about the intermediate state. There may
be many ways to do this, e.g., one could apply the rule of
consequence to weaken the postcondition of the first component, or to
strengthen the precondition of the second component.

Dijkstra's system of weakest preconditions eliminates such ambiguity
and provides an *algorithm* for computing valid Hoare triples,
provided the invariants of all loops are given. This makes weakest
preconditions the basis of many program proof tools, since given a
program annotated with loop invariants, one can simply compute a
logical formula (called a verification condition) whose validity
implies the correctness of the program.

At the core of the approach is a function ``WP (c, Q)``, which
computes a unique, weakest precondition ``P`` for the program ``c``
and postcondition ``Q``. The semantics of ``WP`` is that ``WP (c, Q)``
is the weakest precondition that should hold before executing ``c``
for the postcondition ``Q`` to be valid after executing ``c``. Thus,
the function ``WP`` assigns meaning to programs as a transformer of
postconditions ``Q`` to preconditions ``WP (s, Q)``.

The ``wp`` function for our small imperative language is shown below:

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: wp$
   :end-before: //SNIPPET_END: wp$

* The case of ``Assign`` is identical to the ``assignment`` lemma
  shown earlier.

* The case of ``Seq`` sequentially composes the wp's. That is, to
  prove the ``post`` after running ``p1 ;; p2`` we need to prove ``wp
  p2 post`` after running ``p1``. It may be helpful to read this case
  as the equivalent form ``fun s0 -> wp p1 (fun s1 -> wp p2 post s1)
  s0``, where ``s0`` is the initial state and ``s1`` is the state that
  results after running just ``p1``.
  
* The ``If`` case computes the WPs for each branch and requires them
  to be proven under the suitable branch condition.

* The ``Repeat`` case is most interesting: it involves an
  existentially quantified invariant ``inv``, which is the loop
  invariant. That is, to reason about ``Repeat n p``, one has to
  somehow find an invariant ``inv`` that is true initially, and
  implies both the WP of the loop body as well as the final
  postcondition.

The ``wp`` function is sound in the sense that it computes a
sufficient precondition, as proven by the following lemma.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: wp_soundness$
   :end-before: //SNIPPET_END: wp_soundness$

One could also prove that ``wp`` computes the weakest precondition,
i.e., if ``triple p c q`` then ``forall s. p s ==> wp c q s``, though
we do not prove that formally here.
  
A Sample Program Proof
^^^^^^^^^^^^^^^^^^^^^^
  
We now illustrate some sample proofs using our Hoare triples and
``wp`` function. To emphasize that Hoare triples provide an *abstract*
way of reasoning about the execution of programs, we define the
``hoare p c q`` an alias for ``triple p c q`` marked with an attribute
to ensure that F* and Z3 cannot reason directly about the underlying
definition of ``triple``---that would allow Z3 to find proofs by
reasoning about the operational semantics directly, which we want to
avoid , since it would not scale to larger programs. For more about
the ``opaque_to_smt`` and ``reveal_opaque`` construct, please see
:ref:`this section on opaque definitions <UTH_opaque_to_smt>`.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: hoare$
   :end-before: //SNIPPET_END: hoare$

The lemmas above are just restatements of the ``wp_soundness`` and
``consequence`` lemmas that we've already proven. Now, these are the
only two lemmas we have to reason about the ``hoare p c q`` predicate.

Next, we define some notation to make it a bit more convenient to
write programs in our small language.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: notation$
   :end-before: //SNIPPET_END: notation$

Finally, we can build proofs of some simple, loop-free programs
automatically by computing their ``wp`` using ``wp_hoare`` and
applying ``hoare_consequence`` to get F* and Z3 to prove that the
inferred WP is implied by the annotated precondition.

.. literalinclude:: ../code/Imp.fst
   :language: fstar
   :start-after: //SNIPPET_START: swap$
   :end-before: //SNIPPET_END: swap$

This recipe of computing verification conditions using WPs and then
checking the computed WP against the annotated specification using a
solver like Z3 is a very common and powerful pattern. In fact, as
we'll see below, the methodology that we've developed here for our
small imperative language is exactly what the F* typechecker does (at
a larger scale and for the whole F* language) when checking an F*
program.

  
The ``PURE`` Effect: A Dijkstra Monad for Pure Computations
------------------------------------------------------------

F* provides a weakest precondition calculus for reasoning about pure
computations. The calculus is based on a *Dijkstra Monad*, a
construction first introduced in `this paper
<https://www.microsoft.com/en-us/research/publication/verifying-higher-order-programs-with-the-dijkstra-monad/>`_. In
this chapter, we will learn about Dijkstra Monad and its usage in
specifying and proving pure programs in F*.

The first main difference in adapting the Hoare triples and weakest
precondition computations that we saw earlier to the setting of F*'s
functional language is that there are no global variables or mutable
state (we'll see about how model mutable state in F*'s effect system
later). Instead, each pure expression in F*'s *returns* a value and
the postconditions that we will manipulate are predicates about these
values, rather than state predicates.

To illustrate, we sketch the definition of pure WPs below.

.. code-block:: none

  WP c Q                      = Q c 
  WP (let x = e1 in e2) Q     = WP e1 (fun x -> WP e2 Q)
  WP (if e then e1 else e2) Q = (e ==> WP e1 Q) /\ (~e ==> WP e2 Q)

* The WP of a constant ``c`` is just the postcondition ``Q`` applied to ``c``.
  
* The WP of a ``let`` binding is a sequential composition of WPs,
  applied to the *values* returned by each sub-expression

* The WP of a condition is the WP of each branch, weakened by the
  suitable branch condition, as before.

The F* type system internalizes and generalizes this WP construction
to apply it to all F* terms. The form this takes is as a computation
type in F*, ``PURE a wp``, where in ``prims.fst``, ``PURE`` is defined
as an F* primitive effect with a signature as shown below--we'll see
much more of the ``new_effect`` syntax as we look at user-defined
effects in subsequent chapters; for now, just see it as a reserved
syntax in F* to introduce a computation type constructor.

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
``wp`` argument is also called an *index* of the ``PURE`` effect. [#]_

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
     and ``b = nat``, the constraint ``p`` is ``fun (x:int) -> x >=
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
          PURE a (fun post -> req /\ (forall x. ens x ==> post x))

The signature of ``Pure`` is ``Pure a req ens``, where ``req`` is the
precondition and ``ens:a -> Type0`` is the postcondition. Using
``Pure``, we can write the ``factorial`` function we saw at the top of
this chapter---F* infers a ``PURE a wp`` type for it, and relates it
to the annotated ``Pure int req ens`` type, proving that the latter
has a stronger precondition and weaker postcondition.

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
infers a specification for ``e : PURE a wp``, and then, as with all
PURE computations, F* tries to check that the annotated ``Lemma``
specification has a stronger WP-specification than the computed
weakest precondition.

Of course, F* still includes syntactic sugar for ``Lemma``, e.g.,
``Lemma (requires pre) (ensures post)`` is desugared to ``Lemma unit
pre (fun _ -> post) []``. The last argument of a lemma, the
``smt_pats`` are used to introduce lemmas to the SMT solver for proof
automation---a :ref:`later chapter <UTH_smt>` covers that in detail.

Finally, notice the type of the ``post``, which assumes ``squash pre``
as an argument--this is what allows the ``ensures`` clause of a
``Lemma`` to assume that what was specified in the ```requires``
clause.

