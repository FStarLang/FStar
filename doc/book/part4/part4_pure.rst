.. _Part4_Pure:

Primitive Effect Refinements
==============================

Refinement types ``x:t{p}`` *refine* value types ``t`` and allow us
to make more precise assertions about the values in the program. For
example, when we have ``v : x:int{x >= 0}``, then not only we know
that ``v`` is an ``int``, but also that ``v >= 0``.

In a similar manner, F* allows refining computation types with more
precise specifications about the behavior of the computations. These
refinements, and how they are typechecked by F*, encode the standard
reasoning principles of Hoare Logic and Weakest Precondition-based
calculi. Foreshadowing what's about to come in this chaper, we can
write the following specification for the ``factorial`` function::

  let rec factorial (x:int) : Pure int (requires x >= 0) (ensures fun r -> r >= 1) =
    if x = 0
    then 1
    else x * factorial (x - 1)

To understand what the specification means, let's start with a primer
on Hoare Logic and Weakest Precondition-based reasoning. If the reader
is familiar with these, they may safely skip the next two subsections.


A Primer on Hoare Logic
-------------------------

Hoare Logic is a system of specifications and reasoning principles to
reason about the logical properties of programs. It was introduced by
Tony Hoare in the paper `An axiomatic basis for computer
programming <https://dl.acm.org/doi/10.1145/363235.363259/>`_, in the
context of reasoning about imperative programs.

Let's consider a small imperative language with the following grammar::

  Expression e ::= x | ...

  Statement s ::= skip | x := e | s1; s2 | if e then s1 else s2 | while e s

The language consists of expressions ``e``, which include variables
``x, y, z, ...``. Assume that all the variables have global scope. We
leave the rest of the expression forms as underspecified, as the core
reasoning rules are also abstract in them. The statements ``s`` in the
language consist of ``skip`` (a no-op), assignment statement,
sequencing, conditionals, and while loops with guard ``e`` and loop
body ``s``.

Hoare Logic is a reasoning system for such a language. The unit of
reasoning in Hoare Logic is a *triple* of the form ``{P} s {Q}``, where
``P`` and ``Q`` are assertions (logical formulas) about the state of
the program. In its simplest form, program state is just a mapping of
variables to values.

A Hoare triple ``{P} s {Q}`` is valid, if executing ``s`` in a state
that satisfies ``P`` results in a state that satisfies ``Q``. ``P``
and ``Q`` are also called precondition and postcondition of ``s``
respectively. There are both total correctness and partial correctness
interpretations of the triple, depending on whether the termination of
``s`` is ensured by the logical system.

The Hoare Logic *inference rules* provide axioms for valid Hoare
triples for each statement form, reflecting their logical reasoning
principles. A triple ``{P} s {Q}`` is *derivable* in the system
if these axioms can be instantiated and arranged together in a
*derivation tree* with ``{P} s {Q}`` at the leaf. We first look at
each individual axiom, and then examples of such derivation trees.


Skip
^^^^^^^^

The inference rule for ``skip`` is as shown below::

  ---------------- :: [Skip]
    {P} skip {P}


Inference rules is a general technique of specifying a reasoning
system. An inference rule has two parts, premises and a
conclusion, separated by a horizontal line. The interpretation of an
inference rule is that, given the premises, the rule can be
applied to derive the conclusion. An inference rule may optionally be
named, the ``:: [Skip]`` part here.

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

The assignment rule is more interesting::

  ----------------------- :: [Assign]
    {P[e/x]} x := e {P}


This rule also does not have premise. It says that, ``P`` holds after
executing ``x := e``, if ``P[e/x]``, i.e. ``P`` with ``x`` substituted
with ``e``, holds before executing the statement.

For example, if we wanted to reason that after ``x := y + 1``, ``x >
0`` holds, then the rule says that ``(x > 0)[(y + 1)/x]`` should hold
before the assigment. Simplifying a little, if ``y > -1``, which is
what we would expect. So, applying this rule, we can derive that the
Hoare triple ``{y > -1} x := y + 1 {x > 0}`` is valid.


Sequence
^^^^^^^^^^^^

The sequencing rule stitches together triples for the two statements::

  {P} s1 {R}    {R} s2 {Q}
  ------------------------- :: [Seq]
    {P} s1; s2 {Q}


The rule has two premises. It says that, if we can derive the Hoare
triples of the two statements such that postcondition of ``s1``
matches the precondition of ``s2``, then we can derive the Hoare
triple for ``s1; s2`` as written in the conclusion.
    

Conditional
^^^^^^^^^^^^^

The rule for conditionals is as follows::


  {P /\ e} s1 {Q}    {P /\ ~e} s2 {Q}
  ------------------------------------- :: [If]
     {P} if e then s1 else s2 {Q}

Intuitively, the rule says that to derive the postcondition ``Q``
from the conditional statement, we should be able to derive it from
each of the branch. In addition, since we know that ``s1`` executes
only when ``e`` is true, ``e`` can be added to the precondition of
``s1``, and similarly for ``s2``.


While
^^^^^^^^

The rule for ``while`` requires a *loop invariant*::


  {I && e} s {I}
  ------------------------ :: [While]
  {I} while e s {I && ~e}


Here, the loop invariant ``I`` is an assertion that holds before the
loop starts, is maintained by each iteration of the loop, and is
provided as the postcondition of the loop. While the rule uses the
loop invariant *declaratively*, without worrying about where the
invariant comes from, an actual tool that implements Hoare Logic has
to either infer it or require it as an annotation from the user.

This rule establishes partial correctness, it does not ensure that
the loop terminates. It is possible to augment the rule with
termination metrics to ensure total correctness, see `here
<https://en.wikipedia.org/wiki/Hoare_logic/>`_ for example.

Consequence
^^^^^^^^^^^^^^

The final inference rule is the *rule of consequence* that allows
strengthening the precondition and weakening the postcondition::


  P ==> P1    {P1} s {Q1}    Q1 ==> Q
  ------------------------------------- :: [Consequence]
              {P} s {Q}      

One way to think of the precondition of a statement is as an
obligation before the statement is executed. So if ``s`` requires
``P1``, we can always strengthen the precondition to ``P``, provided
``P ==> P1``, i.e. it is always logically valid to require more than
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
first assignment, using the rule of consequence, resulting in::

                    ------------------------------
   y > 3 ==> y > 3    {y > 3} x := y + 1 {x > 4}    x > 4 ==> x > 1
   -----------------------------------------------------------------     ---------------------------
                      {y > 3} x:= y + 1 {x > 1}                          {x > 1} z := x + 1 {z > 2}
                      -------------------------------------------------------------------------------
                                   {y > 3} x := y + 1; z := x + 1 {z > 2}


   
.. note::

   There may be multiple derivations possible for the same Hoare
   triple. For example, another way to combine the two assignments in
   the example above would be to strengthen the precondition of the
   second assignment. This source of non-determinism comes from the
   *non syntax directed* rule of consequence. For every other rule,
   the shape of the conclusion uniquely determines when the rule may
   be applied. For example, the assignment rule is only applicable for
   statements of the form ``x := e``. Whereas the rule of consequence
   may be non-deterministically applied anywhere.

.. note::

   Such a reasoning system for a programming language is also
   sometimes called its *axiomatic semantics*. Defining semantics of a
   programming language means ascribing formal meaning to the programs
   in the language. There are `3 main styles
   <https://en.wikipedia.org/wiki/Semantics_(computer_science)/>`_ of
   defining language semantics: operational semantics, denotational
   semantics, and axiomatic semantics. Operational semantics defines a
   transition system for how programs in a language execute, i.e. an
   *operational* view of the program. Denotational semantics ascribes
   denotations (meaning) to programs in some target domain. Finally,
   the axiomatic semantics defines the meaning of a program as its
   logical interpretation.

     
Weakest Precondition Calculus
-------------------------------

A closely related reasoning system based on *weakest
preconditions* was given by `Edsger W. Dijkstra
<https://dl.acm.org/doi/10.1145/360933.360975/>`_. While Hoare
Logic is declarative and defines a set of non syntax-directed
inference rules, weakest precondition calculus takes a more
*algorithmic* approach, and
defines a function ``WP (s, Q)``, that computes a unique, weakest
precondition ``P`` for the statement ``s`` and postcondition
``Q``. The semantics of ``WP`` is that ``WP (s, Q)`` is
the weakest precondition that should hold before executing ``s`` for
the postcondition ``Q`` to be valid after executing ``s``. Thus, the
weakest precondition calculus assigns meaning to programs as a
transformer of postconditions ``Q`` to preconditions ``WP (s,
Q)``. The ``WP`` function is defined as follows for our imperative
language::

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

With this background knowledge on Hoare Logic and Weakest
Precondition calculus, we can now get back to F* and how F* allows
similar reasoning.

  
A Dijkstra Monad for Pure Computations
----------------------------------------

F* provides a weakest precondition calculus for pure computations. The
calculus is based on *Dijkstra Monad*, a construction first introduced
in `this paper
<https://www.microsoft.com/en-us/research/publication/verifying-higher-order-programs-with-the-dijkstra-monad/>`_
. In this chapter, we will learn about Dijkstra Monad and its usage in
specifying and proving pure programs in F*. Let's begin by adapting
the weakest precondition calculus from the previous section to the
functional setting of F*.

Let's consider a simple functional language::

  e ::= x | c | let x = e1 in e2 | if e then e1 else e2


``PURE`` is a refinement of ``Tot``
-----------------------------------



``GHOST`` and ``DIV``
---------------------


