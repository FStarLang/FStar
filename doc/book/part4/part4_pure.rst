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
first assignment, using the rule of consequence, resulting in the
following derivation. Here each of the dashed line represents
instantiation of one of the rules above::

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

F* provides a weakest precondition calculus for reasoning about pure
computations. The calculus is based on *Dijkstra Monad*, a
construction first introduced in `this paper
<https://www.microsoft.com/en-us/research/publication/verifying-higher-order-programs-with-the-dijkstra-monad/>`_
. In this chapter, we will learn about Dijkstra Monad and its usage in
specifying and proving pure programs in F*. Let's begin by adapting
the weakest precondition calculus from the previous section to the
functional setting of F*.

Let's consider a simple functional language::

  Expression e ::= x | c | let x = e1 in e2 | if e then e1 else e2

For this language, the postcondition that we may want to prove about
an expression ``e`` is a predicate on the result of computing ``e``,
while the precondition is simply a proposition. Adapting the ``WP``
function from the imperative setting to this is straightforward::

  WP c Q                      = Q c  // Q is a predicate
  WP x Q                      = Q x
  WP (let x = e1 in e2) Q     = WP e1 (fun x -> WP e2 Q)
  WP (if e then e1 else e2) Q = (e ==> WP e1 Q) /\ (~e ==> WP e2 Q)

Let's transcribe this in the F* parlance::

  type pre = prop
  type post (a:Type) = a -> prop
  type wp (a:Type) = post a -> pre

As mentioned above, preconditions are just propositions,
postconditions are predicates on the values of result type ``a``, and
the type ``wp`` is a predicate transformer.

We next transcribe in F* two of the ``WP`` rules, for values and for ``let``::

  let return_wp (#a:Type) (x:a) : wp a = fun post -> post x
  let bind_wp (#a #b:Type) (wp1:wp a) (wp2:a -> wp b) : wp b = fun post -> wp1 (fun x -> wp2 x post)


It's a monad!
^^^^^^^^^^^^^^^

It turns out that ``wp a`` is a monad (there had to be a reason behind
the names ``return_wp`` and ``bind_wp``). :ref:`Recall
<Part2_monad_intro>` that a monad consists of a type operator
(``wp``), a return function (``return_wp``), and a bind function
(``bind_wp``), and satisfies the three monad laws over a suitable
equivalence relation. For ``wp``, we can choose iff as the equivalence
relation::

  let wp_equiv (#a:Type) (wp1 wp2:wp a) : prop = forall post. wp1 post <==> wp2 post

And with this, we can prove that ``wp`` satisfies the three monad
laws::

  let left_identity (a b:Type) (x:a) (wp:a -> wp a)
    : Lemma (wp_equiv (bind_wp (return_wp a) wp) (wp x))
    = ()

  let monotonic (#a:Type) (wp:wp a) =
    forall (p q:post a). (forall x. p x ==> q x) ==> (wp p ==> wp q)

  let right_identity (a b:Type) (wp:wp a) (_:squash (monotonic wp))
    : Lemma (wp_equiv wp (bind_wp wp return_wp))
    = ()

  let associativity (a b c:Type) (wp1:wp a) (wp2:a -> wp b) (wp3:b -> wp c) (_:squash (monotonic wp1))
    : Lemma (wp_equiv (bind_wp wp1 (fun x -> bind_wp (wp2 x) wp3))
                      (bind_wp (bind_wp wp1 wp2) wp3))
    = ()

.. note::

   The proofs above rely on the *monotonicity* property of wps, which
   says that weaker postconditions should map to weaker
   preconditions. In F* pure wps are always monotonic, though in the
   proofs above we have required only one of the wps to be
   monotonic. We can also check that ``return_wp`` is monotonic, and
   if ``wp1`` and ``wp2`` are monotonic, then ``bind_wp wp1 wp2`` is
   monotonic.

The ``wp`` monad is called a Dijkstra monad, as it encodes Dijkstra's
weakest precondition calculus in its combinators.

The ``PURE`` effect
^^^^^^^^^^^^^^^^^^^^

F* provides a primitive ``PURE`` effect that allows writing and
typechecking Dijkstra monad specifications for *pure* computations. A
computation type in the ``PURE`` effect has the signature ``PURE t
wp``, where ``t`` is the return type of the computation and ``wp:wp
t``. The ``wp`` argument is also called an *index* of the ``PURE``
effect. The interpretation of ``e:PURE t wp`` is as expected: ``wp``
is the predicate transformer for ``e``. In other words, for any
postcondition ``p``, if ``wp p`` holds, then ``e`` terminates to a
value ``v:t``, and ``p v`` holds.

Let's look at some examples of writing and typechecking ``PURE``::

  open FStar.Monotonic.Pure
  let incr (x:int) : PURE int (as_pure_wp (fun post -> post (x + 1))) = x + 1

(The ``as_pure_wp`` is a technicality for coercing the wp functions
into pure wps that are required to be monotonic in F*. It is defined
in ulib/FStar.Monotonic.Pure.fst.)

In general, when F* typechecks ``e:PURE a wp``, it first computes a wp
for ``e``, let's call it ``wp_e``, and then checks that ``wp`` is
*stronger* than ``wp_e``, where stronger is defined as follows::

  //wp1 is stronger than wp2
  let stronger_wp (#a:Type) (wp1 wp2:wp a) : prop =
    forall post. wp1 post ==> wp2 post

I.e. for any postcondition ``post``, the precondition ``wp post`` implies the
precondition ``wp_e post``. This matches the intuition about
preconditions that we built earlier: it is always sound to require
more in the precondition. Thus, when we have ``e:PURE a wp`` in F*,
the ``wp`` is *a* predicate transformer for ``e``, not necessarily the
weakest one.

When computing ``wp_e``, the F* typechecker applies the combinators
``return_wp``, ``bind_wp``, ``if_then_else_wp`` (for composing
conditionals), etc. Let's look at another example::

  let maybe_incr (b:bool) (x:int)
    : PURE int (as_pure_wp (fun post -> forall (y:int). y >= x ==> post y))
    = if b then x + 1
      else x

It is worthwhile understanding the wp here. It says that to prove ``post`` of the return value, the precondition is to prove ``post`` on all ``y > x``. The ``y`` here is a valid, although much weaker, characterization of the function's return value.

We can also write a stronger spec which basically mirrors the
definition of wp for the conditionals::

  let maybe_incr (b:bool) (x:int)
    : PURE int (as_pure_wp (fun post -> (b ==> post (x + 1)) /\ ~b ==> post x)) = ...

For recursive functions, ``PURE`` works as with ``Tot``: F* checks
that some termination metric decreases in the recursive calls, and
custom termination metrics may be provided using ``decreases``::

  let rec ackermann (n m:nat)
    : PURE int (as_pure_wp (fun post -> forall (x:int). x >= 0 ==> post x))
               (decreases %[m;n])
    = if m=0 then n + 1
      else if n = 0 then ackermann 1 (m - 1)
      else ackermann_flip (ackermann (n - 1) m) (m - 1)


The wps may also encode the precondition on the function arguments,
e.g.,::

  let rec factorial (x:int)
    : PURE int (as_pure_wp (fun post -> x >= 0 /\ (forall (y:int). y >= 0 ==> post y)))
    = if x = 0
      then 1
      else x * factorial (x - 1)

In this wp, for proving any postcondition, the precondition requires
``x >= 0``.


The ``Pure`` abbreviation
^^^^^^^^^^^^^^^^^^^^^^^^^^

Arguably specifications in the Hoare-style are easier on the eyes, as
the precondition and the postcondition components are more clearly
separated. F* provides an effect called ``Pure`` for
writing and typechecking Hoare-style specifications for pure
programs. The signature of ``Pure`` is ``Pure a req ens``, where
``req:prop`` is the precondition and ``ens:a -> prop`` is the
postcondition. Using ``Pure``, we can write the ``factorial``
function above as::

  let rec factorial (x:int)
    : Pure int (requires x >= 0)
               (ensures fun r -> r >= 0)
    = if x = 0
      then 1
      else x * factorial (x - 1)

Internally, ``Pure`` is not a new effect, rather it is defined just as
an abbreviation of ``PURE``, roughly as::

  let req_ens_to_wp (#a:Type) (req:prop) (ens:a -> prop) =
    fun post -> req /\ (forall x. ens x ==> post x)
  
  effect Pure (a:Type) (req:prop) (ens:a -> prop) =
    PURE a (req_ens_to_wp req ens)

This also means that ``PURE`` and ``Pure`` code seamlessly
interoperate.

Another advantage of using ``Pure`` specifications is that, we don't
have to worry about monotonicity of wps (the ``as_pure_wp``), it is
easy to check that ``req_ens_to_wp req ens`` is monotonic for all
``req`` and ``ens``.

``PURE`` and ``Tot``
---------------------

We can view ``PURE`` as refining ``Tot``. Just like the value refinement
type ``x:t{p}`` refines the type ``t``, ``e:PURE t wp`` refines
``e:Tot t``.

For example, consider ``factorial:nat -> Tot nat`` vs ``factorial::nat
-> PURE nat (fun post -> forall (y:nat). y >= 1 ==> post y)``. Whereas
the first type only tells us that ``factorial`` returns a ``nat``, the
second type refines this further and tells us that it returns a
``y:nat`` s.t. ``y >= 1``. Using ``PURE`` computation type, we can
write and typecheck more precise specifications.

So the next natural question is, when should we use ``Tot`` and when should we use ``PURE`` (or ``Pure``). The answer, as always, is: it depends.

Since we can prove facts about ``Tot`` functions :ref:`extrinsically
<Part1_intrinsic_extrinsic>`, for very simple
``Tot`` functions, precise specifications may not be
needed. For example, for ``let incr (x:nat) : nat = x + 1``, it is
easy for F* to reason logically that ``incr x == x + 1`` at the
uses of ``incr``. For such functions, more precise specifications
in ``PURE`` may be an overkill.

This becomes a little tricky for the properties of recursive
functions. Given the following definition of list append in ``Tot``::

  let rec append (#a:Type) (l1 l2:list a) : list a =
    match l1 with
    | [] -> l2
    | hd::tl -> hd::(append tl l2)

If we want to reason that ``length (append l1 l2) == length l1 +
length l2``, we need to write a lemma using induction (no automatic
induction), and then either invoke the lemma everywhere this property
is needed or add an :ref:`SMT pattern <UTH_smt_patterns>` to it.

Alternatively, we could give ``append`` a more precise specification using ``Pure``::

  let rec append (#a:Type) (l1 l2:list a)
    : Pure (list a) (requires True)
                    (ensures fun r -> length r == length l1 + length l2)
    = ...

And now since the property about ``length`` is *intrinsic* in the type
of ``append``, no separate lemma is required. This property is
available whenever ``append`` is called.

Even for non-recursive cases, say ``let f x : Tot t = e``, it may be
the case that some property ``p`` is true of ``e``, but proving it is
non-trivial. In such cases
also, either we can write a separate lemma that proves ``p`` about
``e``, or refine the type of ``f`` to provide ``p`` in its
postcondition.

On the flip side, we don't want to (and in most cases can't) cram
all the properties in the specifications. That ``length (append l1 l2)
== length l1 + length l2`` is one property, but there are several
other properties of ``append`` (it is associative, its relation to
reverse, etc. etc.), it is not prudent to stuff all these in the spec
of ``append`` itself.

So it is basically a case-by-case judgment call whether to use ``Tot`` or
``PURE``. Hopefully the discussion above helps making this
call. Finally, as with ``Tot``, it is also possible to do extrinsic
proofs for ``PURE`` computations.

      
More on Dijkstra monad
--------------------------

Dijkstra monad was first introduced in
the paper `Verifying Higher-order Programs with the Dijkstra Monad
<https://www.microsoft.com/en-us/research/publication/verifying-higher-order-programs-with-the-dijkstra-monad/>`_,
in the context of verifying stateful programs. Then the paper
`Dependent Types and Multi-Monadic Effects in F*
<https://www.fstar-lang.org/papers/mumon/>`_ unleashed Dijkstra monads
in their full generality, showing Dijkstra monads for different
effects (pure, state, exceptions, etc.), and their
composition with each other.

Dijkstra monads have a deep connection with the continuation
monad. Continuation monad models the `Continuation Passing Style
<https://en.wikipedia.org/wiki/Continuation-passing_style/>`_ programming,
where the control is passed to the callee explicitly in the form of a
continuation. For a result type ``r``, the continuation monad is
defined as follows::

  type cont (a:Type) = (a -> r) -> r
  let return (#a:Type) (x:a) : cont a = fun k -> k x
  let bind (#a #b:Type) (f:cont a) (g:a -> cont b) : cont b =
    fun k -> f (fun x -> g x k)

If we squint a bit, we see that the ``wp`` monad we defined earlier,
is nothing but a continuation into ``prop``::

  type wp (a:Type) = (a -> prop) -> prop

The `Dijkstra Monads for Free
<https://www.fstar-lang.org/papers/dm4free/>`_ paper explores this
connection in more detail. We will also learn more about this in later
chapters.


``GHOST`` and ``DIV``
---------------------

F* provides two more primitive wp-indexed effects: ``GHOST
a wp`` and ``DIV a wp``, where the type of ``wp`` is same as that of
the ``PURE`` effect. Similar to how ``PURE`` refines ``Tot``,
``GHOST`` refines ``GTot`` and ``DIV`` refines ``Dv``. I.e., ``GHOST``
effect may be used to specify erased computations more precisely than
``GTot``, and similarly ``DIV`` may be used to specify potentially
divergent computations more precisely than ``Dv``. F* also provides
``Ghost a req ens`` and ``Div a req ens`` as the Hoare variants of
``GHOST`` and ``DIV`` respectively.

The tradeoffs of using ``GHOST`` vs ``GTot`` are similar to
those for ``PURE`` vs ``Tot``---since ``GHOST`` and ``GTot`` are also
part of the logical core of F*. However, for other effectful
computation types, such as ``Dv``, more precise specifications at the
definitions can be very useful.
