module ConstructiveLogic

open FStar.Tactics

(*
As you probably know by now, verification in F* works by first computing
verification conditions for terms, and then discharging them via the SMT
solver (when they are not trivial).

When a program fails to verify, the user can take one of many paths.
Firstly, one can increase the time limit of the SMT solver, or change
its configuration in the hope that the proof will go through. More
commonly, however, the programmer needs to give the SMT solver some
help in the form of new facts that it can use. We've seen examples of
this when we call lemmas within a function body in order to make it
verify. For instance, compare the following two examples (the first of
which fails).
*)

[@expect_failure]
let modulo_add_fail (p:pos) (a b c : int)
  : Lemma (requires (b % p == c % p)) (ensures ((a + b) % p == (a + c) % p))
  = ()

let modulo_add (p:pos) (a b c : int)
  : Lemma (requires (b % p == c % p)) (ensures ((a + b) % p == (a + c) % p))
  = FStar.Math.Lemmas.modulo_distributivity a b p;
    FStar.Math.Lemmas.modulo_distributivity a c p

(*
This style of proving has two serious disadvantages. First, the goal
and set of hypotheses and not visible to the user, so proving usually
involves some trial and error. Second, there is no automation: the user
is responsible for writing all intermediate assertions and lemma calls,
which also clutter the proof/program.

With tactics, we can do better. We can inspect the "proof state",
i.e. the hypotheses we have and goal we have to solve, and implement
automated proof procedures. We can use tactics to do non-trivial proofs
without the SMT solver, or to simply give it some help when that's more
convenient. In this file we will mostly focus on the first alternative.

To get our feet wet, we will start with some simple examples of logical
propositions. The SMT is very good at this, but we will not use it at
all in the following examples.

Let us prove that implication is reflexive. We will use some tactics
from the `FStar.Tactics.Logic` module, in order to introduce the
implication and use the hypothesis.

When the goal is an implication, `implies_intro` will introduce the
implication and return a `binder` which represents the variable that was
pushed into the context. In the example, we use this `binder` to solve
the goal via `hyp`.
*)

let ex1 (p : prop) =
  assert (p ==> p)
      by (let b = implies_intro () in
          hyp b)

(*
The `qed` tactic checks that there are no more open goals when called,
or fails. We can use it here to check that we have fully solved the
assertion via tactics.
*)

(* This would fail with: (Error) user tactic failed: qed: not done! *)
//let _ =
//  assert True
//      by (qed ())

let ex1_qed (p : prop) =
  assert (p ==> p)
      by (let b = implies_intro () in
          hyp b;
          qed ())

(* Exercise: add intermediate `dump` calls to see how the proofstate evolves *)

(* The following examples are somewhat similar, try to follow them by looking
at the proof states. *)

let ex2 (p q : prop) =
  assert (p ==> q ==> p)
      by (let bp = implies_intro () in
          let _ = implies_intro () in
          hyp bp;
          qed ())

(*
We need some more interesting tactics in order to handle more kinds
of formulae, we now go over a few of them.
*)

(*
The `split` tactic will turn a goal that is a conjunction into separate
goals for each conjunct, which we can then solve independently.
*)
let ex3 (p q : prop) =
  assert (p ==> q ==> q /\ p)
      by (let bp = implies_intro () in
          let bq = implies_intro () in
          split ();
          (* Now we have two goals: q and p *)
          hyp bq;
          (* Only one goal left, p *)
          hyp bp;
          (* Done! *)
          qed ())

(* `destruct_and` can be used to destruct a conjunction and get hypotheses
for each conjunct. *)
let ex4 (p q : prop) =
  assert (p /\ q ==> p)
      by (let h = implies_intro () in
          let (bp, bq) = destruct_and (binder_to_term h) in
          hyp bp;
          qed ())

(* The `left` and `right` tactics solve a disjunction by reducing
it to the left or right disjunct accordingly. *)
let ex5 (p q : prop) =
  assert (p ==> p \/ q)
      by (let bp = implies_intro () in
          left ();
          hyp bp;
          qed ())

let ex6 (p q : prop) =
  assert (p ==> q \/ p)
      by (let bp = implies_intro () in
          right ();
          hyp bp;
          qed ())

(* `cases_or` instead destroys a disjunction `p \/ q`, and splits the
`phi` goal into `p ==> phi` and `q ==> phi`. *)
let ex7 (p q : prop) =
  assert (p \/ q ==> q \/ p)
      by (let bp_or_q = implies_intro () in
          cases_or (binder_to_term bp_or_q);
          (* first case *)
            let bp = implies_intro () in
            right ();
            hyp bp;
          (* second case *)
            let bq = implies_intro () in
            left ();
            hyp bq;
          qed ())

(* To use an implication, we can use the `mapply` tactic. This tactic
takes a `term` argument, so we need to cast the `binder` to a `term` via
`binder_to_term`. *)
let ex8 (p q : prop) =
  assert ((p ==> q) ==> p ==> q)
      by (let i = implies_intro () in
          let h = implies_intro () in
          mapply (binder_to_term i);
          mapply (binder_to_term h);
          qed ())

(* `forall_intro` will turn a goal of the shape `forall (x:t). phi` into
`phi`, while adding a variable `x` (of type `t`) to the context and
returning a binder for it. *)
let ex9 (p : prop) =
  assert (p ==> (forall (_x:int). p))
      by (let bp = implies_intro () in
          let _bx = forall_intro () in
          hyp bp;
          qed ())

(* `instantiate` will instantiate a forall with some particular term
and add the new hypothesis to the context. The `witness` tactic solves
an existential goal with the explicit witness, but requires a proof of
the property. Here we use zero as the witness, via a static quotation
(`0) (more about quotations on a next chapter). *)
let ex10 (p : int -> prop) =
  assert ((forall x. p x) ==> (exists x. p x))
      by (let bf = implies_intro () in
          witness (`0);
          let bp0 = instantiate (binder_to_term bf) (`0) in
          hyp bp0)

(* Exercises: do these proofs constructively, and make sure to end with
a `qed ()` to check that the SMT solver is not used. *)

let ex11 (p q : nat -> prop) =
  assert ((forall x. p x) ==> (forall x. p x \/ q x))
      by (smt ())

let ex12 (p q : nat -> prop) =
  assert ((forall x. p x /\ q x) ==> (forall x. p x))
      by (smt ())

let ex13 (p q : nat -> prop) =
  assert ((forall x. p x /\ q x) ==> (exists x. p x \/ q x))
      by (tadmit ()) // SMT is bad with existentials, just admit

let ex14 (a:Type) (p q : a -> prop) =
  assert ((forall x. p x ==> q x) ==> (forall x. p x) ==> (forall x. q x))
      by (smt ())
