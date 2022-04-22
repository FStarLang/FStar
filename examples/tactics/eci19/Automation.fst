module Automation

open FStar.Tactics

(*
As you have seen, doing constructive proofs by hand can get tedious. We
can instead write automated procedures for some classes of proofs, that
we can call over and over again when we need them, which is the main
motivation for tactic engines in other languages.

Some simple procedures are implemented in the standard library. For
instance, `assumption` tries to solve the current goal from the
hypotheses in the context. Let's first write a tactic that introduces
all implications and then calls `assumption`. (You can look at the
definition of `assumption` in FStar.Tactics.Derived.)
*)

(* Exercise: what does `l_intros` do? Look at its definition to find out. *)

let triv () : Tac unit =
  let _ = l_intros () in
  assumption ();
  qed ()

(* Now we can call it on different goals *)

let ea1 (p q r : prop) =
  assert (p ==> q ==> r ==> p)
      by (triv ())

let ea2 (p q r : prop) =
  assert (p ==> q ==> r ==> q)
      by (triv ())

let ea3 (p q r : prop) =
  assert (p ==> q ==> r ==> r)
      by (triv ())

let ea4 (p q r : prop) =
  assert (p ==> q ==> r ==> (forall (x:int). r))
      by (triv ())

(* This simple tactic will not work with conjunctions, though. Try it! *)

//let ea5 (p q : prop) =
//  assert (p ==> q ==> p /\ q)
//      by (triv ())

(*
We can improve the tactic to also call `split` when the goal is a
conjunction. To do that we need a way to inspect the goal. The most
comfortable way to do that here is by calling `cur_formula ()`, which
returns the current goal represented as a value in the `formula` type.

  noeq type formula =
    | True_  : formula
    | False_ : formula
    | Comp   : comparison -> term -> term -> formula
    | And    : term -> term -> formula
    | Or     : term -> term -> formula
    | Not    : term -> formula
    | Implies: term -> term -> formula
    | Iff    : term -> term -> formula
    | Forall : bv -> term -> formula
    | Exists : bv -> term -> formula
    | App    : term -> term -> formula
    | Name   : bv -> formula
    | FV     : fv -> formula
    | IntLit : int -> formula
    | F_Unknown : formula

When `cur_formula` returns an `And`, we will call `split`, and then
recursively executing our tactic on each subgoal, with the help of
`seq`. Running `seq t1 t2` will run `t1` and then, for all new goals,
run `t2` on each, so we recurse on both conjuncts. The `split` tactic
fails (i.e. raises an exception) when the goal is not a conjunction, so
we will only do that when the goal is indeed a conjunction.
*)

let rec conjt () : Tac unit =
  let _ = l_intros () in
  match cur_formula () with
  | And _ _ -> seq split conjt
  (* otherwise, just try to solve via an assumption *)
  | _ -> (assumption (); qed ())

(* Now, we can prove all of the previous formulae, plus the one with a
conjunction, and more. *)

let ea1' (p q r : prop) =
  assert (p ==> q ==> r ==> p)
      by (conjt ())

let ea2' (p q r : prop) =
  assert (p ==> q ==> r ==> q)
      by (conjt ())

let ea3' (p q r : prop) =
  assert (p ==> q ==> r ==> r)
      by (conjt ())

let ea4' (p q r : prop) =
  assert (p ==> q ==> r ==> (forall (x:int). r))
      by (conjt ())

let ea5' (p q : prop) =
  assert (p ==> q ==> p /\ q)
      by (conjt ())

let ea6' (p q r : prop) =
  assert (p ==> r ==> q ==> (p /\ (q ==> r)))
      by (conjt ())

let ea7' (p q r : prop) =
  assert (p ==> q ==> ((r ==> p) /\ (r ==> p ==> q)))
      by (conjt ())

(* Exercise: the `conjt` fails for goals such as the following. Why? Can
you fix it so it will solve it (and all previous goals?) *)

//let eb1 (p q: prop) =
//  assert ((p ==> q) ==> (p ==> q))
//      by (conjt ())

(* Exercise: extend `conjt` to also solve disjunctions. (Hint: use
`try..with` to backtrack.) It should solve all of the following goals.
*)

let disjt () : Tac unit = smt () (* but don't use SMT :) *)
  
let ea1'' (p q r : prop) =
  assert (p ==> q ==> r ==> p)
      by (disjt ())

let ea2'' (p q r : prop) =
  assert (p ==> q ==> r ==> q)
      by (disjt ())

let ea3'' (p q r : prop) =
  assert (p ==> q ==> r ==> r)
      by (disjt ())

let ea4'' (p q r : prop) =
  assert (p ==> q ==> r ==> (forall (x:int). r))
      by (disjt ())

let ea5'' (p q : prop) =
  assert (p ==> q ==> p /\ q)
      by (disjt ())

let ea6'' (p q r : prop) =
  assert (p ==> r ==> q ==> (p /\ (q ==> r)))
      by (disjt ())

let ea7'' (p q r : prop) =
  assert (p ==> q ==> ((r ==> p) /\ (r ==> p ==> q)))
      by (disjt ())

let ea8'' (p q : prop) =
  assert (p ==> q ==> p \/ q)
      by (disjt ())

let ea9'' (p q : prop) =
  assert (p ==> p \/ q)
      by (disjt ())

let ea10'' (p q : prop) =
  assert (q ==> p \/ q)
      by (disjt ())
