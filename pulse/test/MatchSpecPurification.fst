(*
   Regression test: spec purification (Pulse.Checker.ImpureSpec) used to stop
   at a `match`, so a stateful term (`!p`) or a `ghost fn` whose `ensures` is a
   `rewrites_to` was left unelaborated whenever it occurred under a spec-level
   pattern-`let` (which desugars to a single-branch `match`).

   Two gaps were involved: `symb_eval_subterms` traversed only a match's
   scrutinee and never its branches, and `purify_spec_core` had no match case,
   so a spec that *is* a match was treated as one opaque atom and its conjuncts
   were never split (nor extruded into the context available to the stateful
   terms beside them).

   A pattern-`let` cannot be replaced by `fst`/`snd` here: a caller has to solve
   the witness by unification, and `pts_to x (fst ?w)` is inert because F* does
   not reduce projectors.

   Pre-fix errors, one per case (measured individually, since a module stops
   after its first failing definition):

     tuple_pat  : 2x Error 12 (Ill-typed term; `observe !p` / `!p` still of
                  `fn`/`ghost fn` type where an slprop was expected)
     erased_pat : 2x Error 12, same shape
     ghost_pat  : Error 339 (Cannot check relation with uvars)
     nested_pat : 2x Error 12, same shape
     tuple_ret  : Error 189 (Ill-typed term; `!p` still of `fn` type, so the
                  `q == !p` equation it appears in is ill-typed)
*)
module MatchSpecPurification
open Pulse
#lang-pulse

let predicate observe (x: nat) =
  pure (x == x)

(* Control: a stateful read in a spec with no match. Worked before the fix. *)
fn control (p: ref nat)
  requires exists* v. pts_to p #1.0R v ** observe (!p)
  returns ret: unit
  ensures exists* v. pts_to p #1.0R v ** observe (!p)
{
}

(* A tuple pattern-`let` on a plain parameter. The `!p` sits under the match
   that the pattern-`let` desugars to. *)
fn tuple_pat (pq: ref nat & nat)
  requires (let (p, _) = pq in exists* v. pts_to p #1.0R v ** observe (!p))
  returns ret: unit
  ensures (let (p, _) = pq in exists* v. pts_to p #1.0R v ** observe (!p))
{
}

(* The shape a transpiler emits for a function-pointer wrapper: the pattern-`let`
   destructures `reveal` of an `erased` tuple, so the bound variable is the
   witness the caller must solve by unification. *)
fn erased_pat (p: ref nat) (w: erased (nat & unit))
  requires (let (v0, _) = reveal w in pts_to p #1.0R v0 ** observe (!p))
  returns ret: unit
  ensures (let (v0, _) = reveal w in pts_to p #1.0R v0 ** observe (!p))
{
}

(* A ghost fn whose `ensures` is a `rewrites_to`; the purifier evaluates a call
   to it symbolically, proving its precondition against the surrounding
   context. Under a pattern-`let` that context has to be gathered from the
   conjuncts inside the match. *)
ghost fn ref_val (r: ref nat) #p (#v: nat)
  preserves pts_to r #p v
  returns x: nat
  ensures rewrites_to x v
{ v }

fn ghost_pat (pq: ref nat & nat)
  requires (let (p, _) = pq in
            exists* v. pts_to p #1.0R v ** pure (ref_val p == ref_val p))
  returns ret: unit
  ensures (let (p, _) = pq in
           exists* v. pts_to p #1.0R v ** pure (ref_val p == ref_val p))
{
}

(* Nested pattern-`let`s, i.e. a match inside a match. *)
fn nested_pat (p: ref nat) (w: erased ((nat & unit) & unit))
  requires (let (we, _) = reveal w in
            let (v0, _) = we in
            pts_to p #1.0R v0 ** observe (!p))
  returns ret: unit
  ensures (let (we, _) = reveal w in
           let (v0, _) = we in
           pts_to p #1.0R v0 ** observe (!p))
{
}

(* Both projections of a tuple *return* value. Three things are new here: the
   scrutinee is the `returns` binder rather than a parameter, so the match is
   over a variable the purifier did not itself bind; both binders are live
   rather than one binder and a wildcard, so the branch's binder ordering
   actually matters; and the stateful term sits inside a `pure` relating one
   projection to the other, so discharging it needs the `pts_to` conjunct from
   *inside* the same branch to have been extruded beside it. The body is
   implemented rather than admitted, so the elaborated `q == !p` is checked to
   be provable and not merely well-formed. *)
fn tuple_ret (p0: ref nat)
  requires exists* v. pts_to p0 #1.0R v
  returns pq: (ref nat & nat)
  ensures (let (p, q) = pq in exists* v. pts_to p #1.0R v ** pure (q == !p))
{
  let v = !p0;
  (p0, v)
}
