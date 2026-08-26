(*
   Regression test for https://github.com/FStarLang/FStar/issues/4491

   When a Pulse function's specification mentions a value reached from an
   argument by tuple projections, an `_` at the call site should be solved: the
   precondition pins the value under the hole to `7`, and there is nothing else
   the hole could be.

   This used to work at one projection but fail at two with Error 228
   ("Unexpected unresolved uvars"). `Pulse.Checker.Prover.pure_eq_unif` only
   unifies when one side of the equation is a *bare* uvar, and the projections
   were reduced by `Pulse.Simplify.simplify`, which was a single top-down pass:
   at `fst (fst ((c, ()), ()))` no rule fired at the outer node, and by the time
   the argument had been rewritten to `(c, ())` the outer node was never revisited,
   leaving the stuck goal `pure (fst (c, ()) == 7)`.

   `simplify` now simplifies arguments first and iterates to a fixpoint, so both
   calls below are solved. Note that this is inference only where the answer is
   unique: `d2 (_, ())`, with a single hole for the whole inner tuple, is still
   rejected, since `fst ?u == 7` does not determine `?u`.
*)
module TupleDepth
#lang-pulse
open Pulse

(* one projection: `fst y` *)

fn d1 (y: (int & unit))
  requires pure (fst y == 7)
  ensures  emp
{ () }

fn call_d1 ()
  requires emp
  ensures  emp
{
  d1 (_, ());
}

(* two projections: `fst (fst y)` *)

fn d2 (y: ((int & unit) & unit))
  requires pure (fst (fst y) == 7)
  ensures  emp
{ () }

fn call_d2 ()
  requires emp
  ensures  emp
{
  d2 ((_, ()), ());
}

(* three projections *)

fn d3 (y: (((int & unit) & unit) & unit))
  requires pure (fst (fst (fst y)) == 7)
  ensures  emp
{ () }

fn call_d3 ()
  requires emp
  ensures  emp
{
  d3 (((_, ()), ()), ());
}
