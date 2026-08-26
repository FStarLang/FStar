(*
   Reproducer (currently FAILING, deliberately not fixed) for
   https://github.com/FStarLang/FStar/issues/4491

   When a Pulse function's specification mentions a value reached from an
   argument by *one* tuple projection, an `_` at the call site is solved. When
   the same value is reached by *two* projections, the `_` is left unsolved and
   the call fails with Error 228, even though the precondition pins the value
   under the hole to `7` and there is nothing else the hole could be.

   The specification is provable; only inference fails: writing the value out by
   hand (`d2 ((7, ()), ())`) verifies. It is depth, not arity or position: three
   projections fail too, and a single hole for the whole inner tuple
   (`d2 (_, ())`) fails the same way.

   Expected output today:

     * Error 228 at TupleDepth.fst(...):
       - Tactic failed
       - Unexpected unresolved uvars in the term:
       - 'd2 (((*?u45*)_, ()), ())'
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
  d1 (_, ());          // verifies
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
  d2 ((_, ()), ());    // Error 228
}
