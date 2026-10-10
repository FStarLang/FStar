(*
   Which `_` holes can Pulse and F* solve?

   Two mechanisms solve a hole outright:

   - F* solves *uni-valued* implicits in `try_solve_single_valued_implicits`
     (`FStarC.TypeChecker.Rel.fst`): a `?u : unit`, or a unit refinement, is set
     to `()` with no constraint needed. The comment on that function records how
     narrow it is:

       For now we handle only unit and unit refinement typed implicits,
       we can later extend it to single constructor inductives

   - The Pulse prover solves a hole standing on one side of a `pure (a == b)`
     goal (`Pulse.Checker.Prover.pure_eq_unif`). It requires a *bare* uvar there,
     so `?u == 4` qualifies while `fst ?u == 4` does not.

   Neither reaches a hole standing for a whole tuple, which used to mean such a
   hole had to be split into `(_, _)` by hand -- even when the tuple was uniquely
   determined, and even when every component would individually have been solved.

   `Pulse.Eta` closes that gap by eta-expanding a product-typed hole, refining
   `?u : t1 & t2` into `(?a, ?b)`. That is a structural step, not a guess: every
   inhabitant of a product *is* a pair, so it commits to no value, and a
   component left unsolved still raises Error 228. Once expanded, the two
   mechanisms above reach the components, and `Pulse.Simplify` reduces the
   projections that mention them.

   The tests below are grouped by which mechanism does the work. Every one of
   them is expected to verify; the second group is the one that eta-expansion
   made possible, and each case there names the error it used to produce.
*)
module EtaUnitInference
#lang-pulse
open Pulse

////////////////////////////////////////////////////////////////////////////////
// Solved
////////////////////////////////////////////////////////////////////////////////

(* A lone hole at `unit`, with no equation mentioning it at all. *)

fn takes_unit (u: unit)
  requires emp
  ensures  emp
{ () }

fn call_unit ()
  requires emp
  ensures  emp
{
  takes_unit _;
}

(* Unit refinements are covered by the same rule. *)

fn takes_refined_unit (u: (x:unit{True}))
  requires emp
  ensures  emp
{ () }

fn call_refined_unit ()
  requires emp
  ensures  emp
{
  takes_refined_unit _;
}

(* Both components of a product, by the two different mechanisms: the `int` from
   the precondition, the `unit` from the uni-valued rule. The two equations have
   to be separate `pure`s joined by `**`; `pure (p /\ q)` is not split, so
   `pure_eq_unif` would never see a bare equation. *)

fn both (y: (int & int))
  requires pure (fst y == 4) ** pure (snd y == 7)
  ensures  emp
{ () }

fn call_both_split ()
  requires emp
  ensures  emp
{
  both (_, _);
}

fn unit_fst (y: (unit & int))
  requires pure (snd y == 7)
  ensures  emp
{ () }

fn call_unit_fst_split ()
  requires emp
  ensures  emp
{
  unit_fst (_, _);
}

fn pair_unit (y: (unit & unit))
  requires emp
  ensures  emp
{ () }

fn call_pair_unit_split ()
  requires emp
  ensures  emp
{
  pair_unit (_, _);
}

////////////////////////////////////////////////////////////////////////////////
// Solved only by eta-expanding the hole
//
// Each of these was an Error 228 before `Pulse.Eta` existed, and each is
// written with a single `_` where the group above had to write `(_, _)`.
////////////////////////////////////////////////////////////////////////////////

(* `unit & unit` has exactly one inhabitant, so the hole is as uniquely
   determined as a `unit` one -- but it is a single constructor inductive rather
   than `unit`, so the uni-valued rule does not reach it.

     Previously: Error 228, `pair_unit ?u` *)

fn call_pair_unit_hole ()
  requires emp
  ensures  emp
{
  pair_unit _;
}

(* Mixing the two: one component uni-valued, the other fixed by an equation.
   Both mechanisms would apply if the hole were split, and neither applies to the
   undivided hole.

     Previously: Error 228, `unit_fst ?u` *)

fn call_unit_fst_hole ()
  requires emp
  ensures  emp
{
  unit_fst _;
}

(* Splitting only the outer product is not enough when a component is itself a
   product. Here the `int` is solved from the precondition and the remaining hole
   is the `unit & unit` one, which again needs eta:

     Previously: Error 228, `mixed_left (?u, 7)` *)

fn mixed_left (y: ((unit & unit) & int))
  requires pure (snd y == 7)
  ensures  emp
{ () }

fn call_mixed_left ()
  requires emp
  ensures  emp
{
  mixed_left (_, _);
}

(* The same nested on the right: the outer `unit` is solved by the uni-valued
   rule, and the leftover hole at `unit & int` is not, even though both of *its*
   components would be.

     Previously: Error 228, `mixed_right ((), ?u)` *)

fn mixed_right (y: (unit & (unit & int)))
  requires pure (snd (snd y) == 7)
  ensures  emp
{ () }

fn call_mixed_right ()
  requires emp
  ensures  emp
{
  mixed_right (_, _);
}

(* A product whose components are *both* determined -- `(4, 7)` is the only
   possible argument -- yet the undivided hole is not solved. Nothing here is
   uni-valued and nothing is nested: this is eta-expansion and nothing else,
   which is why `call_both_split` above already succeeded on the very same
   signature.

   Note the two components are solved by two *different* goals, so by the time
   `snd ?u == 7` is looked at, `?u` has already been expanded and partly solved;
   the projection still has to be simplified to expose the second component. *)

fn call_both_hole ()
  requires emp
  ensures  emp
{
  both _;
}

////////////////////////////////////////////////////////////////////////////////
// Still rejected -- eta-expansion refines a hole, it does not guess a value
////////////////////////////////////////////////////////////////////////////////

(* Nothing constrains either component, so both survive the expansion and the
   error is still reported. This is the property that makes the expansion safe:
   `?u` becomes `(?a, ?b)`, which commits to no value.

     Error 228: `unconstrained (?a, ?b)` *)

fn unconstrained (y: (int & int))
  requires emp
  ensures  emp
{ () }

[@@expect_failure [228]]
fn call_unconstrained ()
  requires emp
  ensures  emp
{
  unconstrained _;
}

(* One component determined, the other not: the determined one is solved and the
   error names only what is genuinely missing.

     Error 228: `half_constrained (4, ?b)` *)

fn half_constrained (y: (int & int))
  requires pure (fst y == 4)
  ensures  emp
{ () }

[@@expect_failure [228]]
fn call_half_constrained ()
  requires emp
  ensures  emp
{
  half_constrained _;
}
