module ShortCircuit
#lang-pulse
open Pulse

(* Pulse short-circuits the stateful operands of the boolean operators && and ||.

   When an expression such as `f r && g r` contains stateful sub-expressions,
   the second operand must only be evaluated when the first does not already
   determine the result, i.e. && / || elaborate to the short-circuiting

     if f r then g r else false

   rather than eagerly evaluating both operands

     let a = f r in let b = g r in a && b

   The tests below check this: the explicit if/then/else controls and the
   && / || forms both verify. *)

fn f (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v ** pure (b ==> 'v == 0)
{ admit() }

fn g (r:ref int)
  requires r |-> 'v ** pure ('v == 0)
  returns b:bool
  ensures r |-> 'v
{ admit() }

(* Intended short-circuit semantics, written explicitly: `g r` is only reached
   when `f r` returned true, so `pure ('v == 0)` is available. This verifies. *)
fn test_and_explicit (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  if (f r) { g r } else { false }
}

(* The same program written with &&. It has identical short-circuit semantics:
   `g r` is only evaluated when `f r` returned true, so its precondition
   `pure ('v == 0)` is available. This verifies now that && short-circuits its
   stateful operands. *)
fn test_and (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  f r && g r
}

(* Nested && also short-circuits: the inner `f r && f r` becomes the scrutinee
   of the outer conditional, and `g r` is only reached when it is true (which
   implies `'v == 0`). *)
fn test_and_nested (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  (f r && f r) && g r
}

fn f' (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v ** pure (not b ==> 'v == 0)
{ admit() }

(* Intended short-circuit semantics for ||, written explicitly: `g r` is only
   reached when `f' r` returned false, so `pure ('v == 0)` is available. *)
fn test_or_explicit (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  if (f' r) { true } else { g r }
}

(* The same program written with ||. It verifies now that || short-circuits:
   `g r` is only evaluated when `f' r` returned false (which implies
   `'v == 0`). *)
fn test_or (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  f' r || g r
}

(* The same root cause used to show up in the guard of a while loop, the
   motivating example `while (a && b)`. With && / || short-circuiting, the
   guard now desugars to a conditional with a stateful branch. These loops
   still do not verify, but for a *different*, independent reason: the Pulse
   while-checker cannot yet infer a post-condition for a guard whose boolean
   result is tied to a stateful branch (tracked separately as the while-guard
   post-inference limitation, "Part B"). They are kept as expected failures
   without a specific error code until that is fixed. *)
[@@expect_failure]
fn loop_and (r:ref int)
  requires r |-> 'v
  ensures r |-> 'v
{
  while (f r && g r)
    invariant r |-> 'v
  { () }
}

[@@expect_failure]
fn loop_or (r:ref int)
  requires r |-> 'v
  ensures r |-> 'v
{
  while (f' r || g r)
    invariant r |-> 'v
  { () }
}
