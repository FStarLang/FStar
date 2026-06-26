module ShortCircuit

#lang-pulse
open Pulse

(* Regression coverage for stateful operands of && and ||.

   The explicit if/then/else forms verify. The operator forms now elaborate to
   the same short-circuiting conditionals, but expression-position post
   inference still cannot join the branch resources, so they remain expected
   failures with Error 228. *)

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

fn test_and_explicit (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  if (f r) { g r } else { false }
}

[@@expect_failure [228]]
fn test_and (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  f r && g r
}

[@@expect_failure [228]]
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

fn test_or_explicit (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  if (f' r) { true } else { g r }
}

[@@expect_failure [228]]
fn test_or (r:ref int)
  requires r |-> 'v
  returns b:bool
  ensures r |-> 'v
{
  f' r || g r
}

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
