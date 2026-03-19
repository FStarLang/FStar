module LoopInvariants

#lang-pulse
open Pulse

fn test0 ()
{
  while (true)
    invariant (emp)
  { (); }
}

fn test1 ()
{
  (* This failed to parse, confusing the opening brace
  for the start of a refinement. `invariant (emp)` worked*)
  while (true)
    invariant emp
  { (); }
}

(* Multiple invariant annotations in a loop are just
starred together. *)
fn test2 (r s : ref int)
  preserves r |-> 1
  preserves s |-> 2
{
  while (true)
    invariant r |-> 1
    invariant emp
    invariant s |-> 2
  { (); }
}

(* You can have no invariants, that's the same as annotating
emp. *)
fn test3 (r s : ref int)
  preserves r |-> 1
  preserves s |-> 2
{
  while (true)
  {
    r := !s - 1;
    s := !r + 1;
  }
}

fn test4 ()
{
  while (true)
    invariant emp
    invariant emp
  { (); }
}

[@@expect_failure]
fn test6 (r s : ref int)
  preserves r |-> 1
  preserves s |-> 2
{
  while (true)
    invariant r |-> 1
    invariant emp
    invariant s |-> 2
  { s := 3; }
}

[@@expect_failure]
fn test7 (r s : ref int)
  preserves r |-> 1
  preserves s |-> 2
{
  (* We infer the same invariant as above. *)
  while (true)
    invariant r |-> 1
  { s := 3; }
}
