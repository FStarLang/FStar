module StatefulIfCondition

#lang-pulse
open Pulse

(* Regression test for issue #443: stateful if/match conditions *)

(* Pure conditions still work with backward-compatible syntax *)
fn pure_condition (x : bool)
  requires emp
  ensures  emp
{
  if x {
    ();
  } else {
    ();
  }
}

(* Basic stateful condition — was already supported via hoisting *)
fn basic_stateful_if (r : ref int)
  requires r |-> 'v
  ensures  r |-> 'v
{
  if (!r = 0) {
    ();
  } else {
    ();
  }
}

(* Nested stateful if in condition — the core of issue #443 *)
fn nested_stateful_if (r : ref int)
  requires r |-> 0
  ensures  r |-> 0
{
  if (if true then !r = 0 else false) {
    ();
  } else {
    ();
  }
}

(* Stateful match scrutinee *)
fn stateful_match (r : ref int)
  requires r |-> 0
  ensures  r |-> 0
{
  match (!r) {
    0 -> { (); }
    _ -> { (); }
  }
}

(* Hard case from issue #443: stateful expression inside F*-level if in pure expression *)
fn hard_case (r : ref int) (b : bool)
  requires r |-> 'v
  ensures  r |-> 'v
{
  let foo = (if b then !r + 42 else 67) + 10;
  ()
}

fn consume (r : ref int)
  requires r |-> 'v
  returns b : bool
  ensures (if b then emp else r |-> 'v)
{
  admit();
}

fn test (b : bool) (r : ref int)
  requires r |-> 0
{
  if (consume r) {
    ();
  } else {
    drop_ (r |-> _);
  };
  ()
}
