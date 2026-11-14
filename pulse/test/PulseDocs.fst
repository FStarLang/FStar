module PulseDocs
#lang-pulse
open Pulse.Lib.Pervasives

(*| Increment a reference.

    Adds one to the value stored in [r]. *)
fn incr (r: ref int)
  requires r |-> 'v
  ensures r |-> ('v + 1)
{
  let x = !r;
  r := x + 1;
}

(*| A ghost function documented the same way. *)
ghost
fn noop ()
  requires emp
  ensures emp
{
  ()
}

(*| A plain F* value in a Pulse module. *)
let answer : int = 42
