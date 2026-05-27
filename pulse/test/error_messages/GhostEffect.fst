module GhostEffect
#lang-pulse
open Pulse.Lib.Pervasives

// Using a ghost value in a total computation
ghost
fn ghost_fn ()
  requires emp
  returns r: int
  ensures emp
{
  42
}

[@@expect_failure [228]]
fn non_ghost_caller ()
  requires emp
  returns r: int
  ensures emp
{
  let x = ghost_fn ();  // ERROR: ghost in non-ghost context
  x
}
