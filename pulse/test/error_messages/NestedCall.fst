module NestedCall
#lang-pulse
open Pulse.Lib.Pervasives

// Error in nested call should point to the specific call site
fn inner (r: ref int)
  requires pts_to r 0
  ensures pts_to r 1
{
  r := 1
}

[@@expect_failure [19]]
fn outer (r: ref int)
  requires pts_to r 5
  ensures pts_to r 1
{
  inner r;  // ERROR: precondition mismatch (pts_to r 5 vs pts_to r 0)
  ()
}
