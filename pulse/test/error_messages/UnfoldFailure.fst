module UnfoldFailure
#lang-pulse
open Pulse.Lib.Pervasives

// Failure when trying to match a predicate that can't be unfolded
let my_pred (r: ref int) : slprop = pts_to r 0

[@@expect_failure [228]]
fn unfold_fail (r: ref int)
  requires my_pred r
  ensures pts_to r 1
{
  r := 1  // ERROR: can't write to r without unfolding my_pred first
}
