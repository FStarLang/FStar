module MatchBranchMismatch
#lang-pulse
open Pulse.Lib.Pervasives

// Match branch postcondition mismatch - error should point to offending branch
[@@expect_failure [19]]
fn match_error (r: ref int) (x: int)
  requires pts_to r 0
  ensures pts_to r 1
{
  match x {
    0 -> { r := 1 }
    1 -> { r := 2 }
    _ -> { r := 1 }
  }
}
