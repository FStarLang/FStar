module IfBranchMismatch
#lang-pulse
open Pulse.Lib.Pervasives

// If branches produce different resources
[@@expect_failure [19]]
fn if_branch_mismatch (r: ref int) (b: bool)
  requires pts_to r 0
  ensures pts_to r 1
{
  if b {
    r := 1
  } else {
    r := 2  // ERROR: this branch gives pts_to r 2, should be 1
  }
}
