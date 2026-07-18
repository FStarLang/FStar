module PrePostMismatch
#lang-pulse
open Pulse.Lib.Pervasives

// Post-condition doesn't match what the body establishes
[@@expect_failure [19]]
fn pre_post_mismatch (r: ref int)
  requires pts_to r 0
  ensures pts_to r 42
{
  r := 1;
  ()
}
