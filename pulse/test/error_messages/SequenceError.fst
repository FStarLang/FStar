module SequenceError
#lang-pulse
open Pulse.Lib.Pervasives

// Error after a sequence of operations - check where error is reported
[@@expect_failure [19]]
fn seq_error (r1 r2: ref int)
  requires pts_to r1 0 ** pts_to r2 0
  ensures pts_to r1 1 ** pts_to r2 1
{
  r1 := 1;
  r2 := 2;  // ERROR: should point here, post expects pts_to r2 1
  ()
}
