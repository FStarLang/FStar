module RewriteFail
#lang-pulse
open Pulse.Lib.Pervasives

// Rewrite with incompatible propositions
[@@expect_failure [19]]
fn rewrite_fail (r: ref int)
  requires pts_to r 0
  ensures pts_to r 1
{
  rewrite (pts_to r 0) as (pts_to r 1);  // ERROR: can't rewrite, not equivalent
  ()
}
