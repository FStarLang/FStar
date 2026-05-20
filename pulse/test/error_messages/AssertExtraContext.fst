module AssertExtraContext
#lang-pulse
open Pulse.Lib.Pervasives

// Assert with binders where the witness is wrong
[@@expect_failure [19]]
fn assert_extra (r: ref int)
  requires pts_to r 0
  ensures pts_to r 0
{
  with v. assert (pts_to r v ** pure (v > 0));
  ()
}
