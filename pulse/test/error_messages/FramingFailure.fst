module FramingFailure
#lang-pulse
open Pulse.Lib.Pervasives

// Framing failure: trying to use a resource that isn't in scope
[@@expect_failure [228]]
fn framing_fail (r1 r2: ref int)
  requires pts_to r1 0
  ensures pts_to r1 1
{
  let v = !r2;
  r1 := 1;
  ()
}
