module LeftoverResources
#lang-pulse
open Pulse.Lib.Pervasives

// Leftover resources: postcondition doesn't consume everything
[@@expect_failure [228]]
fn leftover (r s: ref int)
  requires pts_to r 0 ** pts_to s 0
  ensures pts_to r 0
{
  ()  // ERROR: pts_to s 0 is leftover
}
