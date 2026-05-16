module IfCondType
#lang-pulse
open Pulse.Lib.Pervasives

// If condition that's not a bool
[@@expect_failure [189]]
fn bad_if_cond (x: int)
  requires emp
  ensures emp
{
  if x { () } else { () };
  ()
}
