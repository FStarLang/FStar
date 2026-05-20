module ReturnTypeMismatch
#lang-pulse
open Pulse.Lib.Pervasives

// Returning wrong type
[@@expect_failure [189]]
fn return_wrong_type (x: int)
  requires emp
  returns r: bool
  ensures emp
{
  x
}
