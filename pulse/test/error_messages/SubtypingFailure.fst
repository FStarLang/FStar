module SubtypingFailure
#lang-pulse
open Pulse.Lib.Pervasives

// Subtyping failure in function argument
fn callee (x: nat)
  requires emp
  ensures emp
{
  ()
}

[@@expect_failure [19]]
fn caller (x: int)
  requires emp
  ensures emp
{
  callee x
}
