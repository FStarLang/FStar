module ReturnImplicit
#lang-pulse
open Pulse.Lib.Pervasives

// Return type annotation mismatch with body
[@@expect_failure [19]]
fn return_impl ()
  requires emp
  returns r: nat
  ensures emp
{
  -1  // ERROR: -1 is not nat
}
