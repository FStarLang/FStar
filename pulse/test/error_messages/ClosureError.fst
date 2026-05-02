module ClosureError
#lang-pulse
open Pulse.Lib.Pervasives

// Error in a local function definition
[@@expect_failure [19]]
fn closure_error (r: ref int)
  requires pts_to r 0
  ensures pts_to r 0
{
  fn helper ()
    requires pts_to r 1  // ERROR: pre says r==1 but caller has r==0
    ensures pts_to r 1
  {
    ()
  };
  helper ();
  ()
}
