module IllTypedSpec
#lang-pulse
open Pulse.Lib.Pervasives

// Ill-typed precondition: using an int where a vprop is expected
[@@expect_failure [189]]
fn bad_precondition (x: int)
  requires x
  ensures emp
{
  ()
}
