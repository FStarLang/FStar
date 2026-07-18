module FailAssertion
#lang-pulse
open Pulse.Lib.Pervasives

// Failing assertion: error should point to the assert line
[@@expect_failure [228]]
fn test_fail_assert (x: int)
  requires emp
  ensures emp
{
  assert (x > 0);
  ()
}
