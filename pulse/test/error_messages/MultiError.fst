module MultiError
#lang-pulse
open Pulse.Lib.Pervasives

// Multiple errors in sequence - check that each one is localized correctly
[@@expect_failure [19]]
fn multi_error (r: ref int)
  requires pts_to r 0
  ensures pts_to r 100
{
  r := 1;
  assert (pure (1 = 2));   // first error here
  r := 100
}
