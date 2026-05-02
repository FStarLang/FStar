module WithLocalError
#lang-pulse
open Pulse.Lib.Pervasives

// Error within a with_local block
[@@expect_failure [189]]
fn with_local_err ()
  requires emp
  ensures emp
{
  let mut x = 0;
  x := 5;
  assert (pure (x == 0))  // ERROR: x is 5, not 0
}
