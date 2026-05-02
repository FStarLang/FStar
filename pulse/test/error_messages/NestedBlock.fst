module NestedBlock
#lang-pulse
open Pulse.Lib.Pervasives

// Error inside a nested block should point to the inner statement
[@@expect_failure [19]]
fn nested_block (r: ref int)
  requires pts_to r 0
  ensures pts_to r 0
{
  {
    assert (pts_to r 1)  // ERROR: r is 0, not 1
  };
  ()
}
