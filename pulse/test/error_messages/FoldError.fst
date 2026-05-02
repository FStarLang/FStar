module FoldError
#lang-pulse
open Pulse.Lib.Pervasives

let my_inv (r: ref int) (v: int) : slprop = pts_to r v ** pure (v >= 0)

// Trying to fold with mismatched context
[@@expect_failure [19]]
fn fold_fail (r: ref int)
  requires pts_to r (-1)
  ensures my_inv r (-1)
{
  fold (my_inv r (-1));  // ERROR: pure (v >= 0) not satisfiable with v = -1
  ()
}
