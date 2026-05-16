module MutualExcl
#lang-pulse
open Pulse.Lib.Pervasives

// Postcondition has emp but function body leaves resources behind
[@@expect_failure [228]]
fn mutual_excl (r: ref int)
  requires pts_to r 0
  ensures emp
{
  ()  // ERROR: pts_to r 0 is leftover, postcondition is emp
}
