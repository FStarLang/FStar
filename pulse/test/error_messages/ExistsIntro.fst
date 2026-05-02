module ExistsIntro
#lang-pulse
open Pulse.Lib.Pervasives

// Postcondition requires existential that can't be satisfied
[@@expect_failure [19]]
fn exists_intro_fail (r: ref int)
  requires pts_to r 5
  ensures exists* v. pts_to r v ** pure (v > 10)
{
  // ERROR: after body, we have pts_to r 5 but need v > 10
  ()
}
