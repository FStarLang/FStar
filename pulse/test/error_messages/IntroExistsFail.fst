module IntroExistsFail
#lang-pulse
open Pulse.Lib.Pervasives

// Existential introduction with wrong witness
[@@expect_failure [19]]
fn intro_exists_fail (r: ref int)
  requires pts_to r 0
  ensures (exists* v. pts_to r v ** pure (v > 0))
{
  ()  // ERROR: can't prove exists* v. pts_to r v ** pure (v > 0)
}
