module PulseRespectIx3

#lang-pulse
open Pulse

// Postcondition mismatch: impl promises emp but interface promises pure (1 == 2)
[@@expect_failure]
ghost
fn foo ()
  ensures emp
{ (); }
