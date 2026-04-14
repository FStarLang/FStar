module PulseRespectIx5

#lang-pulse
open Pulse

// Non-ghost fn with precondition mismatch
[@@expect_failure]
fn foo ()
  requires pure False
  ensures pure False
{ (); }
