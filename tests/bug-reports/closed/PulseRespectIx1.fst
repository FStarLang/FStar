module PulseRespectIx1

#lang-pulse
open Pulse

[@@expect_failure]
ghost
fn foo ()
  requires pure False
  ensures pure False
{ (); }
