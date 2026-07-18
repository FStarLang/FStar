module PulseRespectIx4

#lang-pulse
open Pulse

// Swapped order: bar defined before foo.
// Interface checking should match by name, not position.

ghost
fn bar ()
  ensures emp
{ (); }

#lang-pulse
open Pulse

[@@expect_failure]
ghost
fn foo ()
  requires pure False
  ensures pure False
{ (); }
