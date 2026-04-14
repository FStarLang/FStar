module ErrCantFindWitness
#lang-pulse
open Pulse.Nolib

[@@expect_failure]
fn foo ()
  ensures exists* (x: nat). emp
{}