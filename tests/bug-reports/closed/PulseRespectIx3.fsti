module PulseRespectIx3

#lang-pulse
open Pulse

ghost
fn foo ()
  ensures pure (1 == 2)
