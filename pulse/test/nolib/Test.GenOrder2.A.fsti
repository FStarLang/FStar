module Test.GenOrder2.A

#lang-pulse
open Pulse.Nolib

val foo : int -> int -> slprop

fn flip ()
  requires foo 'x 'y
  ensures  foo 'y 'x
