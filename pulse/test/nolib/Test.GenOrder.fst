
module Test.GenOrder

#lang-pulse
open Pulse.Nolib

assume val foo : int -> int -> slprop

fn flip ()
  requires foo 'x 'y
  ensures  foo 'y 'x
{ admit(); }

fn test ()
  requires foo 1 2
  ensures  foo 2 1
{
  flip () #1 #2;
}
