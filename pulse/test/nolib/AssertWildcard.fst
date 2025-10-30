module AssertWildcard

#lang-pulse
open Pulse.Nolib

assume
val foo (x y z w : int) : slprop

fn test () (#x:int)
  requires foo x 'y 'z 'w
  ensures  foo x 'y 'z 'w
{
  (* obtain just y, don't care about the rest *)
  with y.
    assert foo x y _ _;
  ()
}
