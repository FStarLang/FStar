module Assume

#lang-pulse
open Pulse

assume val foo : int -> slprop

fn test0 (x:int)
  requires emp
  ensures foo 1
{
  assume foo 1;
}

[@@expect_failure]
fn test1 (x:int)
  requires emp
  ensures foo 1
{
  with a. assume foo 1;
}
