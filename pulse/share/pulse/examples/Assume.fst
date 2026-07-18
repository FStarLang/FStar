module Assume

#lang-pulse
open Pulse

assume val foo : int -> slprop

fn test0 (x:int)
  ensures foo 1
{
  assume foo 1;
}

[@@expect_failure]
fn test1 (x:int)
  ensures foo 1
{
  with a. assume foo 1;
}

fn test2 (x:int)
  ensures foo 1
  ensures foo 2
{
  assume foo 1;
  assume foo 2;
}

[@@expect_failure]
fn test3 (x:int)
  ensures foo 1
  ensures foo 2
{
  assume foo 2;
}
