module LambdaArg
#lang-pulse
open Pulse.Lib.Pervasives

// Passing wrong number of arguments
fn takes_two (x y: int)
  requires emp
  ensures emp
{
  ()
}

[@@expect_failure [71]]
fn wrong_args ()
  requires emp
  ensures emp
{
  takes_two 1 2 3;  // ERROR: too many arguments
  ()
}
