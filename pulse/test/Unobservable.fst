module Unobservable

#lang-pulse
open Pulse

assume val foo : slprop

unobservable
fn incr (x : int)
  preserves foo
  returns int
{
  (x+1)
}

atomic fn test ()
  preserves foo
  returns int
{
  let x = incr 1;
  let x = incr x;
  x
}

unobservable
fn test2 ()
  preserves foo
  returns int
{
  let x = incr 1;
  x
}

[@@expect_failure]
unobservable
fn test3 ()
  preserves foo
  returns int
{
  let x = test ();
  x
}
