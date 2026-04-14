module Bug416

#lang-pulse

open Pulse.Nolib

assume val ref : int -> prop
assume val foo : x:int{ref x} -> slprop

[@@expect_failure [19]]
ghost
fn test (_ : squash (ref 1))
  requires foo 1
  ensures          foo 2
{
  admit ()
}
