module RewriteNopWarning

#lang-pulse
open Pulse.Nolib

assume val foo : int -> slprop

(* The rewrite is a nop. *)
fn test1 (y : int)
  preserves foo 1
{
  rewrite each y as 1;
}

(* Same *)
fn test2 (y : int) (z : int)
  preserves foo 1 ** foo y
{
  rewrite each z as 42;
}

