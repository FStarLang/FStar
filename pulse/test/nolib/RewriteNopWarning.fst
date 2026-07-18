module RewriteNopWarning

#lang-pulse
open Pulse.Nolib

assume val foo : int -> slprop

(* The rewrite is a nop. *)
fn test1 (y : int)
  requires pure (y == 1)
  preserves foo 1
{
  rewrite each y as 1;
}

(* Same *)
fn test2 (y : int) (z : int)
  requires pure (z == 42)
  preserves foo 1
  preserves foo y
{
  rewrite each z as 42;
}

