module Introduce

#lang-pulse
open Pulse.Nolib

assume val p : int -> slprop
assume val q : int -> int -> slprop

fn test ()
  requires p 1
  ensures  exists* (v:int). p v
{
  introduce exists* (v:int). p v with _;
  ()
}

fn test2 ()
  requires p 1
  ensures  exists* (v:int). p v
{
  introduce exists* (v:int). p v with 1;
  ()
}

(* ambig *)
[@@expect_failure]
fn test3 ()
  requires p 1 ** p 2
  ensures  exists* (v:int). p v
{
  introduce exists* (v:int). p v with _;
  drop_ (p 1);
  ()
}

fn test4 ()
  requires p 1 ** p 2
  ensures  exists* (v:int). p v
{
  introduce exists* (v:int). p v with 2;
  drop_ (p 1);
  ()
}

(* NOTE: This fails with a unit after it, which is pretty bad. *)
fn test5 ()
  requires q 1 2
  ensures  exists* v1 v2. q v1 v2
{
  introduce exists* v1 v2. q v1 v2 with 1 2;
  // ()
}
