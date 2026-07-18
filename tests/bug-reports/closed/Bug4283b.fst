module Bug4283b

#lang-pulse
open Pulse

assume val a : int -> slprop
assume val b : int -> slprop
assume val c : int -> slprop

assume val lem (x : int) : b x == c x

[@@pulse_intro]
ghost
fn a_to_b (x : int)
  requires a x
  ensures b x
{
  admit();
}

fn test (x : int)
  requires a x
  ensures c x
{
  lem x;
  ();
  (* a_to_b x; *)
  rewrite b x as c x;
  ()
}
