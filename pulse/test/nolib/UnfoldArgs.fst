module UnfoldArgs

#lang-pulse
open Pulse.Nolib

assume
val trade
  ([@@@mkey] p : slprop)
  ([@@@mkey] q : slprop)
  : slprop

assume val rel : int -> slprop
assume val f : int -> int
assume val g : int -> int

type box a =
  | Box of a

[@@pulse_unfold]
let unbox (Box x) = x

let rel2 (Box x) = rel x

fn test1 (x : _)
  requires trade (rel x) emp
  ensures  trade (rel2 (Box x)) emp
{
  ();
}

fn test2 (x : _)
  requires trade (rel2 (Box x)) emp
  ensures  trade (rel x) emp
{
  ();
}

(*
fn test3 (x : _)
  requires (rel (unbox x))
  ensures  (rel2 x)
{
  ();
}

fn test4 (x : _)
  requires trade (rel (unbox x)) emp
  ensures  trade (rel2 x) emp
{
  ();
}
