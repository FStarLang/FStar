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
assume val g : x:int -> y:int{f y == x}

let rel2 x = rel (g (f x))

fn test1 (x : _)
  requires trade emp (rel2 x)
  ensures  trade emp (rel (g (f x)))
{
  ();
}

fn test2 (x : _)
  requires trade emp (rel (g (f x)))
  ensures  trade emp (rel2 x)
{
  ();
}

fn test3 (y : _)
  requires trade emp (rel (g y))
  ensures  trade emp (rel2 (g y))
{
  rewrite each y as f (g y); // ideally automated
  ();
}

fn test4 (y : _)
  requires trade emp (rel2 (g y))
  ensures  trade emp (rel (g y))
{
  rewrite each rel2 (g y) as rel (g (f (g y))); // ideally automated?
  ();
}
