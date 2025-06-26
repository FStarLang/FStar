module Preserves

#lang-pulse
open Pulse.Nolib

assume val foo : int -> slprop
assume val bar : int -> slprop

fn usefoo (x:int)
  requires foo x
  ensures emp
{
  admit()
}

fn usebar (x:int)
  requires bar x
  ensures emp
{
  admit()
}

#push-options "--no_smt"

fn test1 ()
  preserves foo 1 ** bar 2
{
  ();
}

fn test2 ()
  preserves foo 1
  requires foo 2
{
  usefoo 2;
}

fn test3 ()
  preserves bar 2
  ensures foo 1
{
  assume (foo 1);
}

fn test4 ()
  preserves foo 2 ** foo 1
{
  ();
}
