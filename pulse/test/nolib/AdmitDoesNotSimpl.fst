module AdmitDoesNotSimpl

#lang-pulse
open Pulse.Nolib

assume val foo : int -> slprop

fn test (x y : int)
  requires foo (fst (x,y))
  ensures foo x
{
  admit(); (* Should show foo (fst (x,y)) *)
}

fn test2 (x y : int)
  requires foo (fst (x,y))
  ensures foo x
{
  assert foo x;
  admit(); (* Should show foo x *)
}

fn test3 ()
  requires foo (1+1)
  ensures foo 2
{
  admit(); (* Should show foo (1+1) *)
}

fn test4 ()
  requires foo (1+1)
  ensures foo 2
{
  ();
  admit(); (* Stil foo (1+1) *)
}
