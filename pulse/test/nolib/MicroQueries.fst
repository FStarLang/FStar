module MicroQueries
#lang-pulse
open Pulse.Nolib

// #set-options "--ext context_pruning=false"

fn foo (x:int)
  requires pure (x > 0)
{ (); }

fn test (x:nat)
  requires pure (x > 0)
  ensures  emp
{
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
  foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x; foo x;
}
