module VecAlloc

#lang-pulse

open Pulse
module V = Pulse.Lib.Vec

fn hf ()
{
  let v = V.alloc 1ul 100sz;
  V.free v;
  ()
}
