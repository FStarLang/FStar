module Unfold
#lang-pulse

open Pulse.Lib.Pervasives

assume
val p : slprop

[@@pulse_unfold]
let q = p


fn test_pq ()
  requires p
  ensures q
{
  ();
}



fn test_qp ()
  requires q
  ensures p
{
  ();
}

