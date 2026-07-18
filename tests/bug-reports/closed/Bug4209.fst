module Bug4209

#lang-pulse
open Pulse

assume val p : bool -> slprop
let even (x:nat) : GTot bool = x % 2 = 0
unfold let foo (x : nat) : slprop = p (even x && true)

fn test
  (x : nat)
  preserves foo x
{
  assert foo x;
  assert p (even x && true);
  ();
}
