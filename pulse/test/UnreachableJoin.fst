module UnreachableJoin
open Pulse
#lang-pulse

fn if_then_unreachable (x: ref nat)
  preserves x |-> 'vx
  requires pure (!x >= 42)
  returns y : nat
  ensures pure (y == !x)
{
  if (!x < 10) {
    x := 0;
    unreachable ();
  };

  !x
}