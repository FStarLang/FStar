module PrintCheck

#lang-pulse
open Pulse

fn test (x : ref int)
  requires x |-> 'v
  returns  old : int
  ensures  x |-> ('v + 1) ** pure (old == old)
{
  let old = !x;
  x := !x + 1;
  old
}
#check test

assume val q : int -> slprop
assume val test2 : stt_ghost int emp_inames emp q

#check test2

assume val r : unit -> slprop
assume val test3 : stt_ghost unit emp_inames emp r

#check test3
