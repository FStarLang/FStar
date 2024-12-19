module RevealHide
#lang-pulse

open Pulse.Lib.Pervasives

assume val p : int -> slprop


fn test0 (x:int)
  requires p x
  ensures  p (reveal (hide x))
{
  ()
}



fn test1 (x:int)
  requires p (reveal (hide x))
  ensures  p x
{
  ()
}

