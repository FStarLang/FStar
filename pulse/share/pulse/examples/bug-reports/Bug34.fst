module Bug34
#lang-pulse

open Pulse.Lib.Pervasives

class eq (a:Type) = {
  (=?) : a -> a -> bool
}

instance eq_int : eq int = {
  (=?) = (=);
}


fn test (#a:Type0) {| eq a |} (x:a)
  requires emp
  returns _:bool
  ensures emp
{
  (x =? x)
}



fn call ()
  requires emp
  ensures  emp
{
  let x : bool = test 123;
  ()
}

