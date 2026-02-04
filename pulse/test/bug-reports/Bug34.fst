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
  returns _:bool
{
  (x =? x)
}



fn call ()
{
  let x : bool = test 123;
  ()
}

