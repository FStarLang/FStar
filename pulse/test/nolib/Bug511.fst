module Bug511
open Pulse.Nolib
#lang-pulse

let p () = emp

ghost fn exists_unit ()
  ensures exists* x. p x
{
  fold p ();
}
