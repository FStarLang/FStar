module CherryPulseUninit
#lang-pulse
open Pulse
module R  = Pulse.Lib.Reference

fn bad (l: list int)
  returns r: list int
{
  let p = R.alloc_uninit (list int) ();
  p := l;
  let v = !p;
  R.free p;
  v
}

fn main ()
  returns x: FStar.Int32.t
{
  let _ = bad [1];
  0l
}
