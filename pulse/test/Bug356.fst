module Bug356
#lang-pulse
open Pulse.Nolib

fn test (b : bool)
  returns x : UInt32.t
{
  if (b) {
    1ul;
  } else {
    admit();
    2ul;
  }
}

fn test_final_admit (b : bool)
  returns x : UInt32.t
{
  if (b) {
    1ul;
  } else {
    admit();
  }
}

fn test_unit_admit (x: bool)
{
  admit ();
  let _ = test x;
  ()
}