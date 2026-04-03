module ExtractUninit
open Pulse
#lang-pulse

fn uninit_ref ()
  returns i: UInt32.t
  ensures pure (i == 32ul)
{
  let mut r : UInt32.t;
  r := 3ul;
  let res = (!r) `UInt32.add` 29ul;
  res
}

fn uninit_array ()
  returns i: UInt32.t
  ensures pure (i == 6ul)
{
  let mut arr : array UInt32.t = [| 5sz |];
  mask_write arr 1sz 2ul;
  mask_write arr 3sz 4ul;
  (mask_read arr 1sz) `UInt32.add` (mask_read arr 3sz)
}