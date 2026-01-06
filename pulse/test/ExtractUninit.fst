module ExtractUninit
open Pulse
#lang-pulse

fn uninit_ref ()
  returns i: UInt32.t
  ensures pure (i == 32ul)
{
  let r = Pulse.Lib.Reference.alloc_uninit UInt32.t ();
  r := 3ul;
  let res = (!r) `UInt32.add` 29ul;
  Pulse.Lib.Reference.free r;
  res
}

fn uninit_array ()
  returns i: UInt32.t
  ensures pure (i == 6ul)
{
  let arr = mask_alloc UInt32.t 5sz;
  mask_write arr 0sz 1ul;
  mask_write arr 1sz 2ul;
  mask_write arr 2sz 3ul;
  mask_write arr 3sz 4ul;
  mask_write arr 4sz 5ul;
  from_mask arr;
  let result = arr.(1sz) `UInt32.add` arr.(3sz);
  Pulse.Lib.Array.free arr;
  result
}