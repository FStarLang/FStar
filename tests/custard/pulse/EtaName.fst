module EtaName
#lang-pulse
open Pulse
module A  = Pulse.Lib.Array
module U32 = FStar.UInt32
module U8 = FStar.UInt8

fn encrypt (key: U8.t) (nonce: U8.t) (ctr: U32.t)
  returns r: U8.t
{
  U8.add_mod key (U8.add_mod nonce (FStar.Int.Cast.uint32_to_uint8 ctr))
}

fn decrypt (key: U8.t) (nonce: U8.t) (ctr: U32.t)
  returns r: U8.t
{
  encrypt key nonce ctr
}

(* The wrapper's own binder is called [nonce] too, and the name it inherits
   for the next position is also [nonce].  {!Rename.pick} settles it by
   counting rather than by capturing. *)
fn clash (ctr: U8.t) (nonce: U8.t) (c: U32.t)
  returns r: U8.t
{
  encrypt ctr nonce c
}

fn main ()
  returns x: FStar.Int32.t
{
  let a = decrypt 1uy 2uy 3ul;
  let b = clash 1uy 4uy 5ul;
  if (U8.eq a 6uy && U8.eq b 10uy) { 0l } else { 1l }
}
