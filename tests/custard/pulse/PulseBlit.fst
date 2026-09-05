module PulseBlit
#lang-pulse
open Pulse
module A  = Pulse.Lib.Array
module AP = Pulse.Lib.ArrayPtr
module US = FStar.SizeT
module U8 = FStar.UInt8

(* Section 41.1.  Pulse.Lib.ArrayPtr.memcpy is the sole source of the IR's
   [BufBlit], and until this file nothing in either suite called it, so the
   printer case had never printed anything and section 35.2's sweep had
   nothing to look at.  The length position is where a redundant pair shows
   up, and it shows up exactly when the length is already a group -- a
   literal, a cast, an arithmetic expression -- which [2sz] is and a struct
   field is not.  main checks the copied bytes. *)

fn copy2 (src: AP.ptr U8.t) (dst: AP.ptr U8.t)
         (#p: perm)
         (#s0: Ghost.erased (Seq.seq U8.t) { Seq.length s0 >= 2 })
         (#s1: Ghost.erased (Seq.seq U8.t) { Seq.length s1 >= 2 })
  preserves AP.pts_to src #p s0
  requires AP.pts_to dst s1
  ensures exists* s. AP.pts_to dst s **
            pure (Seq.length s == Seq.length s1 /\
                  Seq.index s 0 == Seq.index s0 0 /\
                  Seq.index s 1 == Seq.index s0 1)
{
  AP.memcpy src 0sz dst 0sz 2sz;
}

fn main ()
  returns r:US.t
{
  let src = A.alloc 7uy 2sz;
  A.pts_to_len src;
  A.op_Dot_Lparen_Rparen_Less_Minus src 1sz 9uy;
  let dst = A.alloc 0uy 2sz;
  A.pts_to_len dst;
  let sp = AP.from_array src;
  let dp = AP.from_array dst;
  copy2 sp dp;
  AP.to_array sp src;
  AP.to_array dp dst;
  A.pts_to_len dst;
  let a = A.op_Dot_Lparen_Rparen dst 0sz;
  let b = A.op_Dot_Lparen_Rparen dst 1sz;
  A.free src;
  A.free dst;
  if (U8.(a =^ 7uy) && U8.(b =^ 9uy)) { 0sz } else { 1sz }
}
