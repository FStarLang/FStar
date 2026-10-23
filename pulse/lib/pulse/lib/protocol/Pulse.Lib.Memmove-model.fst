module Pulse.Lib.Memmove

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

(* Model implementation of Pulse.Lib.Memmove: verified, but never extracted
   (the C implementation, a call to memmove, is
   pulse/share/pulse/runtime/Pulse_Lib_Memmove_runtime.c).  It copies in place,
   front to back when the destination is at or before the source and back to
   front otherwise, so that no byte is overwritten before it has been read. *)

let moved (before after: Seq.seq U8.t) (dst src len: nat) : prop =
  dst + len <= Seq.length before /\
  src + len <= Seq.length before /\
  Seq.length after == Seq.length before /\
  Seq.equal (Seq.slice after 0 dst) (Seq.slice before 0 dst) /\
  Seq.equal (Seq.slice after dst (dst + len)) (Seq.slice before src (src + len)) /\
  Seq.equal (Seq.slice after (dst + len) (Seq.length after))
            (Seq.slice before (dst + len) (Seq.length before))

let moved_intro (before after: Seq.seq U8.t) (dst src len: nat)
  : Lemma
    (requires
      dst + len <= Seq.length before /\
      src + len <= Seq.length before /\
      Seq.length after == Seq.length before /\
      (forall (k:nat). k < dst ==> Seq.index after k == Seq.index before k) /\
      (forall (j:nat). j < len ==> Seq.index after (dst + j) == Seq.index before (src + j)) /\
      (forall (k:nat). dst + len <= k /\ k < Seq.length before ==>
                       Seq.index after k == Seq.index before k))
    (ensures moved before after dst src len)
  = assert (forall (j:nat). j < len ==>
              Seq.index (Seq.slice after dst (dst + len)) j == Seq.index after (dst + j));
    assert (forall (j:nat). j < len ==>
              Seq.index (Seq.slice before src (src + len)) j == Seq.index before (src + j))

fn copy_forward
  (buffer:array U8.t) (dst_offset src_offset len:SZ.t)
  (#before: erased (Seq.seq U8.t))
  requires pts_to buffer before **
           pure (SZ.v dst_offset <= SZ.v src_offset /\
                 SZ.v dst_offset + SZ.v len <= Seq.length before /\
                 SZ.v src_offset + SZ.v len <= Seq.length before)
  ensures exists* after. pts_to buffer after **
          pure (moved before after (SZ.v dst_offset) (SZ.v src_offset) (SZ.v len))
{
  pts_to_len buffer;
  let mut i = 0sz;
  while (!i `SZ.lt` len)
  invariant exists* (vi:SZ.t) (s:Seq.seq U8.t).
    pts_to i vi **
    pts_to buffer s **
    pure (SZ.v vi <= SZ.v len /\
          Seq.length s == Seq.length before /\
          (forall (k:nat). k < SZ.v dst_offset ==> Seq.index s k == Seq.index before k) /\
          (forall (j:nat). j < SZ.v vi ==>
             Seq.index s (SZ.v dst_offset + j) == Seq.index before (SZ.v src_offset + j)) /\
          (forall (k:nat). SZ.v dst_offset + SZ.v vi <= k /\ k < Seq.length s ==>
             Seq.index s k == Seq.index before k))
  decreases (SZ.v len - SZ.v !i)
  {
    let vi = !i;
    let b = buffer.(src_offset `SZ.add` vi);
    buffer.(dst_offset `SZ.add` vi) <- b;
    i := vi `SZ.add` 1sz;
  };
  with s. assert (pts_to buffer s);
  moved_intro before s (SZ.v dst_offset) (SZ.v src_offset) (SZ.v len);
}

fn copy_backward
  (buffer:array U8.t) (dst_offset src_offset len:SZ.t)
  (#before: erased (Seq.seq U8.t))
  requires pts_to buffer before **
           pure (SZ.v src_offset < SZ.v dst_offset /\
                 SZ.v dst_offset + SZ.v len <= Seq.length before /\
                 SZ.v src_offset + SZ.v len <= Seq.length before)
  ensures exists* after. pts_to buffer after **
          pure (moved before after (SZ.v dst_offset) (SZ.v src_offset) (SZ.v len))
{
  pts_to_len buffer;
  let mut i = len;
  while (0sz `SZ.lt` !i)
  invariant exists* (vi:SZ.t) (s:Seq.seq U8.t).
    pts_to i vi **
    pts_to buffer s **
    pure (SZ.v vi <= SZ.v len /\
          Seq.length s == Seq.length before /\
          (forall (k:nat). k < SZ.v dst_offset + SZ.v vi ==> Seq.index s k == Seq.index before k) /\
          (forall (j:nat). SZ.v vi <= j /\ j < SZ.v len ==>
             Seq.index s (SZ.v dst_offset + j) == Seq.index before (SZ.v src_offset + j)) /\
          (forall (k:nat). SZ.v dst_offset + SZ.v len <= k /\ k < Seq.length s ==>
             Seq.index s k == Seq.index before k))
  decreases (SZ.v !i)
  {
    let vi = !i;
    let j = vi `SZ.sub` 1sz;
    let b = buffer.(src_offset `SZ.add` j);
    buffer.(dst_offset `SZ.add` j) <- b;
    i := j;
  };
  with s. assert (pts_to buffer s);
  moved_intro before s (SZ.v dst_offset) (SZ.v src_offset) (SZ.v len);
}

fn memmove
  (buffer:array U8.t)
  (dst_offset:SZ.t)
  (src_offset:SZ.t)
  (len:SZ.t)
  requires pts_to buffer 'before **
           pure (SZ.v dst_offset + SZ.v len <= Seq.length 'before /\
                 SZ.v src_offset + SZ.v len <= Seq.length 'before)
  ensures exists* after.
          pts_to buffer after **
          pure (SZ.v dst_offset + SZ.v len <= Seq.length (Ghost.reveal 'before) /\
                SZ.v src_offset + SZ.v len <= Seq.length (Ghost.reveal 'before) /\
                Seq.length after == Seq.length (Ghost.reveal 'before) /\
                Seq.equal
                  (Seq.slice after 0 (SZ.v dst_offset))
                  (Seq.slice (Ghost.reveal 'before) 0 (SZ.v dst_offset)) /\
                Seq.equal
                  (Seq.slice
                    after
                    (SZ.v dst_offset)
                    (SZ.v dst_offset + SZ.v len))
                  (Seq.slice
                    (Ghost.reveal 'before)
                    (SZ.v src_offset)
                    (SZ.v src_offset + SZ.v len)) /\
                Seq.equal
                  (Seq.slice
                    after
                    (SZ.v dst_offset + SZ.v len)
                    (Seq.length after))
                  (Seq.slice
                    (Ghost.reveal 'before)
                    (SZ.v dst_offset + SZ.v len)
                    (Seq.length (Ghost.reveal 'before))))
{
  if (dst_offset `SZ.lte` src_offset) {
    copy_forward buffer dst_offset src_offset len;
  } else {
    copy_backward buffer dst_offset src_offset len;
  }
}
