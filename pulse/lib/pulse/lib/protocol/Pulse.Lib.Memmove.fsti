module Pulse.Lib.Memmove

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

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
