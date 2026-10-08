module Calc.Impl.Parser

#lang-pulse

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Cast = FStar.Int.Cast

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec

open Calc.Wire

(** Parse request tag from buffer **)
fn parse_tag (buf: Vec.vec U8.t)
  requires Vec.pts_to buf 'bytes ** pure (Seq.length 'bytes == 5)
  returns tag: U8.t
  ensures Vec.pts_to buf 'bytes ** pure (Seq.length 'bytes == 5 /\ tag == Seq.index 'bytes 0)
{
  Vec.op_Dot_Lparen_Rparen buf 0sz
}

(** Parse Push value from bytes 1-4 (big-endian U32) **)
fn parse_push_value (buf: Vec.vec U8.t)
  requires Vec.pts_to buf 'bytes ** pure (Seq.length 'bytes == 5)
  returns value: U32.t
  ensures Vec.pts_to buf 'bytes **
          pure (Seq.length 'bytes == 5 /\
                U32.v value == Calc.Wire.Lemmas.be_to_n_unrefined
                  (Seq.index 'bytes 1)
                  (Seq.index 'bytes 2)
                  (Seq.index 'bytes 3)
                  (Seq.index 'bytes 4))
{
  let b1 = Vec.op_Dot_Lparen_Rparen buf 1sz;
  let b2 = Vec.op_Dot_Lparen_Rparen buf 2sz;
  let b3 = Vec.op_Dot_Lparen_Rparen buf 3sz;
  let b4 = Vec.op_Dot_Lparen_Rparen buf 4sz;
  let v0 : U32.t = Cast.uint8_to_uint32 b1;
  let v1 : U32.t = Cast.uint8_to_uint32 b2;
  let v2 : U32.t = Cast.uint8_to_uint32 b3;
  let v3 : U32.t = Cast.uint8_to_uint32 b4;
  
  // Call lemmas to prove correspondence
  Calc.Wire.Lemmas.lemma_parse_push_value_correct b1 b2 b3 b4 (Seq.slice 'bytes 1 5);
  Calc.Wire.Lemmas.lemma_be_to_n_equiv (Seq.slice 'bytes 1 5);
  Calc.Wire.Lemmas.lemma_u32_arithmetic_correspondence v0 v1 v2 v3;
  
  U32.add (U32.add (U32.mul v0 16777216ul) (U32.add (U32.mul v1 65536ul) (U32.mul v2 256ul))) v3
}
