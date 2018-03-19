module LowParse.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8

type byte = U8.byte
type bytes = Seq.seq byte
