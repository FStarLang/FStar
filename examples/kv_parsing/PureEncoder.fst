module PureEncoder

open FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module List = FStar.List.Tot

open KeyValue
open Serializing
open IntegerParsing

(*! Serializing a key-value store *)

val encode_entry: encoded_entry -> bytes
let encode_entry e = encode_u16_array e.key_len e.key `append`
                     encode_u32_array e.val_len e.value

val encode_store : s:store -> bytes
let encode_store s =
  encode_u32 (s.num_entries) `append`
  encode_many s.entries encode_entry (U32.v s.num_entries)
