(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
