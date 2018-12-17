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
module PureParser

open KeyValue
open Parsing
open IntegerParsing

open FStar.Seq
open FStar.Kremlin.Endianness
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(*** Spec-level pure parsing to values *)

val parse_entry : parser encoded_entry
let parse_entry =
  parse_u16_array `and_then`
  (fun key -> parse_u32_array `and_then`
  (fun value ->
  parse_ret (EncodedEntry key.len16 key.a16 value.len32 value.a32)))

let parse_abstract_store : parser store =
  parse_u32 `and_then`
  (fun num_entries -> parse_many parse_entry (U32.v num_entries) `and_then`
  (fun entries -> parsing_done `and_then`
  (fun _ -> parse_ret (Store num_entries entries))))

let parse_entries (num_entries:U32.t) : parser store =
  parse_many parse_entry (U32.v num_entries) `and_then`
  (fun entries -> parsing_done `and_then`
  (fun _ -> parse_ret (Store num_entries entries)))
