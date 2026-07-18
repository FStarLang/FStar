(*
   Copyright 2023 Microsoft Research

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

module CBOR.Pulse.Type

open Pulse.Lib.Pervasives

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module A = Pulse.Lib.Array

(* The C datatype for CBOR objects *)

noeq
type cbor_int = {
  cbor_int_type: Cbor.major_type_uint64_or_neg_int64;
  cbor_int_value: U64.t;
}

noeq
type cbor_string = {
  cbor_string_type: Cbor.major_type_byte_string_or_text_string;
  cbor_string_length: U64.t;
  cbor_string_payload: A.array U8.t;
}

val cbor_map_entry: Type0

val cbor: Type0

val cbor_array_iterator_t: Type0

val cbor_map_iterator_t: Type0
