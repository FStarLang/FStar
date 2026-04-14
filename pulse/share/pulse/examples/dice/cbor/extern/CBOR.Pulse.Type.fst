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

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference

inline_for_extraction noextract
let cbor_serialized_payload_t = A.array U8.t

[@@no_auto_projectors]
noeq
type cbor_serialized = {
  cbor_serialized_size: SZ.t;
  cbor_serialized_payload: cbor_serialized_payload_t;
}

[@@no_auto_projectors]
noeq
type cbor_tagged0 = {
  cbor_tagged0_tag: U64.t;
  cbor_tagged0_payload: R.ref cbor;
}

and cbor_array = {
  cbor_array_length: U64.t;
  cbor_array_payload: A.array cbor;
}

and cbor_map_entry = {
  cbor_map_entry_key: cbor;
  cbor_map_entry_value: cbor;
}

and cbor_map = {
  cbor_map_length: U64.t;
  cbor_map_payload: A.array cbor_map_entry;
}

and cbor =
| CBOR_Case_Int64:
  v: cbor_int ->
  cbor
| CBOR_Case_String:
  v: cbor_string ->
  cbor
| CBOR_Case_Tagged:
  v: cbor_tagged0 ->
  cbor
| CBOR_Case_Array:
  v: cbor_array ->
  cbor
| CBOR_Case_Map:
  v: cbor_map ->
  cbor
| CBOR_Case_Simple_value:
  v: Cbor.simple_value ->
  cbor
| CBOR_Case_Serialized:
  v: cbor_serialized ->
  cbor

[@@no_auto_projectors]
noeq
type cbor_array_iterator_payload_t =
| CBOR_Array_Iterator_Payload_Array:
    payload: A.array cbor ->
    cbor_array_iterator_payload_t
| CBOR_Array_Iterator_Payload_Serialized:
    payload: cbor_serialized_payload_t ->
    cbor_array_iterator_payload_t

[@@no_auto_projectors]
noeq
type cbor_array_iterator_t = {
  cbor_array_iterator_length: U64.t;
  cbor_array_iterator_payload: cbor_array_iterator_payload_t;
}

[@@no_auto_projectors]
noeq
type cbor_map_iterator_payload_t =
| CBOR_Map_Iterator_Payload_Map:
    payload: A.array cbor_map_entry ->
    cbor_map_iterator_payload_t
| CBOR_Map_Iterator_Payload_Serialized:
    payload: cbor_serialized_payload_t ->
    cbor_map_iterator_payload_t

// NOTE: this type could be made abstract (with val and
// CAbstractStruct, and then hiding cbor_array_iterator_payload_t
// altogether), but then, users couldn't allocate on stack
[@@no_auto_projectors]
noeq
type cbor_map_iterator_t = {
  cbor_map_iterator_length: U64.t;
  cbor_map_iterator_payload: cbor_map_iterator_payload_t;
}
