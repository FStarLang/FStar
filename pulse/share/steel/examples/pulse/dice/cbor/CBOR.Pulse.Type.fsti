module CBOR.Pulse.Type

open Pulse.Lib.Pervasives

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
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

inline_for_extraction
noextract
val dummy_cbor : cbor

inline_for_extraction
noextract
val cbor_map_entry_key: cbor_map_entry -> cbor

inline_for_extraction
noextract
val cbor_map_entry_value: cbor_map_entry -> cbor

val cbor_map_entry_key_value_inj
  (m1 m2: cbor_map_entry)
: Lemma
  (requires (
    cbor_map_entry_key m1 == cbor_map_entry_key m2 /\
    cbor_map_entry_value m1 == cbor_map_entry_value m2
  ))
  (ensures (m1 == m2))
  [SMTPatOr [
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_value m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_value m2)];
  ]]

inline_for_extraction
noextract
val mk_cbor_map_entry
  (key: cbor)
  (value: cbor)
: Pure cbor_map_entry
  (requires True)
  (ensures (fun res ->
    cbor_map_entry_key res == key /\
    cbor_map_entry_value res == value
  ))

val cbor_array_iterator_t: Type0
