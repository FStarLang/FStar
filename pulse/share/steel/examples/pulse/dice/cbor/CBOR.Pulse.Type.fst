module CBOR.Pulse.Type

inline_for_extraction noextract
let cbor_serialized_payload_t = A.array U8.t

noeq
type cbor_serialized = {
  cbor_serialized_size: SZ.t;
  cbor_serialized_payload: cbor_serialized_payload_t;
}

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

let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy

let cbor_map_entry_key = Mkcbor_map_entry?.cbor_map_entry_key
let cbor_map_entry_value = Mkcbor_map_entry?.cbor_map_entry_value

let cbor_map_entry_key_value_inj
  m1 m2
= ()

let mk_cbor_map_entry
  k v
= Mkcbor_map_entry k v

noeq
type cbor_array_iterator_payload_t =
| CBOR_Array_Iterator_Payload_Array:
    payload: A.array cbor ->
    cbor_array_iterator_payload_t
| CBOR_Array_Iterator_Payload_Serialized:
    payload: cbor_serialized_payload_t ->
    cbor_array_iterator_payload_t

noeq
type cbor_array_iterator_t = {
  cbor_array_iterator_length: U64.t;
  cbor_array_iterator_payload: cbor_array_iterator_payload_t;
}

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
noeq
type cbor_map_iterator_t = {
  cbor_map_iterator_length: U64.t;
  cbor_map_iterator_payload: cbor_map_iterator_payload_t;
}