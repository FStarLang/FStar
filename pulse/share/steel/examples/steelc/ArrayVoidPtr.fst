module ArrayVoidPtr

module C = Steel.ST.C.Types
module U64 = FStar.UInt64
module U8 = FStar.UInt8

let dummy = 0uL // otherwise Karamel produces no .c file

noeq
type object4_map = {
  object4_map_entry_count: U64.t;
  object4_map_payload: C.array_void_ptr;
}

noeq
type object4 = {
  object4_type: U8.t;
  object4_map: object4_map;
}

noeq
type object4_pair = {
  object4_pair_key: object4;
  object4_pair_payload: object4;
}
