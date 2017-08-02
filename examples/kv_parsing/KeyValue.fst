module KeyValue

open FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module List = FStar.List.Tot

type byte = FStar.UInt8.byte
type bytes = seq byte

open Slice

(*** Binary key-value store parsing ***)

(** We define a simple encoding of a key-value store with variable-length keys
    and values (both byte arrays). So far the experiments here concern parsing
    the key-value store by validating it and then locating keys and values on
    access, using pointers to the input data rather than copying values. *)

type entry: Type0 =
  { key: bytes;
    value: bytes; }

type abstract_store = seq entry

// goal: validate a sequence of bytes to establish a refinement that makes
// reading it later work

(* the binary format of the key-value store is as follows:
   - the number of entries (uint32)
   - variable-length entries consisting of:
     - the key length, in bytes (uint16)
     - the key data
     - the value length, in bytes (uint32)
       the value data

  Validating this format boils down to checking that the number of entries lines up with the sum of the key-value entry lengths, when parsed sequentially.
*)

type encoded_entry =
  | EncodedEntry:
    key_len: U16.t ->
    key: bytes{length key == U16.v key_len} ->
    val_len: U32.t ->
    value: bytes{length value == U32.v val_len} ->
    encoded_entry

type store =
  | Store :
    num_entries:U32.t ->
    entries:list encoded_entry{List.length entries == U32.v num_entries} ->
    store

// TODO: clearly encoded_entry should have a u16_array and a u32_array

type u16_array =
  | U16Array : len16:U16.t -> a16:bytes{length a16 == U16.v len16} -> u16_array

type u32_array =
  | U32Array : len32:U32.t -> a32:bytes{length a32 == U32.v len32} -> u32_array

noeq type u16_array_st =
  | U16ArraySt : len16_st:U16.t -> a16_st:bslice{U32.v a16_st.len == U16.v len16_st} -> u16_array_st

noeq type u32_array_st =
  | U32ArraySt : len32_st:U32.t -> a32_st:bslice{U32.v a32_st.len == U32.v len32_st} -> u32_array_st

// an entry with buffers instead of bytes
noeq type entry_st =
  | EntrySt: key_st:u16_array_st ->
              val_st:u32_array_st ->
              entry_st

let entry_live h (e:entry_st) =
    live h e.key_st.a16_st /\
    live h e.val_st.a32_st

let as_u16_array h (a:u16_array_st) : Ghost u16_array
  (requires (live h a.a16_st))
  (ensures (fun _ -> True)) =
  U16Array a.len16_st (as_seq h a.a16_st)

let as_u32_array h (a:u32_array_st) : Ghost u32_array
  (requires (live h a.a32_st))
  (ensures (fun _ -> True)) =
  U32Array a.len32_st (as_seq h a.a32_st)

let as_entry h (e:entry_st) : Ghost encoded_entry
  (requires (entry_live h e))
  (ensures (fun _ -> True)) =
  let key = as_u16_array h e.key_st in
  let value = as_u32_array h e.val_st in
  EncodedEntry key.len16 key.a16
               value.len32 value.a32
