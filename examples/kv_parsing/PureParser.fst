module PureParser

open KeyValue
open Parsing

open FStar.Seq
open FStar.Kremlin.Endianness
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(*** Spec-level pure parsing to values *)

let parse_u8: parser U8.t =
  fun b -> if length b < 1 then None
        else Some (index b 0, 1)

let parse_u16: parser U16.t =
  fun b -> if length b < 2 then None
        else begin
          let b' = slice b 0 2 in
          lemma_be_to_n_is_bounded b';
          Some (U16.uint_to_t (be_to_n b'), 2)
        end

let parse_u32: parser U32.t =
  fun b -> if length b < 4 then None
        else begin
          let b' = slice b 0 4 in
          lemma_be_to_n_is_bounded b';
          Some (U32.uint_to_t (be_to_n b'), 4)
        end

val parse_u16_array: parser u16_array
let parse_u16_array =
  parse_u16 `and_then`
  (fun array_len b' ->
    if length b' < U16.v array_len then None
    else let data = slice b' 0 (U16.v array_len) in
    Some (U16Array array_len data, U16.v array_len))

val parse_u32_array: parser u32_array
let parse_u32_array =
  parse_u32 `and_then`
  (fun array_len b' ->
    if length b' < U32.v array_len then None
    else let data = slice b' 0 (U32.v array_len) in
    Some (U32Array array_len data, U32.v array_len))

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
