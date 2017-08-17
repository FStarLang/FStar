module Validator

open KeyValue
open Parsing
open PureParser
open Slice

open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST
module C = C
// special kremlin support for looping
open C.Loops

module B = FStar.Buffer

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(*** Stateful validation of input buffer *)

let parse_u8_st_nochk :
    parser_st_nochk (hide parse_u8) = fun input ->
    let b0 = B.index input.p 0ul in
    (b0, 1ul)

let parse_u8_st : parser_st (hide parse_u8) = fun input ->
    if U32.lt input.len 1ul then None
    else (Some (parse_u8_st_nochk input))

let parse_u16_st_nochk :
  parser_st_nochk (hide parse_u16) = fun input ->
  let n = C.load16_be (truncated_slice input 2ul).p in
  (n, 2ul)

let parse_u16_st : parser_st (hide parse_u16) = fun input ->
  if U32.lt input.len 2ul
    then None
  else Some (parse_u16_st_nochk input)

let parse_u32_st_nochk :
  parser_st_nochk (hide parse_u32) = fun input ->
  let n = C.load32_be (truncated_slice input 4ul).p in
  (n, 4ul)

let parse_u32_st : parser_st (hide parse_u32) = fun input ->
  if U32.lt input.len 4ul
    then None
    else Some (parse_u32_st_nochk input)


#reset-options "--z3rlimit 10"

let validate_u16_array_st : stateful_validator (hide parse_u16_array) = fun input ->
  match parse_u16_st input with
  | Some (n, off) -> begin
      let n: U32.t = Cast.uint16_to_uint32 n in
      // overflow is not possible here, since n < pow2 16 and off == 2
      // (any encodable length would fit in a U32)
      let total_len = U32.add n off in
      if U32.lt input.len total_len then None
      else Some total_len
    end
  | None -> None

inline_for_extraction
let u32_array_bound: U32.t = 4294967291ul

let u32_array_bound_is (_:unit) :
  Lemma (U32.v u32_array_bound = pow2 32 - 4 - 1) = ()

let validate_u32_array_st : stateful_validator (hide parse_u32_array) = fun input ->
  match parse_u32_st input with
  | Some (n, off) -> begin
      // we have to make sure that the total length we compute doesn't overflow
      // a U32.t to correctly check if the input is long enough
      if U32.gte n u32_array_bound then None
      else begin
        assert (U32.v n + U32.v off < pow2 32);
        let total_len = U32.add n off in
        if U32.lt input.len total_len then None
        else Some total_len
      end
    end
  | None -> None

// eta expansion is necessary to get the right subtyping check
let validate_entry_st : stateful_validator (hide parse_entry) = fun input ->
  then_check (hide parse_u16_array) validate_u16_array_st
             (hide parse_u32_array) validate_u32_array_st
             (fun key value -> EncodedEntry key.len16 key.a16 value.len32 value.a32) input

#reset-options "--z3rlimit 25"

val validate_entries_st (num_entries:U32.t) : stateful_validator (hide (parse_entries num_entries))
let validate_entries_st (num_entries:U32.t) =
  fun input ->
  // XXX: explicitly annotating this type is terrible
  then_check (elift1 (fun p -> parse_many p (U32.v num_entries)) (hide parse_entry))
  (validate_many_st (hide parse_entry) validate_entry_st num_entries)
  (hide parsing_done) validate_done_st
  (fun entries _ -> Store num_entries entries) input

let validate_store_st : stateful_validator (hide parse_abstract_store) = fun input ->
  match parse_u32_st input with
  | Some (num_entries, off) ->
    begin
      let input = advance_slice input off in
      match validate_entries_st num_entries input with
      | Some off' -> if u32_add_overflows off off' then None
                    else Some (U32.add off off')
      | None -> None
    end
  | None -> None
