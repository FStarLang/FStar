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
module Validator

open KeyValue
open Parsing
open IntegerParsing
open PureParser
open Slice

open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST
module C = C
// special karamel support for looping
open C.Loops


module U32 = FStar.UInt32

(*** Stateful validation of input buffer *)

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
