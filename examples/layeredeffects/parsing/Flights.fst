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


module Flights

/// Parsing flights (sequence of messages) using the interface of the Messages module


open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer

open Messages


/// A common function that takes as input a parser and uses it to parse a message from the input buffer
///
/// Returns the corresponding repr with validity postcondition

inline_for_extraction
let parse_common (#a:Type0)
  (parser:parser_t a)
  (b:B.buffer uint_8)
  (m_begin:uint_32)
: ST (option (repr a))
  (requires fun h -> B.live h b /\ m_begin <= B.len b)
  (ensures fun h0 r h1 ->
    B.(modifies loc_none h0 h1) /\
    (match r with
     | None -> True
     | Some x -> valid_repr b h1 x))
= let r = parser b m_begin in
  match r with
  | None -> None
  | Some (x, m_end) -> Some ({ v = x; m_begin = m_begin; m_end = m_end })


/// Partial application of parse_common to different parsers

inline_for_extraction
let parse_t1 = parse_common t1_parser

inline_for_extraction
let parse_t2 = parse_common t2_parser

inline_for_extraction
let parse_t3 = parse_common t3_parser

let parse_flt : parse_flt_t
= fun b f_begin ->
  let r = parse_t1 b f_begin in
  match r with
  | None -> None
  | Some x ->
    let r = parse_t2 b x.m_end in
    match r with
    | None -> None
    | Some y ->
      let r = parse_t3 b y.m_end in
      match r with
      | None -> None
      | Some z ->
        Some ({
          t1_msg = x;
          t2_msg = y;
          t3_msg = z })
