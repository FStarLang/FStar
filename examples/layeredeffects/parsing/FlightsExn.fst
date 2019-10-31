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

module FlightsExn

/// Flight parsing functionality using the layered effect from MExn
///
/// To the client code, it provides the same interface as `parse_flt_t`
///   but internally uses the layered effect to simplify the code and proofs


open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer

open Messages
open MExn

module M = Messages


/// Define a parse_common function but this time in the Exn effect



/// `B.live h1 b` so that the continuations get the liveness
/// `B.(modifies loc_none h0 h1)` so that framing of repr validity can kick


inline_for_extraction
let parse_common (#a:Type0)
  (parser:parser_t a)
  (b:B.buffer uint_8)
  (m_begin:uint_32)
: Exn (M.repr a)
  (requires fun h -> B.live h b /\ m_begin <= B.len b)
  (ensures fun h0 r h1 ->
   B.live h1 b /\ B.(modifies loc_none h0 h1) /\ 
   (match r with
    | None -> True
    | Some x -> valid_repr b h1 x))
= EXN?.reflect (fun _ ->
    let r = parser b m_begin in
    match r with
    | None -> None
    | Some (x, m_end) -> Some ({ v = x; m_begin = m_begin; m_end = m_end }))



/// Partially applied parse_common

inline_for_extraction
let parse_t1 = parse_common #t1 t1_parser

inline_for_extraction
let parse_t2 = parse_common #t2 t2_parser

inline_for_extraction
let parse_t3 = parse_common #t3 t3_parser


/// Finally, the internal function in `Exn`

#set-options "--using_facts_from '* -LowStar -FStar.HyperStack -FStar.Monotonic -FStar.Heap'"

inline_for_extraction
let parse_flt_aux (b:B.buffer uint_8) (f_begin:uint_32)
: Exn flt (pre_f b f_begin) (post_f b)
= let x = parse_t1 b f_begin in
  let y = parse_t2 b x.m_end in
  let z = parse_t3 b y.m_end in
  { t1_msg = x;
    t2_msg = y;
    t3_msg = z }


/// But to the clients we can present the same interface
///
/// And it also extracts to the same C code as without using the layered effect (Flights.fst)

let parse_flt : parse_flt_t
= fun b f_begin -> reify (parse_flt_aux b f_begin) ()
