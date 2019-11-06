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

module Messages


/// Set up for the parsing example using layered effects
///
/// This module declares some types and functions to parse messages of those types from buffers


open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer


/// Some type declarations for message types

val t1 : Type0

val t2 : Type0

val t3 : Type0


/// Validity predicate and its framing lemma
///
/// b's contents in memory h, between m_begin and m_end, are valid serialization of x

unfold
let valid_indices (b:B.buffer uint_8) (i j:uint_32) =
  i <= j /\ j <= B.len b

val valid_
  (#a:Type0)
  (b:B.buffer uint_8)
  (m_begin:uint_32) (m_end:uint_32{valid_indices b m_begin m_end})
  (h:HS.mem)
  (x:a)
: Type0

val frame_valid_
  (#a:Type0)
  (b:B.buffer uint_8)
  (m_begin:uint_32) (m_end:uint_32{valid_indices b m_begin m_end})
  (x:a)
  (h0 h1:HS.mem)
: Lemma
  (requires valid_ b m_begin m_end h0 x /\ B.(modifies loc_none h0 h1))
  (ensures valid_ b m_begin m_end h1 x)
  [SMTPat (valid_ b m_begin m_end h1 x);
   SMTPat (B.(modifies loc_none h0 h1))]

let valid_parsing (#a:Type0) (b:B.buffer uint_8) (m_begin m_end:uint_32) (h:HS.mem) (x:a) =
  valid_indices b m_begin m_end /\ valid_ b m_begin m_end h x


/// Type of a parser

inline_for_extraction
type parser_t (a:Type0) =
  b:B.buffer uint_8 ->
  m_begin:uint_32   ->
  ST (option (a & uint_32))
  (requires fun h -> B.live h b /\ m_begin <= B.len b)
  (ensures fun h0 r h1 ->
    B.(modifies loc_none h0 h1) /\
    (match r with
     | None -> True
     | Some (x, m_end) -> valid_parsing b m_begin m_end h1 x))


/// Parsers for t1, t2, and t3

val t1_parser : parser_t t1
val t2_parser : parser_t t2
val t3_parser : parser_t t3


/// Repr type to package parsed messages with indices in the buffer

type repr (a:Type0) = {
  v       : a;
  m_begin : uint_32;
  m_end   : uint_32
}


/// Validity of a repr in a memory

let valid_repr (#a:Type0) (b:B.buffer uint_8) (h:HS.mem) (r:repr a) : Type0
= valid_parsing b r.m_begin r.m_end h r.v


noeq
type flt = {
  t1_msg : repr t1;
  t2_msg : repr t2;
  t3_msg : repr t3
}


unfold let pre_f (b:B.buffer uint_8) (f_begin:uint_32) =
  fun (h:HS.mem) -> B.live h b /\ f_begin <= B.len b

unfold let post_f (b:B.buffer uint_8) =
  fun (_:HS.mem) (r:option flt) (h1:HS.mem) ->
  (match r with
   | None -> True
   | Some flt -> valid_repr b h1 flt.t1_msg /\ valid_repr b h1 flt.t2_msg /\ valid_repr b h1 flt.t3_msg)

inline_for_extraction
type parse_flt_t =
  b:B.buffer uint_8 -> f_begin:uint_32 ->
  ST (option flt) (pre_f b f_begin)
  (fun h0 r h1 -> B.(modifies loc_none h0 h1) /\ post_f b h0 r h1)
