module Messages


/// Set up for the parsing example using layered effects
///
/// This module declares some types and functions to parse terms of those types from buffers


open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer


/// Some type declarations for message types

val t1 : Type0

val t2 : Type0

val t3 : Type0


/// Validity predicate
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


val t1_parser : parser_t t1
val t2_parser : parser_t t2
val t3_parser : parser_t t3
