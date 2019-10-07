module Flights

/// Parsing flights (sequence of messages) using the interface of the Messages module

open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer

open Messages

type repr (a:Type0) = {
  v       : a;
  m_begin : uint_32;
  m_end   : uint_32
}

let valid_repr (#a:Type0) (b:B.buffer uint_8) (h:HS.mem) (r:repr a) : Type0
= valid_parsing b r.m_begin r.m_end h r.v


noeq
type flt = {
  t1_msg : repr t1;
  t2_msg : repr t2;
  t3_msg : repr t3
}

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

inline_for_extraction
let parse_t1 = parse_common t1_parser

inline_for_extraction
let parse_t2 = parse_common t2_parser

inline_for_extraction
let parse_t3 = parse_common t3_parser

let parse_flt (b:B.buffer uint_8) (f_begin:uint_32) (f_end:uint_32)
: ST (option flt)
  (requires fun h -> B.live h b /\ valid_indices b f_begin f_end)
  (ensures fun h0 r h1 ->
    B.(modifies loc_none h0 h1) /\
    (match r with
     | None -> True
     | Some flt -> valid_repr b h1 flt.t1_msg /\ valid_repr b h1 flt.t2_msg /\ valid_repr b h1 flt.t3_msg))
= let r = parse_t1 b f_begin in
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
