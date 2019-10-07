module FlightsExn

open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer

open Messages
open Exn

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

unfold let pre_m (b:B.buffer uint_8) m_begin =
  fun h -> B.live h b /\ m_begin <= B.len b

unfold let post_m (#a:Type0) b =
  fun h0 r h1 ->
  B.(modifies loc_none h0 h1) /\
  (match r with
   | None -> True
   | Some x -> valid_repr b h1 x)

inline_for_extraction
let parse_common_ (#a:Type0)
  (parser:parser_t a)
  (b:B.buffer uint_8)
  (m_begin:uint_32)
: unit -> ST (option (repr a)) (requires pre_m b m_begin) (ensures post_m #a b)
= fun _ ->
  let r = parser b m_begin in
  match r with
  | None -> None
  | Some (x, m_end) -> Some ({ v = x; m_begin = m_begin; m_end = m_end })

inline_for_extraction
let parse_common (#a:Type0) (parser:parser_t a) (b:B.buffer uint_8) (m_begin:uint_32)
: Exn (repr a) (requires pre_m b m_begin) (ensures post_m #a b)
= EXN?.reflect (parse_common_ #a parser b m_begin)

inline_for_extraction
let parse_t1 = parse_common #t1 t1_parser

inline_for_extraction
let parse_t2 = parse_common #t2 t2_parser

inline_for_extraction
let parse_t3 = parse_common #t3 t3_parser

unfold let pre_f (b:B.buffer uint_8) f_begin f_end =
  fun h -> B.live h b /\ valid_indices b f_begin f_end

unfold let post_f (b:B.buffer uint_8) =
  fun h0 r h1 ->
   B.(modifies loc_none h0 h1) /\
   (match r with
    | None -> True
    | Some flt -> valid_repr b h1 flt.t1_msg /\ valid_repr b h1 flt.t2_msg /\ valid_repr b h1 flt.t3_msg)

inline_for_extraction
let parse_flt_aux (b:B.buffer uint_8) (f_begin:uint_32) (f_end:uint_32)
: Exn flt (requires pre_f b f_begin f_end) (ensures post_f b)
= let x = parse_t1 b f_begin in
  let y = parse_t2 b x.m_end in
  let z = parse_t3 b y.m_end in
  { t1_msg = x;
    t2_msg = y;
    t3_msg = z }

let parse_flt (b:B.buffer uint_8) (f_begin:uint_32) (f_end:uint_32)
: ST (option flt) (requires pre_f b f_begin f_end) (ensures post_f b)
= reify (parse_flt_aux b f_begin f_end) ()
