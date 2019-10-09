module FlightsExn

open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer

open Messages
open MExn

module M = Messages

unfold let parse_common_wp (a:Type0) (b:B.buffer uint_8) (m_begin:uint_32) : wp_t (M.repr a)
= fun p h0 ->
    B.live h0 b /\ m_begin <= B.len b /\
    (forall r h1.
       (B.live h1 b /\ B.(modifies loc_none h0 h1)) ==> 
       (match r with
        | None -> p None h1
        | Some x -> valid_repr b h1 x ==> p r h1))

inline_for_extraction
let parse_common_ (#a:Type0)
  (parser:parser_t a)
  (b:B.buffer uint_8)
  (m_begin:uint_32)
: repr (M.repr a) (parse_common_wp a b m_begin)
= fun _ ->
  let r = parser b m_begin in
  match r with
  | None -> None
  | Some (x, m_end) -> Some ({ v = x; m_begin = m_begin; m_end = m_end })

inline_for_extraction
let parse_common (#a:Type0) (parser:parser_t a) (b:B.buffer uint_8) (m_begin:uint_32)
: Exn (M.repr a)
  (requires fun h -> B.live h b /\ m_begin <= B.len b)
  (ensures fun h0 r h1 ->
   B.live h1 b /\ B.(modifies loc_none h0 h1) /\
   (match r with
    | None -> True
    | Some x -> valid_repr b h1 x))
= EXN?.reflect (parse_common_ #a parser b m_begin)

inline_for_extraction
let parse_t1 = parse_common #t1 t1_parser

inline_for_extraction
let parse_t2 = parse_common #t2 t2_parser

inline_for_extraction
let parse_t3 = parse_common #t3 t3_parser

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

let parse_flt : parse_flt_t
= fun b f_begin -> reify (parse_flt_aux b f_begin) ()
