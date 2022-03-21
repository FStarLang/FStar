module LowParseWriters.NoHoare.Compat
include LowParseWriters.Compat
include LowParseWriters.NoHoare.Parsers

module LP = LowParse.Low

let valid_rewrite_parse_synth'
  (p1: parser)
  (#t2: Type)
  (f2: Parser?.t p1 -> GTot t2)
  (f1: t2 -> GTot (Parser?.t p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (squash (valid_rewrite_prop p1 (parse_synth p1 f2 f1)))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_synth p1 f2 f1 sq)

let valid_rewrite_parse_synth_recip'
  (p1: parser)
  (#t2: Type)
  (f2: Parser?.t p1 -> GTot t2)
  (f1: t2 -> GTot (Parser?.t p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (squash (valid_rewrite_prop (parse_synth p1 f2 f1) p1))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_synth_recip p1 f2 f1 sq)

module U32 = FStar.UInt32

let valid_rewrite_parse_vlarray_intro'
  (pa: parser)
  (p: parser1)
  (array_byte_size_min: U32.t)
  (array_byte_size_max: U32.t { U32.v array_byte_size_min <= U32.v array_byte_size_max /\ U32.v array_byte_size_max > 0 } )
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: squash (
    LP.vldata_vlarray_precond (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_parser p) elem_count_min elem_count_max == true /\
    get_parser_kind pa == LP.parse_vlarray_kind (U32.v array_byte_size_min) (U32.v array_byte_size_max) /\
    Parser?.t pa == LP.vlarray (Parser?.t p) elem_count_min elem_count_max /\
    get_parser pa == LP.parse_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max ()
  ))
: Tot (squash (valid_rewrite_prop
    (parse_vllist p array_byte_size_min array_byte_size_max)
    pa
  ))
=
  tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_vlarray_intro pa p array_byte_size_min array_byte_size_max elem_count_min elem_count_max u)

let valid_rewrite_parse_vlarray_elim'
  (pa: parser)
  (p: parser1)
  (array_byte_size_min: U32.t)
  (array_byte_size_max: U32.t { U32.v array_byte_size_min <= U32.v array_byte_size_max /\ U32.v array_byte_size_max > 0 } )
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: squash (
    LP.vldata_vlarray_precond (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_parser p) elem_count_min elem_count_max == true /\
    get_parser_kind pa == LP.parse_vlarray_kind (U32.v array_byte_size_min) (U32.v array_byte_size_max) /\
    Parser?.t pa == LP.vlarray (Parser?.t p) elem_count_min elem_count_max /\
    get_parser pa == LP.parse_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max ()
  ))
: Tot (squash (valid_rewrite_prop
    pa
    (parse_vllist p array_byte_size_min array_byte_size_max)
  ))
=
  tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_vlarray_elim pa p array_byte_size_min array_byte_size_max elem_count_min elem_count_max u)

let valid_rewrite_parse_bounded_vldata_intro'
  (pa: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t {
    U32.v min <= U32.v max /\
    U32.v max > 0 /\
    LP.serialize_bounded_vldata_precond (U32.v min) (U32.v max) (get_parser_kind p) /\
    Parser?.t pa == Parser?.t p /\
    get_parser_kind pa == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) (get_parser_kind p) /\
    get_parser pa == LP.parse_bounded_vldata (U32.v min) (U32.v max) (get_parser p)
  })
: Tot (squash (valid_rewrite_prop
    (parse_vldata p min max)
    pa
  ))
=
  tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_bounded_vldata_intro pa p min max)

inline_for_extraction
noextract
let parse_bounded_vldata_intro_ho'
  (#inv: memory_invariant)
  (pa: parser)
  (p: parser)
  (min: U32.t)
  (max: U32.t {
    U32.v min <= U32.v max /\
    U32.v max > 0 /\
    LP.serialize_bounded_vldata_precond (U32.v min) (U32.v max) (get_parser_kind p) /\
    Parser?.t pa == Parser?.t p /\
    get_parser_kind pa == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) (get_parser_kind p) /\
    get_parser pa == LP.parse_bounded_vldata (U32.v min) (U32.v max) (get_parser p)
  })
  (f: (unit -> TWrite unit parse_empty p inv))
: TWrite unit parse_empty pa
    inv
=
  twrite_of_ewrite (fun _ -> parse_bounded_vldata_intro_ho' pa p min max (fun _ -> ewrite_of_twrite f))
   
