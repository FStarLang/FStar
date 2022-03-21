module LowParseWriters.Compat
include LowParseWriters.Parsers

module LP = LowParse.Low

val parse_empty_correct : squash (
  get_parser_kind parse_empty == LP.parse_ret_kind /\
  get_parser parse_empty == LP.parse_empty /\
  get_serializer parse_empty == LP.serialize_empty
)

val parse_pair_correct
  (p1 p2: parser)
: Lemma
  (get_parser_kind (p1 `parse_pair` p2) == get_parser_kind p1 `LP.and_then_kind` get_parser_kind p2 /\
  get_parser (p1 `parse_pair` p2) == get_parser p1 `LP.nondep_then` get_parser p2 /\
  get_serializer (p1 `parse_pair` p2) == get_serializer p1 `LP.serialize_nondep_then` get_serializer p2)
  [SMTPat (p1 `parse_pair` p2)]

inline_for_extraction
val parse_synth
  (p1: parser)
  (#t2: Type)
  (f2: Parser?.t p1 -> GTot t2)
  (f1: t2 -> GTot (Parser?.t p1))
: Pure parser
  (requires (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
  (ensures (fun r ->
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1 /\
    Parser?.t r == t2 /\
    get_parser_kind r == get_parser_kind p1 /\
    get_parser r == LP.coerce (LP.parser (get_parser_kind r) (Parser?.t r)) (get_parser p1 `LP.parse_synth` f2) /\
    get_serializer r == LP.coerce (LP.serializer (get_parser r)) (LP.serialize_synth (get_parser p1) f2 (get_serializer p1) f1 ())
  ))

val valid_rewrite_parse_synth
  (p1: parser)
  (#t2: Type)
  (f2: Parser?.t p1 -> GTot t2)
  (f1: t2 -> GTot (Parser?.t p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (valid_rewrite_t p1 (parse_synth p1 f2 f1) (fun _ -> True) f2)

val valid_rewrite_parse_synth_recip
  (p1: parser)
  (#t2: Type)
  (f2: Parser?.t p1 -> GTot t2)
  (f1: t2 -> GTot (Parser?.t p1))
  (sq: squash (
    LP.synth_injective f2 /\
    LP.synth_inverse f2 f1
  ))
: Tot (valid_rewrite_t (parse_synth p1 f2 f1) p1 (fun _ -> True) f1)

module U32 = FStar.UInt32

val parse_vldata_correct
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Lemma
  (
    let p' = parse_vldata p min max in
    Parser?.t p' == LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) (get_serializer p) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) (get_parser_kind p) /\
    get_parser p' == LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p) /\
    get_serializer p' == LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p)
  )
  [SMTPatOr [
    [SMTPat (Parser?.t (parse_vldata p min max))];
    [SMTPat (get_parser_kind (parse_vldata p min max))];
    [SMTPat (get_parser (parse_vldata p min max))];
    [SMTPat (get_serializer (parse_vldata p min max))];
  ]]

val list_size_correct
  (p: parser1)
  (x: list (Parser?.t p))
: Lemma
  (list_size p x == Seq.length (LP.serialize (LP.serialize_list _ (get_serializer p)) x))
  [SMTPat (list_size p x)]

inline_for_extraction
val parse_vllist_correct
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Lemma
  (let p' = parse_vllist p min max in
    Parser?.t p' == LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) LP.parse_list_kind /\
    get_parser p' == LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) /\
    get_serializer p' == LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p))
  )
  [SMTPatOr [
    [SMTPat (Parser?.t (parse_vllist p min max))];
    [SMTPat (get_parser_kind (parse_vllist p min max))];
    [SMTPat (get_parser (parse_vllist p min max))];
    [SMTPat (get_serializer (parse_vllist p min max))];
  ]]

val parse_vlbytes_correct
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Lemma (
    let p' = parse_vlbytes min max in
    Parser?.t p' == LP.parse_bounded_vlbytes_t (U32.v min) (U32.v max) /\
    get_parser_kind p' == LP.parse_bounded_vldata_strong_kind (U32.v min) (U32.v max) (LP.log256' (U32.v max)) LP.parse_all_bytes_kind /\
    get_parser p' == LP.parse_bounded_vlbytes (U32.v min) (U32.v max) /\
    get_serializer p' == LP.serialize_bounded_vlbytes (U32.v min) (U32.v max)
  )
  [SMTPatOr [
    [SMTPat (Parser?.t (parse_vlbytes min max))];
    [SMTPat (get_parser_kind (parse_vlbytes min max))];
    [SMTPat (get_parser (parse_vlbytes min max))];
    [SMTPat (get_serializer (parse_vlbytes min max))];
  ]]

inline_for_extraction
noextract
noeq
type parse_sum_t = {
  sum_kt: LP.parser_kind;
  sum_t: LP.sum;
  sum_p: LP.parser sum_kt (LP.sum_repr_type sum_t);
  sum_s: LP.serializer sum_p;
  sum_pc: ((x: LP.sum_key sum_t) -> Tot (k: LP.parser_kind & LP.parser k (LP.sum_type_of_tag sum_t x)));
  sum_sc: ((x: LP.sum_key sum_t) -> Tot (LP.serializer (dsnd (sum_pc x))));
}

inline_for_extraction
noextract
val parse_enum
  (#key: eqtype)
  (p: parser { hasEq (Parser?.t p) })
  (e: LP.enum key (Parser?.t p))
: Tot (p': parser {
    Parser?.t p' == LP.enum_key e /\
    get_parser_kind p' == LP.parse_filter_kind (get_parser_kind p) /\
    get_parser p' == LP.parse_enum_key (get_parser p) e /\
    get_serializer p' == LP.serialize_enum_key _ (get_serializer p) e
  })

inline_for_extraction
noextract
let pparser
  (t: Type)
  (k: LP.parser_kind)
  (p: LP.parser k t)
  (s: LP.serializer p)
: Tot Type
=
  (q: parser {
    Parser?.t q == t /\
    get_parser_kind q == k /\
    get_parser q == p /\
    get_serializer q == s
  })

val valid_rewrite_parse_sum
  (ps: parse_sum_t)
  (pe: pparser _ _ _ (LP.serialize_enum_key ps.sum_p ps.sum_s (LP.sum_enum ps.sum_t)))
  (p: pparser _ _ _ (LP.serialize_sum ps.sum_t ps.sum_s #ps.sum_pc ps.sum_sc))
  (k: LP.sum_key ps.sum_t)
  (pk: pparser _ _ (dsnd (ps.sum_pc k)) (ps.sum_sc k))
: Tot (valid_rewrite_t (pe `parse_pair` pk) p (fun (k', _) -> k' == k) (fun (_, pl) -> LP.Sum?.synth_case ps.sum_t k pl))

inline_for_extraction
noextract
noeq
type parse_dsum_t = {
  dsum_kt: LP.parser_kind;
  dsum_t: LP.dsum;
  dsum_p: LP.parser dsum_kt (LP.dsum_repr_type dsum_t);
  dsum_s: LP.serializer dsum_p;
  dsum_pc: ((x: LP.dsum_known_key dsum_t) -> Tot (k: LP.parser_kind & LP.parser k (LP.dsum_type_of_known_tag dsum_t x)));
  dsum_sc: ((x: LP.dsum_known_key dsum_t) -> Tot (LP.serializer (dsnd (dsum_pc x))));
  dsum_ku: LP.parser_kind;
  dsum_pu: LP.parser dsum_ku (LP.dsum_type_of_unknown_tag dsum_t);
  dsum_su: LP.serializer dsum_pu;
}

inline_for_extraction
noextract
val parse_maybe_enum
  (#key: eqtype)
  (p: parser { hasEq (Parser?.t p) })
  (e: LP.enum key (Parser?.t p))
: Tot (p': parser {
    Parser?.t p' == LP.maybe_enum_key e /\
    get_parser_kind p' == get_parser_kind p /\
    get_parser p' == LP.coerce (LP.parser (get_parser_kind p') (Parser?.t p')) (LP.parse_maybe_enum_key (get_parser p) e) /\
    get_serializer p' == LP.coerce (LP.serializer (get_parser p')) (LP.serialize_maybe_enum_key _ (get_serializer p) e)
  })

val valid_rewrite_parse_dsum_known
  (ps: parse_dsum_t)
  (pe: pparser _ _ _ (LP.serialize_maybe_enum_key ps.dsum_p ps.dsum_s (LP.dsum_enum ps.dsum_t)))
  (p: pparser _ _ _ (LP.serialize_dsum ps.dsum_t ps.dsum_s ps.dsum_pc ps.dsum_sc ps.dsum_pu ps.dsum_su))
  (k: LP.dsum_known_key ps.dsum_t)
  (pk: pparser _ _ (dsnd (ps.dsum_pc k)) (ps.dsum_sc k))
: Tot (valid_rewrite_t (pe `parse_pair` pk) p (fun (k', _) -> k' == LP.Known k) (fun (_, pl) -> LP.DSum?.synth_case ps.dsum_t (LP.Known k) pl))

val valid_rewrite_parse_dsum_unknown
  (ps: parse_dsum_t)
  (pe: pparser _ _ _ (LP.serialize_maybe_enum_key ps.dsum_p ps.dsum_s (LP.dsum_enum ps.dsum_t)))
  (p: pparser _ _ _ (LP.serialize_dsum ps.dsum_t ps.dsum_s ps.dsum_pc ps.dsum_sc ps.dsum_pu ps.dsum_su))
  (pu: pparser _ _ ps.dsum_pu ps.dsum_su)
: Tot (valid_rewrite_t (pe `parse_pair` pu) p (fun (k', _) -> LP.Unknown? #_ #_ #(LP.dsum_enum ps.dsum_t) k') (fun (k', pl) -> LP.DSum?.synth_case ps.dsum_t k' pl))

val valid_rewrite_parse_vlarray_intro
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
: Tot (valid_rewrite_t
    (parse_vllist p array_byte_size_min array_byte_size_max)
    pa
    (fun _ -> True)
    (fun x -> LP.vldata_to_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max () x)
  )

val valid_rewrite_parse_vlarray_elim
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
: Tot (valid_rewrite_t
    pa
    (parse_vllist p array_byte_size_min array_byte_size_max)
    (fun _ -> True)
    (fun x -> LP.vlarray_to_vldata (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max () x)
  )

val valid_rewrite_parse_bounded_vldata_intro
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
: Tot (valid_rewrite_t
    (parse_vldata p min max)
    pa
    (fun _ -> True)
    (fun x -> x)
  )

inline_for_extraction
noextract
let parse_bounded_vldata_intro_ho
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
  #pre #post #post_err
  ($f: (unit -> EWrite unit parse_empty p pre post post_err inv))
: EWrite unit parse_empty pa pre 
    (fun _ _ vout ->
      pre () /\
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        post () () v /\
        (vout <: Parser?.t p) == v
      | _ -> False
      end
    )
    (fun vin ->
      post_err ()
    )
    inv
=
  assert ( // FIXME: WHY WHY WHY?
    let x = destr_repr_spec _ _ _ _ _ _ _ f () in True
  );
  parse_vldata_intro_ho p min max _ _ _ f;
  valid_rewrite _ _ _ _ _ (valid_rewrite_parse_bounded_vldata_intro _ _ _ _)

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
  (f: (unit -> EWrite unit parse_empty p (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: EWrite unit parse_empty pa
    (fun _ -> True)
    (fun _ _ vout ->
      begin match destr_repr_spec _ _ _ _ _ _ _ f () with
      | Correct (_, v) ->
        (vout <: Parser?.t p) == v
      | _ -> False
      end
    )
    (fun vin ->
      Error? (destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
=
  assert ( // FIXME: WHY WHY WHY?
    let x = destr_repr_spec _ _ _ _ _ _ _ f () in True
  );
  parse_vldata_intro_ho' p min max f;
  valid_rewrite _ _ _ _ _ (valid_rewrite_parse_bounded_vldata_intro _ _ _ _)
