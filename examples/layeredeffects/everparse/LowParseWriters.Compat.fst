module LowParseWriters.Compat

friend LowParseWriters.LowParse
friend LowParseWriters.Parsers

module B = LowStar.Buffer

let parse_empty_correct = ()

let parse_pair_correct
  p1 p2
= ()

let parse_synth
  p1 #t2 f2 f1
= make_parser
    ((Parser?.p p1).parser `LP.parse_synth` f2)
    (LP.serialize_synth (Parser?.p p1).parser f2 (Parser?.p p1).serializer f1 ())
    (LP.jump_synth (Parser?.p p1).jumper f2 ())

let valid_rewrite_parse_synth
  p1 #t2 f2 f1 sq
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    LP.valid_synth h (get_parser p1) f2 (LP.make_slice b (B.len b)) pos
  );
  valid_rewrite_size = (fun x ->
    LP.synth_injective_synth_inverse_synth_inverse_recip f2 f1 ();
    LP.serialize_synth_eq (get_parser p1) f2 (Parser?.p p1).serializer f1 () (f2 x)
  );
}

let valid_rewrite_parse_synth_recip
  p1 #t2 f2 f1 sq
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    LP.synth_injective_synth_inverse_synth_inverse_recip f2 f1 ();
    LP.valid_synth h (get_parser p1) f2 (LP.make_slice b (B.len b)) pos
  );
  valid_rewrite_size = (fun x ->
    LP.serialize_synth_eq (get_parser p1) f2 (Parser?.p p1).serializer f1 () (x)
  );
}

let parse_vldata_correct
  p min max
= ()

let list_size_correct
  p x
= ()

let parse_vllist_correct
  p min max
= ()

let parse_vlbytes_correct
  min max
= ()

let parse_enum
  #key p e
=
  make_parser
    (LP.parse_enum_key (get_parser p) e)
    (LP.serialize_enum_key _ (get_serializer p) e)
    (LP.jump_enum_key (Parser?.p p).jumper e)

let valid_rewrite_parse_sum
  ps pe p k pk
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    let sl = LP.make_slice b (B.len b) in
    assert (LP.valid (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t) `LP.nondep_then` dsnd (ps.sum_pc k)) h sl pos);
    let (k', _) = LP.contents (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t) `LP.nondep_then` dsnd (ps.sum_pc k)) h sl pos in
    assert (k' == k);
    LP.valid_nondep_then h (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t)) (dsnd (ps.sum_pc k)) sl pos;
    assert (LP.valid (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t)) h sl pos);
    assert (LP.contents (LP.parse_enum_key ps.sum_p (LP.sum_enum ps.sum_t)) h sl pos == k);
    LP.valid_sum_intro h ps.sum_t ps.sum_p ps.sum_pc sl pos
  );
  valid_rewrite_size = (fun x ->
    let (k', pl) = LP.coerce (Parser?.t pe & Parser?.t pk) (x <: (Parser?.t (pe `parse_pair` pk))) in
    let y = LP.synth_sum_case ps.sum_t k pl in
    assert (LP.sum_tag_of_data ps.sum_t y == k);
    LP.synth_sum_case_inverse ps.sum_t k;
    LP.synth_sum_case_injective ps.sum_t k;
    LP.synth_injective_synth_inverse_synth_inverse_recip (LP.synth_sum_case ps.sum_t k) (LP.synth_sum_case_recip ps.sum_t k) ();
    assert (LP.synth_sum_case_recip ps.sum_t k y == pl);
    LP.serialize_sum_eq ps.sum_t ps.sum_s #ps.sum_pc ps.sum_sc y
  );
}

let parse_maybe_enum
  #key p e
=
  make_parser
    (LP.parse_maybe_enum_key (get_parser p) e)
    (LP.serialize_maybe_enum_key _ (get_serializer p) e)
    (LP.jump_maybe_enum_key (Parser?.p p).jumper e)

let valid_rewrite_parse_dsum_known
  ps pe p k pk
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    let sl = LP.make_slice b (B.len b) in
    assert (LP.valid (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t) `LP.nondep_then` dsnd (ps.dsum_pc k)) h sl pos);
    let (k', _) = LP.contents (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t) `LP.nondep_then` dsnd (ps.dsum_pc k)) h sl pos in
    assert (k' == LP.Known k);
    LP.valid_nondep_then h (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t)) (dsnd (ps.dsum_pc k)) sl pos;
    assert (LP.valid (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t)) h sl pos);
    assert (LP.contents (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t)) h sl pos == LP.Known k);
    LP.valid_dsum_intro_known h ps.dsum_t ps.dsum_p ps.dsum_pc ps.dsum_pu sl pos
  );
  valid_rewrite_size = (fun x ->
    let (k', pl) = LP.coerce (Parser?.t pe & Parser?.t pk) (x <: (Parser?.t (pe `parse_pair` pk))) in
    let y = LP.synth_dsum_case ps.dsum_t (LP.Known k) pl in
    assert (LP.dsum_tag_of_data ps.dsum_t y == LP.Known k);
    LP.synth_dsum_case_inverse ps.dsum_t (LP.Known k);
    LP.synth_dsum_case_injective ps.dsum_t (LP.Known k);
    LP.synth_injective_synth_inverse_synth_inverse_recip (LP.synth_dsum_case ps.dsum_t (LP.Known k)) (LP.synth_dsum_case_recip ps.dsum_t (LP.Known k)) ();
    assert (LP.synth_dsum_case_recip ps.dsum_t (LP.Known k) y == pl);
    LP.serialize_dsum_eq ps.dsum_t ps.dsum_s ps.dsum_pc ps.dsum_sc ps.dsum_pu ps.dsum_su y
  );
}

let valid_rewrite_parse_dsum_unknown
  ps pe p pu
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    let sl = LP.make_slice b (B.len b) in
    assert (LP.valid (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t) `LP.nondep_then` (ps.dsum_pu)) h sl pos);
    let (k', _) = LP.contents (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t) `LP.nondep_then` (ps.dsum_pu)) h sl pos in
    assert (LP.Unknown? k');
    LP.valid_nondep_then h (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t)) ((ps.dsum_pu)) sl pos;
    assert (LP.valid (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t)) h sl pos);
    assert (LP.Unknown? (LP.contents (LP.parse_maybe_enum_key ps.dsum_p (LP.dsum_enum ps.dsum_t)) h sl pos));
    LP.valid_dsum_intro_unknown h ps.dsum_t ps.dsum_p ps.dsum_pc ps.dsum_pu sl pos
  );
  valid_rewrite_size = (fun x ->
    let (k', pl) = LP.coerce (Parser?.t pe & Parser?.t pu) (x <: (Parser?.t (pe `parse_pair` pu))) in
    let y = LP.synth_dsum_case ps.dsum_t (k') pl in
    assert (LP.dsum_tag_of_data ps.dsum_t y == k');
    LP.synth_dsum_case_inverse ps.dsum_t (k');
    LP.synth_dsum_case_injective ps.dsum_t (k');
    LP.synth_injective_synth_inverse_synth_inverse_recip (LP.synth_dsum_case ps.dsum_t (k')) (LP.synth_dsum_case_recip ps.dsum_t (k')) ();
    assert (LP.synth_dsum_case_recip ps.dsum_t (k') y == pl);
    LP.serialize_dsum_eq ps.dsum_t ps.dsum_s ps.dsum_pc ps.dsum_sc ps.dsum_pu ps.dsum_su y
  );
}

let valid_rewrite_parse_vlarray_intro
  pa p array_byte_size_min array_byte_size_max elem_count_min elem_count_max u
=
  LP.vldata_to_vlarray_inj (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u;
  LP.vlarray_to_vldata_to_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u;
  valid_rewrite_implies
    _ _ _ _
    (valid_rewrite_compose
      _ _ _ _
      (valid_rewrite_parse_synth
        (parse_vllist p array_byte_size_min array_byte_size_max)
        (LP.vldata_to_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u)
        (LP.vlarray_to_vldata (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u)
        ()
      )
      _ _ _
      (valid_rewrite_parser_eq _ _)
    )
    _ _

let valid_rewrite_parse_vlarray_elim
  pa p array_byte_size_min array_byte_size_max elem_count_min elem_count_max u
=
  LP.vldata_to_vlarray_inj (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u;
  LP.vlarray_to_vldata_to_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u;
  valid_rewrite_implies
    _ _ _ _
    (valid_rewrite_compose
      _ _ _ _
      (valid_rewrite_parser_eq _ _)
      _ _ _
      (valid_rewrite_parse_synth_recip
        (parse_vllist p array_byte_size_min array_byte_size_max)
        (LP.vldata_to_vlarray (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u)
        (LP.vlarray_to_vldata (U32.v array_byte_size_min) (U32.v array_byte_size_max) (get_serializer p) elem_count_min elem_count_max u)
        ()
      )
    )
    _ _

let valid_rewrite_parse_bounded_vldata_intro
  pa p min max
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    assert (valid_pos (parse_vldata p min max) h b pos pos');
    let sl = LP.make_slice b (B.len b) in
    LP.valid_bounded_vldata_strong_elim h (U32.v min) (U32.v max) (get_serializer p) sl pos;
    LP.valid_bounded_vldata_intro h (U32.v min) (U32.v max) (get_parser p) sl pos pos'
  );
  valid_rewrite_size = (fun (x: Parser?.t (parse_vldata p min max)) ->
    LP.serializer_unique (get_parser pa) (get_serializer pa) (LP.serialize_bounded_vldata (U32.v min) (U32.v max) (get_serializer p)) x
  );
}
