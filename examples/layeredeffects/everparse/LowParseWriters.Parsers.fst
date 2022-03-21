module LowParseWriters.Parsers
friend LowParseWriters.LowParse

module LP = LowParse.Low
module B = LowStar.Buffer

let get_parser_kind
  p
= (Parser?.p p).kind

let get_parser
  p
= (Parser?.p p).parser

let get_serializer
  p
= (Parser?.p p).serializer

let make_parser'
  #t #k p s j
= {
  kind = k;
  parser = p;
  serializer = s;
  jumper = j;
}

let make_parser_correct
  #t #k p s j
= ()

let size_correct
  p x
= ()

let leaf_reader_of_lp_leaf_reader
  p r
= fun b len -> r (LP.make_slice b len) 0ul

inline_for_extraction
let leaf_writer_of_lp_leaf_writer
  p w
= if (get_parser_kind p).LP.parser_kind_low > 4294967295
  then (fun b len x -> None)
  else (fun b len x ->
    if len `U32.lt` U32.uint_to_t ((get_parser_kind p).LP.parser_kind_low)
    then None
    else Some (w x (LP.make_slice b len) 0ul)
  )

let lp_clens_to_clens
  (#t1 #t2: Type)
  (c: LP.clens t1 t2)
: Tot (clens t1 t2)
= {
  clens_cond = c.LP.clens_cond;
  clens_get = c.LP.clens_get
}

let access_spec
  p1 p2 #lens #g a #inv x
=
  access_spec #p1 #p2 #(lp_clens_to_clens lens) g x

let access_impl
  p1 p2 #lens #g a #inv x
= access_impl #p1 #p2 #(lp_clens_to_clens lens) a x

let valid_rewrite_parser_eq
  p1 p2
= {
  valid_rewrite_valid = (fun h b pos pos' -> ());
  valid_rewrite_size = (fun x ->
    LP.serializer_unique (get_parser p1) (Parser?.p p1).serializer (Parser?.p p2).serializer x
  );
}

let parse_vldata_t_correct
  (min: nat)
  (max: nat { min <= max /\ 0 < max /\ max < 4294967296 })
  (p: parser)
: Lemma
  (parse_vldata_t ( min) ( max) p == LP.parse_bounded_vldata_strong_t ( min) ( max) (get_serializer p))
  [SMTPat (parse_vldata_t ( min) ( max) p)]
=
  assert_norm (parse_vldata_t (min) ( max) p == LP.parse_bounded_vldata_strong_t ( min) ( max) (get_serializer p))

let parse_vldata
  p min max
=
  make_parser
    (LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p))
    (LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p))
    (LP.jump_bounded_vldata_strong (U32.v min) (U32.v max) (get_serializer p) ())

let size_parse_vldata
  p min max x
= ()

let log256_correct
  (max: U32.t { U32.v max > 0 })
: Lemma
  (U32.v (log256 max) == LP.log256' (U32.v max))
  [SMTPat (U32.v (log256 max))]
= ()

let valid_rewrite_parse_vldata
  p min max min' max'
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    let sl = LP.make_slice b (B.len b) in
    let s = get_serializer p in
    let sz = U32.v (log256 max) in
    LP.valid_bounded_vldata_strong_elim h (U32.v min) (U32.v max) s sl pos;
    LP.valid_bounded_vldata_strong_intro h (U32.v min') (U32.v max') s sl pos pos'
  );
  valid_rewrite_size = (fun x ->
    ()
  );
}

let parse_bounded_integer
  sz
=
  make_parser
    (LP.parse_bounded_integer (U32.v sz))
    (LP.serialize_bounded_integer (U32.v sz))
    (LP.jump_bounded_integer' sz)

module HST = FStar.HyperStack.ST

let parse_vldata_intro_impl
  #inv p min max
= mk_repr_impl
    _ _ _ _ _ _ inv (parse_vldata_intro_spec p min max)
  (fun b len pos ->
    let h = HST.get () in
    [@inline_let]
    let sz : LP.integer_size = LP.log256' (U32.v max) in
    [@inline_let]
    let sz32 = U32.uint_to_t sz in
    let sl = LP.make_slice b len in
    LP.valid_nondep_then h (LP.parse_bounded_integer sz) (get_parser p) sl 0ul;
    assert (LP.valid_pos (get_parser p) h sl sz32 pos); // necessary because the vldata lemma below uses the end position
    let size = pos `U32.sub` sz32 in
    let _ = LP.write_bounded_integer sz size sl 0ul in
    let h1 = HST.get () in
    LP.valid_bounded_vldata_strong_intro h1 (U32.v min) (U32.v max) (get_serializer p) sl 0ul pos;
    ICorrect () pos
  )

let write_bounded_integer = LP.write_bounded_integer'

let parse_vldata_intro_weak_impl
  #inv p min max
= mk_repr_impl
    _ _ _ _ _ _ inv (parse_vldata_intro_weak_spec p min max)
  (fun b len pos ->
    let h = HST.get () in
    [@inline_let]
    let sz : LP.integer_size = LP.log256' (U32.v max) in
    [@inline_let]
    let sz32 = U32.uint_to_t sz in
    let sl = LP.make_slice b len in
    LP.valid_nondep_then h (LP.parse_bounded_integer sz) (get_parser p) sl 0ul;
    assert (LP.valid_pos (get_parser p) h sl sz32 pos); // necessary because the vldata lemma below uses the end position
    let size = pos `U32.sub` sz32 in
    if min `U32.lte` size && size `U32.lte` max
    then begin
      let _ = LP.write_bounded_integer sz size sl 0ul in
      let h1 = HST.get () in
      LP.valid_bounded_vldata_strong_intro h1 (U32.v min) (U32.v max) (get_serializer p) sl 0ul pos;
      ICorrect () pos
    end else begin
      IError "parse_vldata_intro_weak: out of bounds"
    end
  )

let parse_vldata_recast_impl
  #inv p min max min' max'
=
  mk_repr_impl _ _ _ _ _ _ inv (parse_vldata_recast_spec p min max min' max') (fun b len pos ->
    let h = HST.get () in
    let sl = LP.make_slice b len in
    let s = get_serializer p in
    LP.valid_bounded_vldata_strong_elim h (U32.v min) (U32.v max) s sl 0ul;
    let sz = pos `U32.sub` U32.uint_to_t (LP.log256' (U32.v max)) in
    if min' `U32.lte` sz && sz `U32.lte` max'
    then begin
      LP.valid_bounded_vldata_strong_intro h (U32.v min') (U32.v max') s sl 0ul pos;
      ICorrect () pos
    end else
      IError "parse_vldata_recast: out of bounds"
  )

noeq
type rlptr = {
  rlptr_base: B.buffer u8;
  rlptr_len: (rlptr_len: U32.t { rlptr_len == B.len rlptr_base });
}

let valid_rlptr
  p inv x
=
  let base = x.rlptr_base in
  let len = B.len base in
  let sl = LP.make_slice base len in
  LP.valid_list (get_parser p) inv.h0 sl 0ul len /\
  inv.lwrite `B.loc_disjoint` B.loc_buffer base

let deref_list_spec
  #p #inv x
=
  let base = x.rlptr_base in
  let len = B.len base in
  let sl = LP.make_slice base len in
  LP.contents_list (get_parser p) inv.h0 sl 0ul len

let valid_rlptr_frame
  #p #inv x inv'
= ()

module HS = FStar.HyperStack

#push-options "--z3rlimit 32"

let rec valid_list_ext
  (#rrel #rel: _)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h1: HS.mem)
  (sl1: LP.slice rrel rel)
  (pos1: U32.t)
  (pos1' : U32.t)
  (h2: HS.mem)
  (sl2: LP.slice rrel rel)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    LP.valid_list p h1 sl1 pos1 pos1' /\
    U32.v pos2 <= U32.v pos2' /\
    U32.v pos2' <= U32.v sl2.LP.len /\
    LP.live_slice h2 sl2 /\
    LP.bytes_of_slice_from_to h1 sl1 pos1 pos1' `Seq.equal` LP.bytes_of_slice_from_to h2 sl2 pos2 pos2'
  ))
  (ensures (
    LP.valid_list p h1 sl1 pos1 pos1' /\
    LP.valid_list p h2 sl2 pos2 pos2' /\
    LP.contents_list p h1 sl1 pos1 pos1' ==
    LP.contents_list p h2 sl2 pos2 pos2'
  ))
  (decreases (U32.v pos1' - U32.v pos1))
=
  LP.valid_list_equiv p h1 sl1 pos1 pos1' ;
  LP.valid_list_equiv p h2 sl2 pos2 pos2' ;
  assert (Seq.length (LP.bytes_of_slice_from_to h1 sl1 pos1 pos1') == Seq.length (LP.bytes_of_slice_from_to h2 sl2 pos2 pos2'));
  assert (U32.v pos2' - U32.v pos2 == U32.v pos1' - U32.v pos1);
  if pos1 = pos1'
  then begin
    LP.valid_list_nil p h1 sl1 pos1;
    LP.valid_list_nil p h2 sl2 pos2
  end else begin
    let pos1_ = LP.get_valid_pos p h1 sl1 pos1 in
    assert (U32.v pos1_ <= U32.v pos1');
    LP.valid_facts p h1 sl1 pos1;
    let pos2_ = pos2 `U32.add` (pos1_ `U32.sub` pos1) in
    LP.parse_strong_prefix p (LP.bytes_of_slice_from h1 sl1 pos1) (LP.bytes_of_slice_from_to h1 sl1 pos1 pos1_);
    assert (LP.bytes_of_slice_from_to h1 sl1 pos1 pos1_ `Seq.equal` Seq.slice (LP.bytes_of_slice_from_to h1 sl1 pos1 pos1') 0 (U32.v pos1_ - U32.v pos1));
    assert (LP.bytes_of_slice_from_to h2 sl2 pos2 pos2_ `Seq.equal` Seq.slice (LP.bytes_of_slice_from_to h2 sl2 pos2 pos2') 0 (U32.v pos2_ - U32.v pos2));
    LP.parse_strong_prefix p (LP.bytes_of_slice_from_to h1 sl1 pos1 pos1_) (LP.bytes_of_slice_from_to h2 sl2 pos2 pos2_);
    LP.parse_strong_prefix p (LP.bytes_of_slice_from_to h2 sl2 pos2 pos2_) (LP.bytes_of_slice_from h2 sl2 pos2);
    assert (Some? (LP.parse p (LP.bytes_of_slice_from h2 sl2 pos2)));
    LP.valid_facts p h2 sl2 pos2;
    assert (LP.valid p h2 sl2 pos2);
    assert (pos2_ == LP.get_valid_pos p h2 sl2 pos2);
    assert (LP.bytes_of_slice_from_to h1 sl1 pos1_ pos1' `Seq.equal` Seq.slice (LP.bytes_of_slice_from_to h1 sl1 pos1 pos1') (U32.v pos1_ - U32.v pos1) (U32.v pos1' - U32.v pos1));
    assert (LP.bytes_of_slice_from_to h2 sl2 pos2_ pos2' `Seq.equal` Seq.slice (LP.bytes_of_slice_from_to h2 sl2 pos2 pos2') (U32.v pos2_ - U32.v pos2) (U32.v pos2' - U32.v pos2));
    valid_list_ext p h1 sl1 pos1_ pos1' h2 sl2 pos2_ pos2';
    LP.contents_list_eq p h1 sl1 pos1 pos1' ;
    LP.valid_list_cons p h2 sl2 pos2 pos2'
  end

#pop-options

let destr_list_spec
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: Tot (read_repr_spec
    (option (ptr p inv & lptr p inv))
    True
    (destr_list_post x)
    (fun _ -> False)
  )
= fun _ ->
  Correct (match deref_list_spec x with
  | [] -> None
  | a :: q ->
    let base = x.rlptr_base in
    let len = B.len base in
    let sl = LP.make_slice base len in
    let ps = get_parser p in
    if len = 0ul
    then LP.valid_list_nil ps inv.h0 sl 0ul;
    LP.valid_list_cons_recip ps inv.h0 sl 0ul len;
    let pos = LP.get_valid_pos ps inv.h0 sl 0ul in
    let b_hd = B.gsub base 0ul pos in
    let len_tl = len `U32.sub` pos in
    let b_tl = B.gsub base pos len_tl in
    let sl_hd = LP.make_slice b_hd pos in
    let sl_tl = LP.make_slice b_tl len_tl in
    LP.valid_facts ps inv.h0 sl 0ul;
    LP.parse_strong_prefix ps (LP.bytes_of_slice_from inv.h0 sl 0ul) (LP.bytes_of_slice_from inv.h0 sl_hd 0ul);
    LP.valid_facts ps inv.h0 sl_hd 0ul;
    valid_list_ext ps inv.h0 sl pos len inv.h0 sl_tl 0ul len_tl;
    Some (mk_ptr p inv b_hd pos, {
      rlptr_base = b_tl;
      rlptr_len = len_tl;
  }))

inline_for_extraction
let destr_list_impl
  (#p: parser1)
  (#inv: memory_invariant)
  (x: lptr p inv)
: Tot (read_repr_impl
    (option (ptr p inv & lptr p inv))
    True
    (destr_list_post x)
    (fun _ -> False)
    inv
    (destr_list_spec x)
  )
= mk_read_repr_impl
    (option (ptr p inv & lptr p inv))
    True
    (destr_list_post x)
    (fun _ -> False)
    inv
    (destr_list_spec x)
    (fun _ ->
      let ps = Ghost.hide (get_parser p) in
      let base = x.rlptr_base in
      let len = x.rlptr_len in
      let sl = LP.make_slice base len in
      if x.rlptr_len = 0ul
      then begin
        LP.valid_list_nil ps inv.h0 sl 0ul;
        Correct None
      end else begin
        LP.valid_list_cons_recip ps inv.h0 sl 0ul len;
        let pos = (Parser?.p p).jumper sl 0ul in
        let b_hd = B.sub base 0ul pos in
        let len_tl = len `U32.sub` pos in
        let b_tl = B.sub base pos len_tl in
        let sl_hd = LP.make_slice b_hd pos in
        let sl_tl = LP.make_slice b_tl len_tl in
        LP.valid_facts ps inv.h0 sl 0ul;
        LP.parse_strong_prefix ps (LP.bytes_of_slice_from inv.h0 sl 0ul) (LP.bytes_of_slice_from inv.h0 sl_hd 0ul);
        LP.valid_facts ps inv.h0 sl_hd 0ul;
        valid_list_ext ps inv.h0 sl pos len inv.h0 sl_tl 0ul len_tl;
        Correct (Some (mk_ptr p inv b_hd pos, {
          rlptr_base = b_tl;
          rlptr_len = len_tl;
        }))
      end
    )

let destr_list_repr
  #p #inv x
= ReadRepr _ (destr_list_impl x)

let read_do_while_impl
  inv #t invariant measure error body x0
=
  mk_read_repr_impl _ _ _ _ inv (read_do_while_spec inv #t invariant measure error body x0) (fun _ ->
    HST.push_frame ();
    let btemp : B.pointer (result t) = B.alloca (Correct x0) 1ul in
    let h0 = HST.get () in
    C.Loops.do_while
      (fun h stop ->
        B.modifies (B.loc_all_regions_from true (HS.get_tip h0)) h0 h /\
        B.live h btemp /\
        HS.get_tip h0 == HS.get_tip h /\
        begin match B.deref h btemp with
        | Correct x ->
          invariant x (not stop) /\
          read_do_while_spec' inv #t invariant measure error body x0 () ==
            begin if stop
              then Correct x
              else read_do_while_spec' inv #t invariant measure error body x ()
            end
        | Error s ->
          stop == true /\
          read_do_while_spec' inv #t invariant measure error body x0 () == Error s
        end
      )
      (fun _ ->
        let Correct x = B.index btemp 0ul in
        let h = HST.get () in
        assert (invariant x true);
        assert (read_do_while_spec' inv #t invariant measure error body x0 () == read_do_while_spec' inv #t invariant measure error body x ());
        match reify_read _ _ _ _ _ (body x) with
        | Correct (x', cont) ->
          B.upd btemp 0ul (Correct x');
          let h' = HST.get () in
          assert (Correct? (destr_read_repr_spec _ _ _ _ _ (body x) ()));
          assert (invariant x' cont);
          not cont
        | Error s ->
          B.upd btemp 0ul (Error s);
          true
      );
    let res = B.index btemp 0ul in
    HST.pop_frame ();
    res
  )

let list_size
  p x
=
  Seq.length (LP.serialize (LP.serialize_list _ (get_serializer p)) x)

let list_size_nil
  p
=
  LP.serialize_list_nil _ (get_serializer p)

let list_size_cons
  p a q
=
  LP.serialize_list_cons _ (get_serializer p) a q

let parse_vllist_t_correct
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Lemma
  (parse_vllist_t p min max == LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)))
  [SMTPat (parse_vllist_t p min max)]
= assert_norm (parse_vllist_t p min max == LP.parse_bounded_vldata_strong_t (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)))

let parse_vllist
  p min max
=
  make_parser
    (LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)))
    (LP.serialize_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)))
    (LP.jump_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) ())

let parse_vllist_size
  p min max x
= ()

let lptr_of_vllist_ptr_spec
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (r: ptr (parse_vllist p min max) inv)
: Tot (read_repr_spec (lptr p inv) True (fun r' -> deref_list_spec r' == (deref_spec r <: list (Parser?.t p))) (fun _ -> False))
=
  fun _ ->
  let (b, len) = buffer_of_ptr r in
  let sl = LP.make_slice b len in
  LP.valid_bounded_vldata_strong_elim inv.h0 (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) sl 0ul;
  let pos_pl = U32.uint_to_t (LP.log256' (U32.v max)) in
  let len_pl = len `U32.sub` pos_pl in
  LP.valid_exact_list_valid_list (get_parser p) inv.h0 sl pos_pl len;
  let b_pl = B.gsub b pos_pl len_pl in
  valid_list_ext (get_parser p) inv.h0 sl pos_pl len inv.h0 (LP.make_slice b_pl len_pl) 0ul len_pl;
  Correct ({ rlptr_base = b_pl; rlptr_len = len_pl })

inline_for_extraction
let lptr_of_vllist_ptr_impl
  (#inv: memory_invariant)
  (p: parser1)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (r: ptr (parse_vllist p min max) inv)
: Tot (read_repr_impl _ _ _ _ inv (lptr_of_vllist_ptr_spec p min max r))
=
  mk_read_repr_impl
    _ _ _ _ inv (lptr_of_vllist_ptr_spec p min max r) (fun _ ->
    let (b, len) = buffer_of_ptr r in
    let sl = LP.make_slice b len in
    LP.valid_bounded_vldata_strong_elim inv.h0 (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) sl 0ul;
    let pos_pl = U32.uint_to_t (LP.log256' (U32.v max)) in
    let len_pl = len `U32.sub` pos_pl in
    LP.valid_exact_list_valid_list (get_parser p) inv.h0 sl pos_pl len;
    let b_pl = B.sub b pos_pl len_pl in
    valid_list_ext (get_parser p) inv.h0 sl pos_pl len inv.h0 (LP.make_slice b_pl len_pl) 0ul len_pl;
    Correct ({ rlptr_base = b_pl; rlptr_len = len_pl })
  )

let lptr_of_vllist_ptr_repr
  #inv p min max r
=
  (ReadRepr _ (lptr_of_vllist_ptr_impl p min max r))

let parse_vllist_nil_impl
  #inv p max
=
  mk_repr_impl
    _ _ _ _ _ _ inv (parse_vllist_nil_spec p max) (fun b len _ ->
    let pos_pl = U32.uint_to_t (LP.log256' (U32.v max)) in
    if len `U32.lt` pos_pl
    then IOverflow
    else begin
      let h = HST.get () in
      let sl = LP.make_slice b len in
      LP.valid_list_nil (get_parser p) h sl pos_pl;
      LP.valid_list_valid_exact_list (get_parser p) h sl pos_pl pos_pl;
      LP.finalize_bounded_vldata_strong_exact 0 (U32.v max) (LP.serialize_list _ (get_serializer p)) sl 0ul pos_pl;
      ICorrect () pos_pl
    end
  )

#push-options "--z3rlimit 32"

let parse_vllist_snoc_impl
  #inv p min max
= mk_repr_impl
    _ _ _ _ _ _ inv (parse_vllist_snoc_spec p min max) (fun b len pos ->
    let h = HST.get () in
    let sl = LP.make_slice b len in
    assert (LP.valid (LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) `LP.nondep_then` get_parser p) h sl 0ul);
    LP.valid_nondep_then h (LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p))) (get_parser p) sl 0ul;
    let pos_last = LP.jump_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) () sl 0ul in
    let pos_pl = U32.uint_to_t (LP.log256' (U32.v max)) in
    LP.valid_bounded_vldata_strong_elim h (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) sl 0ul;
    LP.valid_exact_list_valid_list (get_parser p) h sl pos_pl pos_last;
    LP.valid_list_snoc (get_parser p) h sl pos_pl pos_last;
    LP.valid_list_valid_exact_list (get_parser p) h sl pos_pl pos;
    LP.finalize_bounded_vldata_strong_exact (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) sl 0ul pos;
    ICorrect () pos
  )

let parse_vllist_snoc_weak_impl
  #inv p min max
= mk_repr_impl
    _ _ _ _ _ _ inv (parse_vllist_snoc_weak_spec p min max) (fun b len pos ->
    let h = HST.get () in
    let sl = LP.make_slice b len in
    assert (LP.valid (LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) `LP.nondep_then` get_parser p) h sl 0ul);
    LP.valid_nondep_then h (LP.parse_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p))) (get_parser p) sl 0ul;
    let pos_last = LP.jump_bounded_vldata_strong (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) () sl 0ul in
    let pos_pl = U32.uint_to_t (LP.log256' (U32.v max)) in
    LP.valid_bounded_vldata_strong_elim h (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) sl 0ul;
    LP.valid_exact_list_valid_list (get_parser p) h sl pos_pl pos_last;
    LP.valid_list_snoc (get_parser p) h sl pos_pl pos_last;
    LP.valid_list_valid_exact_list (get_parser p) h sl pos_pl pos;
    let sz = pos `U32.sub` pos_pl in
    if min `U32.lte` sz && sz `U32.lte` max
    then begin
      LP.finalize_bounded_vldata_strong_exact (U32.v min) (U32.v max) (LP.serialize_list _ (get_serializer p)) sl 0ul pos;
      ICorrect () pos
    end else
      IError "parse_vllist_snoc_weak: out of bounds"
  )

#pop-options

let valid_rewrite_parse_vllist
  p min max min' max'
= {
  valid_rewrite_valid = (fun h b pos pos' ->
    let sl = LP.make_slice b (B.len b) in
    let s = LP.serialize_list _ (get_serializer p) in
    LP.valid_bounded_vldata_strong_elim h (U32.v min) (U32.v max) s sl pos;
    LP.valid_bounded_vldata_strong_intro h (U32.v min') (U32.v max') s sl pos pos'
  );
  valid_rewrite_size = (fun x ->
    ()
  );
}

let parse_vllist_recast_impl
  #inv p min max min' max'
=
  mk_repr_impl _ _ _ _ _ _ inv (parse_vllist_recast_spec p min max min' max') (fun b len pos ->
    let h = HST.get () in
    let sl = LP.make_slice b len in
    let s = LP.serialize_list _ (get_serializer p) in
    LP.valid_bounded_vldata_strong_elim h (U32.v min) (U32.v max) s sl 0ul;
    let sz = pos `U32.sub` U32.uint_to_t (LP.log256' (U32.v max)) in
    if min' `U32.lte` sz && sz `U32.lte` max'
    then begin
      LP.valid_bounded_vldata_strong_intro h (U32.v min') (U32.v max') s sl 0ul pos;
      ICorrect () pos
    end else
      IError "parse_vllist_recast: out of bounds"
  )

let parse_vlbytes_t_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Lemma
  (parse_vlbytes_t min max == LP.parse_bounded_vlbytes_t min max)
  [SMTPat (parse_vlbytes_t min max)]
= assert_norm (parse_vlbytes_t min max == LP.parse_bounded_vlbytes_t min max)

let parse_vlbytes
  min max
= make_parser
    (LP.parse_bounded_vlbytes (U32.v min) (U32.v max))
    (LP.serialize_bounded_vlbytes (U32.v min) (U32.v max))
    (LP.jump_bounded_vlbytes (U32.v min) (U32.v max))

let get_vlbytes_spec
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (p: ptr (parse_vlbytes min max) inv)
: Tot (read_repr_spec 
    (B.buffer LP.byte & U32.t)
    True
    (fun (b, len) ->
      B.live inv.h0 b /\
      len == B.len b /\
      B.as_seq inv.h0 b `Seq.equal` FStar.Bytes.reveal (deref_spec p)
    )
    (fun _ -> False)
  )
= fun _ ->
    let l = LP.log256' (U32.v max) in
    let (base, len) = buffer_of_ptr p in
    let input = LP.make_slice base len in
    let x = LP.contents (LP.parse_bounded_vlbytes (U32.v min) (U32.v max)) inv.h0 input 0ul in
    let blen = FStar.Bytes.len x in
    LP.valid_bounded_vlbytes'_elim inv.h0 (U32.v min) (U32.v max) l input 0ul;
    LP.valid_facts (LP.parse_flbytes (U32.v blen)) inv.h0 input (U32.uint_to_t l);
    Correct (B.gsub input.LP.base (U32.uint_to_t l) blen, blen)

inline_for_extraction
let get_vlbytes_impl
  (#inv: memory_invariant)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (p: ptr (parse_vlbytes min max) inv)
: Tot (read_repr_impl
    (B.buffer LP.byte & U32.t)
    True
    (fun (b, len) ->
      B.live inv.h0 b /\
      len == B.len b /\
      B.as_seq inv.h0 b `Seq.equal` FStar.Bytes.reveal (deref_spec p)
    )
    (fun _ -> False)
    inv
    (get_vlbytes_spec min max p)
  )
= mk_read_repr_impl _ _ _ _ inv (get_vlbytes_spec min max p) (fun _ ->
    let (base, len) = buffer_of_ptr p in
    let input = LP.make_slice base len in
    let blen = LP.bounded_vlbytes_payload_length (U32.v min) (U32.v max) input 0ul in
    let b = LP.get_vlbytes_contents (U32.v min) (U32.v max) input 0ul in
    Correct (b, blen)
  )

let get_vlbytes
  #inv min max p
=
  ERead?.reflect (ReadRepr _ (get_vlbytes_impl min max p))

#push-options "--z3rlimit 32"

let put_vlbytes_impl
  #inv min max len l f
=
  mk_repr_impl _ _ _ _ _ _ inv (put_vlbytes_spec min max l) (fun b blen _ ->
    let ilen = U32.uint_to_t (LP.log256' (U32.v max)) in
    if blen `U32.lt` ilen || (blen `U32.sub` ilen) `U32.lt` len
    then begin
      LP.length_serialize_bounded_vlbytes (U32.v min) (U32.v max) (FStar.Bytes.hide (Ghost.reveal l));
      IOverflow
    end else begin
      let sl = LP.make_slice b blen in
      let _ = LP.write_bounded_integer (LP.log256' (U32.v max)) len sl 0ul in
      let b_pl = B.sub b ilen len in
      f b_pl;
      let h = HST.get () in
      LP.valid_flbytes_intro h (U32.v len) sl ilen;
      LP.valid_bounded_vlbytes_intro h (U32.v min) (U32.v max) sl 0ul len;
      ICorrect () (ilen `U32.add` len)
    end
  )

noeq
type do_while_result
  (p: parser)
  (t: Type0)
= | DWCorrect:
      (x: t) ->
      (pos: U32.t) ->
      do_while_result p t
  | DWError:
      (x: t) ->
      (vin: Ghost.erased (Parser?.t p)) ->
      (s: string) ->
      do_while_result p t
  | DWOverflow:
      (x: t) ->
      (vin: Ghost.erased (Parser?.t p)) ->
      do_while_result p t

let do_while_impl
  inv #p #t invariant measure error body x0
=
  mk_repr_impl _ _ _ _ _ _ inv (do_while_spec inv #p #t invariant measure error body x0) (fun b blen pos0 ->
    HST.push_frame ();
    let btemp : B.pointer (iresult t) = B.alloca (ICorrect x0 pos0) 1ul in
    let h0 = HST.get () in
    let vin0 = Ghost.hide (contents p h0 b 0ul pos0) in
    C.Loops.do_while
      (fun h stop ->
        B.modifies (B.loc_buffer b `B.loc_union` B.loc_all_regions_from true (HS.get_tip h0)) h0 h /\
        B.live h btemp /\
        HS.get_tip h0 == HS.get_tip h /\
        begin match B.deref h btemp with
        | ICorrect x pos ->
          U32.v pos0 <= U32.v pos /\
          valid_pos p h b 0ul pos /\ (
            let vin = contents p h b 0ul pos in
            invariant vin x (not stop) /\
            do_while_spec' inv #p #t invariant measure error body x0 (Ghost.reveal vin0) ==
              begin if stop
              then Correct (x, vin)
              else do_while_spec' inv #p #t invariant measure error body x vin
            end
          )
        | IError s ->
          stop == true /\
          do_while_spec' inv #p #t invariant measure error body x0 (Ghost.reveal vin0) == Error s
        | IOverflow ->
          stop == true /\
          begin match do_while_spec' inv #p #t invariant measure error body x0 (Ghost.reveal vin0) with
          | Error _ -> True
          | Correct (_, vout) ->
            size p vout > B.length b
          end
        end
      )
      (fun _ ->
        let ICorrect x pos = B.index btemp 0ul in
        let h = HST.get () in
        let vin = Ghost.hide (contents p h b 0ul pos) in
        assert (invariant vin x true);
        assert (do_while_spec' inv #p #t invariant measure error body x0 vin0 == do_while_spec' inv #p #t invariant measure error body x vin);
        match extract_repr_impl _ _ _ _ _ _ _ _ (destr_repr_impl _ _ _ _ _ _ _ (body x)) b blen pos with
        | ICorrect (x', cont) pos' ->
          B.upd btemp 0ul (ICorrect x' pos');
          let h' = HST.get () in
          let vin' = Ghost.hide (contents p h' b 0ul pos') in
          assert (Correct? (destr_repr_spec _ _ _ _ _ _ _ (body x) vin));
          assert (invariant vin' x' cont);
          not cont
        | IError s ->
          B.upd btemp 0ul (IError s);
          true
        | IOverflow ->
          assert (match do_while_spec' inv #p #t invariant measure error body x vin with
          | Error _ -> True
          | Correct (_, vout) ->
            begin match destr_repr_spec _ _ _ _ _ _ _ (body x) vin with
            | Error _ -> False
            | Correct (_, vout') ->
              size p vout' > B.length b /\ size p vout >= size p vout'
            end
          );
          B.upd btemp 0ul IOverflow;
          true
      );
    let res = B.index btemp 0ul in
    HST.pop_frame ();
    res
  )

#pop-options

let parse_u32
= make_parser
  LP.parse_u32
  LP.serialize_u32
  LP.jump_u32

let parse_u16
= make_parser
  LP.parse_u16
  LP.serialize_u16
  LP.jump_u16

let parse_u8
= make_parser
  LP.parse_u8
  LP.serialize_u8
  LP.jump_u8
