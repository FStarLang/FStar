module LowParseWriters.NoHoare
include LowParseWriters

inline_for_extraction
let read_repr
  (t: Type)
  (inv: memory_invariant)
: Tot Type
= read_repr t True (fun _ -> True) (fun _ -> True) inv

inline_for_extraction
let read_reify_trivial
  (#a: Type)
  (#l: memory_invariant)
  (f: (unit -> ERead a True (fun _ -> True) (fun _ -> True) l))
: Tot (read_repr a l)
= reify (f ())

inline_for_extraction
let read_return_conv
  (t: Type)
  (x: t)
  (inv: memory_invariant)
  ()
: ERead t True (fun _ -> True) (fun _ -> True) inv
= x

inline_for_extraction
let read_return
  (t: Type)
  (x: t)
  (inv: memory_invariant)
: Tot (read_repr t inv)
=
  read_reify_trivial (read_return_conv t x inv)

inline_for_extraction
let read_bind_conv
  (a:Type) (b:Type)
  (l: memory_invariant)
  (f_bind : read_repr a l)
  (g : (x: a -> read_repr b l))
  ()
: ERead b True (fun _ -> True) (fun _ -> True) l
= let x = ERead?.reflect f_bind in
  ERead?.reflect (g x)

inline_for_extraction
let read_bind
  (a:Type) (b:Type)
  (l: memory_invariant)
  (f_bind : read_repr a l)
  (g : (x: a -> read_repr b l))
: Tot (read_repr b l)
= read_reify_trivial (read_bind_conv a b l f_bind g)

inline_for_extraction
let read_subcomp_conv (a:Type)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:read_repr a l)
  (sq: squash (l `memory_invariant_includes` l'))
  ()
: ERead a True (fun _ -> True) (fun _ -> True) l'
= let x = ERead?.reflect f_subcomp in
  x

inline_for_extraction
let read_subcomp (a:Type)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:read_repr a l)
: Pure (read_repr a l')
  (requires (l `memory_invariant_includes` l'))
  (ensures (fun _ -> True))
= read_reify_trivial (read_subcomp_conv a l l' f_subcomp ())

inline_for_extraction
let read_if_then_else (a:Type)
  (l:memory_invariant)
  (f_ifthenelse:read_repr a l)
  (g:read_repr a l)
  (p:bool)
: Tot Type
= read_repr a l

// [@@ smt_reifiable_layered_effect ]
reifiable reflectable total
layered_effect {
  TRead : a:Type -> (memory_invariant) -> Effect
  with
  repr = read_repr;
  return = read_return;
  bind = read_bind;
  subcomp = read_subcomp;
  if_then_else = read_if_then_else
}

inline_for_extraction
let lift_pure_read_conv (a:Type) (wp:pure_wp a)
  (l: memory_invariant)
  (f_pure:unit -> PURE a wp)
  (sq: squash (wp (fun _ -> True)))
  ()
: ERead a True (fun _ -> True) (fun _ -> True) l
= f_pure ()

inline_for_extraction
let lift_pure_read' (a:Type) (wp:pure_wp a)
  (l: memory_invariant)
  (f_pure: eqtype_as_type unit -> PURE a wp)
: Pure (read_repr a l)
  (requires (wp (fun _ -> True)))
  (ensures (fun _ -> True))
= read_reify_trivial (lift_pure_read_conv a wp l f_pure ())

sub_effect PURE ~> TRead = lift_pure_read'

(*
let read_bind_spec'
  (inv: memory_invariant)
  (a b: Type)
  (f: (unit -> TRead a inv))
  (g: (a -> TRead b inv))
: GTot (result b)
=
   match ReadRepr?.spec (reify (f ())) () with
    | Error e -> Error e
    | Correct x -> ReadRepr?.spec (reify (g x)) ()

let read_bind_impl'
  (inv: memory_invariant)
  (a b: Type)
  (f: (unit -> TRead a inv))
  (g: (a -> TRead b inv))
: TRead b inv
= let x = f () in g x

let read_bind_correct
  (inv: memory_invariant)
  (a b: Type)
  (f: (unit -> TRead a inv))
  (g: (a -> TRead b inv))
: Lemma
      (ReadRepr?.spec (reify (read_bind_impl' inv a b f g)) () == read_bind_spec' inv a b f g)
= assert_norm
    (ReadRepr?.spec (reify (read_bind_impl' inv a b f g)) () == read_bind_spec' inv a b f g)
*)

inline_for_extraction
let tread_of_eread // NOTE: I could define it as a lift (sub_effect), but I prefer to do it explicitly to avoid F* generating pre and postconditions
  (#a: Type)
  (#l: memory_invariant)
  (f: unit -> ERead a True (fun _ -> True) (fun _ -> True) l)
: TRead a l
= TRead?.reflect (read_reify_trivial f)

inline_for_extraction
let eread_of_tread
  (#a: Type)
  (#l: memory_invariant)
  (f: unit -> TRead a l)
: ERead a True (fun _ -> True) (fun _ -> True) l
= ERead?.reflect (reify (f ()))

inline_for_extraction
let failwith
  (#a: Type)
  (#inv: memory_invariant)
  (s: string)
: TRead a inv
= tread_of_eread (fun _ -> failwith s)

module B = LowStar.Buffer
module U32 = FStar.UInt32

inline_for_extraction
let buffer_index
  (#t: Type)
  (#inv: memory_invariant)
  (b: B.buffer t)
  (i: U32.t {
      B.live inv.h0 b /\
      B.loc_buffer b `B.loc_disjoint` inv.lwrite /\
      U32.v i < B.length b
  })
: TRead t inv
= tread_of_eread (fun _ -> buffer_index b i)

inline_for_extraction
let buffer_sub
  (#t: Type)
  (#inv: memory_invariant)
  (b: B.buffer t)
  (i: U32.t)
  (len: Ghost.erased U32.t {
      B.live inv.h0 b /\
      B.loc_buffer b `B.loc_disjoint` inv.lwrite /\
      U32.v i + U32.v len <= B.length b
  })
: TRead (B.buffer t) inv
= tread_of_eread (fun _ -> buffer_sub b i len)

inline_for_extraction
let repr
  (a: Type u#x)
  (r_in: parser) (r_out: parser)
  (l: memory_invariant)
: Tot Type
=
  repr a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l

inline_for_extraction
let reify_trivial
  (#a: Type)
  (#l: memory_invariant)
  (#p1 #p2: parser)
  (f: (unit -> EWrite a p1 p2 (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l))
: Tot (repr a p1 p2 l)
= reify (f ())

inline_for_extraction
let return_conv
  (t: Type)
  (x: t)
  (r: parser)
  (inv: memory_invariant)
  ()
: EWrite t r r (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv
= x

inline_for_extraction
let returnc
  (t: Type)
  (x: t)
  (r: parser)
  (inv: memory_invariant)
: Tot (repr t r r inv)
= reify_trivial (return_conv t x r inv)

inline_for_extraction
let bind_conv (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f: parser)
  (r_out_g: parser)
  (l: memory_invariant)
  (f_bind : repr a r_in_f r_out_f l)
  (g : (x: a -> repr b (r_out_f) r_out_g l))
  ()
: EWrite b r_in_f r_out_g (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l
= let x = EWrite?.reflect f_bind in
  EWrite?.reflect (g x)

inline_for_extraction
let bind (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f: parser)
  (r_out_g: parser)
  (l: memory_invariant)
  (f_bind : repr a r_in_f r_out_f l)
  (g : (x: a -> repr b (r_out_f) r_out_g l))
: Tot (repr b r_in_f r_out_g l)
= reify_trivial (bind_conv a b r_in_f r_out_f r_out_g l f_bind g)

noeq
type valid_rewrite_t'
  (p1: parser)
  (p2: parser)
=
| ValidSynth:
  (f: (Parser?.t p1 -> GTot (Parser?.t p2))) ->
  (v: LowParseWriters.valid_rewrite_t p1 p2 (fun _ -> True) f) ->
  valid_rewrite_t' p1 p2

let valid_rewrite_prop (p1 p2: parser) : GTot Type0 =
  exists (x: valid_rewrite_t' p1 p2) . True

(*
// unfold
let valid_rewrite_t (p1 p2: parser) : Tot Type0 =
  squash (valid_rewrite_prop p1 p2)
*)

let tvalid_rewrite_of_evalid_rewrite
  (#p1: parser)
  (#p2: parser)
  (#precond: pre_t p1)
  (#f: (x: Parser?.t p1 { precond x }) -> GTot (Parser?.t p2))
  (v: LowParseWriters.valid_rewrite_t p1 p2 precond f { forall (x: Parser?.t p1) . precond x })
: Tot (squash (valid_rewrite_prop p1 p2))
= let _ = ValidSynth
    f
    (valid_rewrite_implies _ _ _ _ v _ _)
  in
  ()

let evalid_rewrite_of_tvalid_rewrite_f
  (#p1: parser)
  (#p2: parser)
  (v: squash (valid_rewrite_prop p1 p2))
  (x: Parser?.t p1)
: GTot (Parser?.t p2)
= let v' : valid_rewrite_t' p1 p2 = FStar.IndefiniteDescription.indefinite_description_ghost (valid_rewrite_t' p1 p2) (fun _ -> True) in
  ValidSynth?.f v' x

let evalid_rewrite_of_tvalid_rewrite
  (#p1: parser)
  (#p2: parser)
  (v: squash (valid_rewrite_prop p1 p2))
: Tot (LowParseWriters.valid_rewrite_t p1 p2 (fun _ -> True) (evalid_rewrite_of_tvalid_rewrite_f v))
= valid_rewrite_implies _ _ _ _ (ValidSynth?.v (FStar.IndefiniteDescription.indefinite_description_ghost (valid_rewrite_t' p1 p2) (fun _ -> True))) _ _

let valid_rewrite_refl
  (p: parser)
: Lemma
  (valid_rewrite_prop p p)
  [SMTPat (valid_rewrite_prop p p)]
= let x = tvalid_rewrite_of_evalid_rewrite #p #p #(fun _ -> True) #(fun x -> x) ({
    valid_rewrite_valid = (fun h b pos pos' -> ());
    valid_rewrite_size = (fun x -> ());
  })
  in
  ()

inline_for_extraction
let valid_rewrite_repr
  (#p1: parser)
  (#p2: parser)
  (#inv: memory_invariant)
  (v: squash (valid_rewrite_prop p1 p2))
: Tot (repr unit p1 p2 inv)
= reify_trivial (fun _ -> valid_rewrite _ _ _ _ _ (evalid_rewrite_of_tvalid_rewrite v))

inline_for_extraction
let subcomp_conv
  (a:Type)
  (r_in:parser) (r_out: parser)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:repr a r_in r_out l)
  (sq: squash (
    l `memory_invariant_includes` l'
  ))
  ()
: EWrite a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l'
= let x = EWrite?.reflect f_subcomp in
  x

inline_for_extraction
let subcomp1
  (a:Type)
  (r_in:parser) (r_out: parser)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:repr a r_in r_out l)
: Pure (repr a r_in r_out l')
  (requires (
    l `memory_invariant_includes` l'
  ))
  (ensures (fun _ -> True))
=
  reify_trivial (subcomp_conv a r_in r_out l l' f_subcomp ())

inline_for_extraction
let subcomp2
  (a:Type)
  (r_in:parser) (r_out r_out': parser)
  (l:memory_invariant)
  (f_subcomp:repr a r_in r_out l)
: Pure (repr a r_in r_out' l)
  (requires (
    valid_rewrite_prop r_out r_out'
  ))
  (ensures (fun _ -> True))
=
  bind a a r_in r_out r_out' l f_subcomp (fun x -> bind unit a r_out r_out' r_out' l (valid_rewrite_repr ()) (fun _ -> returnc a x r_out' l))

inline_for_extraction
let subcomp
  (a:Type)
  (r_in:parser) (r_out r_out': parser)
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:repr a r_in r_out l)
: Pure (repr a r_in r_out' l')
  (requires (
    l `memory_invariant_includes` l' /\
    valid_rewrite_prop r_out r_out'
  ))
  (ensures (fun _ -> True))
= subcomp2 a r_in r_out r_out' l' (subcomp1 a r_in r_out l l' f_subcomp)

let if_then_else (a:Type)
  (r_in:parser) (r_out: parser)
  (l:memory_invariant)
  (f_ifthenelse:repr a r_in r_out l)
  (g:repr a r_in r_out l)
  (p:bool)
: Tot Type
= repr a r_in r_out
    l

// [@@smt_reifiable_layered_effect]
[@@allow_informative_binders]
reifiable reflectable total
layered_effect {
  TWrite : a:Type -> (pin: parser) -> (pout: (parser)) -> (memory_invariant) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

inline_for_extraction
let lift_read_conv
  (a: Type)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a inv)
  ()
: EWrite a r r (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv
= let x = ERead?.reflect f_read_spec in
  x

inline_for_extraction
let lift_read
  (a: Type)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a inv)
: Tot (repr a r r inv)
= reify_trivial (lift_read_conv a inv r f_read_spec)

sub_effect TRead ~> TWrite = lift_read

let destr_repr_spec
  (#a:Type u#x)
  (#r_in: parser)
  (#r_out: parser)
  (#l: memory_invariant)
  ($f_destr_spec: unit -> TWrite a r_in r_out l)
: Tot (repr_spec a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True))
= Repr?.spec (reify (f_destr_spec ()))

inline_for_extraction
let destr_repr_impl
  (#a:Type u#x)
  (#r_in: parser)
  (#r_out: parser)
  (#l: memory_invariant)
  (f_destr_spec: unit -> TWrite a r_in r_out l)
: Tot (repr_impl a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l (destr_repr_spec f_destr_spec))
= Repr?.impl (reify (f_destr_spec ()))

module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack

inline_for_extraction
let extract_t
  (#a:Type u#x)
  (#r_in: parser)
  (#r_out: parser)
  (l: memory_invariant)
  ($f_destr_spec: unit -> TWrite a r_in r_out l)
: Tot Type
=
  (b: B.buffer u8 { l.lwrite `B.loc_includes` B.loc_buffer b }) ->
  (len: U32.t { len == B.len b }) ->
  (pos1: buffer_offset b) ->
  HST.Stack (iresult a)
  (requires (fun h ->
    B.modifies l.lwrite l.h0 h /\
    HS.get_tip l.h0 `HS.includes` HS.get_tip h /\
    valid_pos r_in h b 0ul pos1
  ))
  (ensures (fun h res h' ->
    valid_pos r_in h b 0ul pos1 /\
    B.modifies (B.loc_buffer b) h h' /\ (
    let v_in = contents r_in h b 0ul pos1 in
    begin match destr_repr_spec f_destr_spec v_in, res with
    | Correct (v, v_out), ICorrect v' pos2 ->
      U32.v pos1 <= U32.v pos2 /\
      valid_pos (r_out) h' b 0ul pos2 /\
      v' == v /\
      v_out == contents (r_out) h' b 0ul pos2
    | Correct (v, v_out), IOverflow ->
      size (r_out) v_out > B.length b
    | Error s, IError s' ->
      s == s'
    | Error _, IOverflow ->
      (* overflow happened in implementation before specification could reach error *)
      True
    | _ -> False
    end
  )))

inline_for_extraction
let extract
  (#a:Type u#x)
  (#r_in: parser)
  (#r_out: parser)
  (l: memory_invariant)
  ($f_destr_spec: unit -> TWrite a r_in r_out l)
: Tot (extract_t l f_destr_spec)
= extract_repr_impl _ _ _ _ _ _ _ _ (destr_repr_impl f_destr_spec)

inline_for_extraction
let wrap_extracted_impl
  (#a:Type u#x)
  (#r_in: parser)
  (#r_out: parser)
  (l: memory_invariant)
  (f_destr_spec: unit -> TWrite a r_in r_out l)
  (e: extract_t l f_destr_spec)
: TWrite a r_in r_out l
= TWrite?.reflect (Repr (destr_repr_spec f_destr_spec) (
    mk_repr_impl
      a r_in r_out (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l (destr_repr_spec f_destr_spec) (fun b len pos1 -> e b len pos1)
  ))

let bind_spec'
  (inv: memory_invariant)
  (p1 p2 p3: parser)
  (a b: Type)
  (f: (unit -> TWrite a p1 p2 inv))
  (g: (a -> unit -> TWrite b p2 p3 inv))
  (v1: Parser?.t p1)
: GTot (result (b & Parser?.t p3))
=
   match destr_repr_spec f v1 with
    | Error e -> Error e
    | Correct (x, v2) -> destr_repr_spec (g x) v2

let bind_spec2
  (inv: memory_invariant)
  (p1 p2 p3: parser)
  (a b: Type)
  (f: (unit -> TWrite a p1 p2 inv))
  (g: (a -> unit -> TWrite b p2 p3 inv))
  (v1: Parser?.t p1)
: GTot (result (b & Parser?.t p3))
=
   match Repr?.spec (reify (f ())) v1 with
    | Error e -> Error e
    | Correct (x, v2) -> Repr?.spec (reify (g x ())) v2

let bind_impl'
  (inv: memory_invariant)
  (p1 p2 p3: parser)
  (a b: Type)
  (f: (unit -> TWrite a p1 p2 inv))
  (g: (a -> unit -> TWrite b p2 p3 inv))
  ()
: TWrite b p1 p3 inv
= let x = f () in g x ()

inline_for_extraction
let twrite_of_ewrite // NOTE: I could define it as a lift (sub_effect), but I prefer to do it explicitly to avoid F* generating pre and postconditions
  (#a: Type)
  (#l: memory_invariant)
  (#p1 #p2: parser)
  (f: unit -> EWrite a p1 p2 (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l)
: TWrite a p1 p2 l
= TWrite?.reflect (reify_trivial f)

inline_for_extraction
let wfailwith
  (#a: Type)
  (#inv: memory_invariant)
  (#rin #rout: parser)  
  (s: string)
: TWrite a rin rout inv
= twrite_of_ewrite (fun _ -> wfailwith s)

inline_for_extraction
let ewrite_of_twrite
  (#a: Type)
  (#l: memory_invariant)
  (#p1 #p2: parser)
  ($f: unit -> TWrite a p1 p2 l)
: EWrite a p1 p2 (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) l
= EWrite?.reflect (reify (f ()))

inline_for_extraction
let frame
  (#a: Type)
  (#fr: parser)
  (#p: parser)
  (#l: memory_invariant)
  ($f: unit ->
    TWrite a parse_empty p l
  )
: TWrite a fr (fr `parse_pair` p)
    l
=
  twrite_of_ewrite (fun _ -> frame' _ _ _ _ (fun _ -> ewrite_of_twrite f))

let valid_rewrite_compose
  (#p1: parser)
  (#p2: parser)
  (v12: squash (valid_rewrite_prop p1 p2))
  (#p3: parser)
  (v23: squash (valid_rewrite_prop p2 p3))
: Tot (squash (valid_rewrite_prop p1 p3))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_compose _ _ _ _ (evalid_rewrite_of_tvalid_rewrite v12) _ _ _ (evalid_rewrite_of_tvalid_rewrite v23))

inline_for_extraction
let valid_rewrite
  (#p1: parser)
  (#p2: parser)
  (#inv: memory_invariant)
  (v: squash (valid_rewrite_prop p1 p2))
: TWrite unit p1 p2 inv
= twrite_of_ewrite (fun _ -> valid_rewrite _ _ _ _ _ (evalid_rewrite_of_tvalid_rewrite v))

inline_for_extraction
let cast
  (#p1: parser)
  (#p2: parser)
  (#inv: memory_invariant)
  (v: squash (valid_rewrite_prop p1 p2))
  (x1: ptr p1 inv)
: Tot (ptr p2 inv)
= cast _ _ _ _ (evalid_rewrite_of_tvalid_rewrite v) _ x1

let valid_rewrite_parse_pair_assoc_1
  (p1 p2 p3: parser)
: Tot (squash (valid_rewrite_prop ((p1 `parse_pair` p2) `parse_pair` p3) (p1 `parse_pair` (p2 `parse_pair` p3))))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_pair_assoc_1 p1 p2 p3)

let valid_rewrite_parse_pair_assoc_2
  (p1 p2 p3: parser)
: Tot (squash (valid_rewrite_prop (p1 `parse_pair` (p2 `parse_pair` p3)) ((p1 `parse_pair` p2) `parse_pair` p3)))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_pair_assoc_2 p1 p2 p3)

let valid_rewrite_parse_pair_compat_l
  (p: parser)
  (#p1 #p2: parser)
  (v: squash (valid_rewrite_prop p1 p2))
: Tot (squash (valid_rewrite_prop (p `parse_pair` p1) (p `parse_pair` p2)))
= tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_pair_compat_l p _ _ _ _ (evalid_rewrite_of_tvalid_rewrite v))

let valid_rewrite_parse_pair_compat_r
  (p: parser)
  (#p1 #p2: parser)
  (v: squash (valid_rewrite_prop p1 p2))
: Tot (squash (valid_rewrite_prop (p1 `parse_pair` p) (p2 `parse_pair` p)))
=
  tvalid_rewrite_of_evalid_rewrite (valid_rewrite_parse_pair_compat_r p _ _ _ _ (evalid_rewrite_of_tvalid_rewrite v))

inline_for_extraction
let cat
  (#inv: memory_invariant)
  (#p: parser)
  (x: ptr p inv)
: TWrite unit parse_empty p inv
= twrite_of_ewrite (fun _ -> cat x)
