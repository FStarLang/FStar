module MiniParse.Spec.TSum
include MiniParse.Spec.Combinators
include MiniParse.Spec.Int

module Seq = FStar.Seq
module U16 = FStar.UInt16

inline_for_extraction
let refine_with_tag (#tag_t: Type0) (#data_t: Type0) (tag_of_data: (data_t -> GTot tag_t)) (x: tag_t) : Tot Type0 =
  (y: data_t { tag_of_data y == x } )

inline_for_extraction
let synth_tagged_union_data
  (#tag_t: Type0)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (tg: tag_t)
  (x: refine_with_tag tag_of_data tg)
: Tot data_t
= x

val parse_tagged_union
  (#tag_t: Type0)
  (pt: parser_spec tag_t)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (p: (t: tag_t) -> Tot (parser_spec (refine_with_tag tag_of_data t)))
: Tot (parser_spec data_t)

let parse_tagged_union #tag_t pt #data_t tag_of_data p =
  pt `and_then` (fun (tg: tag_t) ->
    parse_synth' #(refine_with_tag tag_of_data tg) (p tg) (synth_tagged_union_data tag_of_data tg)
  )

let bare_serialize_tagged_union
  (#tag_t: Type0)
  (#pt: parser_spec tag_t)
  (st: serializer_spec pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#p: (t: tag_t) -> Tot (parser_spec (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer_spec (p t)))
: Tot (bare_serializer data_t)
= fun (d: data_t) ->
  let tg = tag_of_data d in
  Seq.append (serialize st tg) (serialize (s tg) d)

let bare_serialize_tagged_union_correct
  (#tag_t: Type0)
  (#pt: parser_spec tag_t)
  (st: serializer_spec pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#p: (t: tag_t) -> Tot (parser_spec (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer_spec (p t)))
: Lemma
  (ensures (serializer_correct (parse_tagged_union pt tag_of_data p) (bare_serialize_tagged_union st tag_of_data s)))
= (* same proof as nondep_then *)
  let prf
    (x: data_t)
  : Lemma (parse (parse_tagged_union pt tag_of_data p) (bare_serialize_tagged_union st tag_of_data s x) == Some (x, Seq.length (bare_serialize_tagged_union  st tag_of_data s x)))
  = let t = tag_of_data x in
    let (u: refine_with_tag tag_of_data t) = x in
    let v1' = parse pt (bare_serialize_tagged_union st tag_of_data s x) in
    let v1 = parse pt (serialize st t) in
    assert (Some? v1);
    assert (no_lookahead_on (coerce_to_bare_parser _ pt) (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    let (Some (_, len')) = parse pt (serialize st t) in
    assert (len' == Seq.length (serialize st t));
    assert (len' <= Seq.length (bare_serialize_tagged_union st tag_of_data s x));
    assert (Seq.slice (serialize st t) 0 len' == serialize st t);
    seq_slice_append_l (serialize st t) (serialize (s t) u);
    assert (no_lookahead_on_precond (coerce_to_bare_parser _ pt) (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (no_lookahead_on_postcond (coerce_to_bare_parser _ pt) (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (Some? v1');
    assert (injective_precond (coerce_to_bare_parser _ pt) (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (injective_postcond (coerce_to_bare_parser _ pt) (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    let (Some (x1, len1)) = v1 in
    let (Some (x1', len1')) = v1' in
    assert (x1 == x1');
    assert ((len1 <: nat) == (len1' <: nat));
    assert (x1 == t);
    assert (len1 == Seq.length (serialize st t));
    assert (bare_serialize_tagged_union st tag_of_data s x == Seq.append (serialize st t) (serialize (s t) u));
    seq_slice_append_r (serialize st t) (serialize (s t) u);
    ()
  in
  Classical.forall_intro prf

let serialize_tagged_union
  (#tag_t: Type0)
  (#pt: parser_spec tag_t)
  (st: serializer_spec pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#p: (t: tag_t) -> Tot (parser_spec (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer_spec (p t)))
: Tot (serializer_spec (parse_tagged_union pt tag_of_data p))
= bare_serialize_tagged_union_correct st tag_of_data s;
  Serializer (bare_serialize_tagged_union st tag_of_data s)

noeq
type sum_case'
  (#tag_t: Type0)
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot tag_t))
  (case: tag_t)
= | Case:
    (ty: Type0) ->
    (p: parser_spec ty) -> 
    (s: serializer_spec p) ->
    (ty_to_data: (ty -> Tot (refine_with_tag tag_of_data case))) ->
    (data_to_ty: (refine_with_tag tag_of_data case -> Tot ty)) ->
    (u: squash (synth_inverse ty_to_data data_to_ty /\ synth_inverse data_to_ty ty_to_data)) ->
    sum_case' tag_of_data case

let sum_case = sum_case'

let parse_sum
  (#tag_t: Type0)
  (pt: parser_spec tag_t)
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot tag_t))
  (cases: ((x: tag_t) -> Tot (sum_case tag_of_data x)))
: Tot (parser_spec data_t)
= parse_tagged_union
    pt
    tag_of_data
    (fun x -> parse_synth ((cases x).p) ((cases x).ty_to_data) ((cases x).data_to_ty))

let serialize_sum
  (#tag_t: Type0)
  (#pt: parser_spec tag_t)
  (st: serializer_spec pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot tag_t))
  (cases: ((x: tag_t) -> Tot (sum_case tag_of_data x)))
: Tot (serializer_spec (parse_sum pt tag_of_data cases))
= serialize_tagged_union
    st
    tag_of_data
    (fun x -> serialize_synth ((cases x).s) ((cases x).ty_to_data) ((cases x).data_to_ty) ())

inline_for_extraction
let bounded_u16_match_t_aux
  (b: nat)
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot (bounded_u16 b)))
  (b': nat { b' <= b } )
: Tot Type
= (x: bounded_u16 b { U16.v x < b' } ) -> Tot (sum_case tag_of_data x)

inline_for_extraction
let bounded_u16_match_t_intro
  (b: nat)
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot (bounded_u16 b)))
  (j: bounded_u16_match_t_aux b tag_of_data b)
  (x: bounded_u16 b)
: Tot (sum_case tag_of_data x)
= j x

inline_for_extraction
let bounded_u16_match_t_aux_nil
  (b: nat)
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot (bounded_u16 b)))
: Tot (bounded_u16_match_t_aux b tag_of_data 0)
= fun _ -> false_elim ()

inline_for_extraction
let bounded_u16_match_t_aux_cons_nil
  (b: nat { b > 0 } )
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot (bounded_u16 b)))
  (y: sum_case #_ #(bounded_u16 b) tag_of_data 0us)
: Tot (bounded_u16_match_t_aux b tag_of_data 1)
= fun (x: bounded_u16 b { U16.v x < 1 } )  -> (
  y
  )

inline_for_extraction
let bounded_u16_match_t_aux_cons
  (b: nat { b > 0 } )
  (#data_t: Type0)
  (tag_of_data: (data_t -> Tot (bounded_u16 b)))
  (b' : nat {b' < b /\ b' < 256 })
  (b_: bounded_u16 b { U16.v b_ == b' } )
  (z: sum_case #_ #(bounded_u16 b) tag_of_data b_)
  (y: bounded_u16_match_t_aux b tag_of_data b')
 : Tot (bounded_u16_match_t_aux b tag_of_data (b' + 1))
= fun (x: bounded_u16 b { U16.v x < b' + 1 } ) ->
  if x `U16.lt` U16.uint_to_t b'
  then y x
  else (z <: sum_case #_ #(bounded_u16 b) tag_of_data x)
