module MiniParse.Spec.TSum
include MiniParse.Spec.Combinators

module Seq = FStar.Seq

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
  (pt: parser tag_t)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (p: (t: tag_t) -> Tot (parser (refine_with_tag tag_of_data t)))
: Tot (parser data_t)

let parse_tagged_union #tag_t pt #data_t tag_of_data p =
  pt `and_then` (fun (tg: tag_t) ->
    parse_synth' #(refine_with_tag tag_of_data tg) (p tg) (synth_tagged_union_data tag_of_data tg)
  )

let bare_serialize_tagged_union
  (#tag_t: Type0)
  (#pt: parser tag_t)
  (st: serializer pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#p: (t: tag_t) -> Tot (parser (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Tot (bare_serializer data_t)
= fun (d: data_t) ->
  let tg = tag_of_data d in
  Seq.append (serialize st tg) (serialize (s tg) d)

let bare_serialize_tagged_union_correct
  (#tag_t: Type0)
  (#pt: parser tag_t)
  (st: serializer pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#p: (t: tag_t) -> Tot (parser (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
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
  (#pt: parser tag_t)
  (st: serializer pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#p: (t: tag_t) -> Tot (parser (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Tot (serializer (parse_tagged_union pt tag_of_data p))
= bare_serialize_tagged_union_correct st tag_of_data s;
  Serializer (bare_serialize_tagged_union st tag_of_data s)
