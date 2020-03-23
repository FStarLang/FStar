(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.TaggedUnion

module P = FStar.Pointer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(** Code

  The code of a tagged union with fields `l` is `typ l`
*)

val typ (l: P.union_typ) : P.typ

(******************************************************************************)

(* Tagging, at the logical level

  `tags l` defines "physical tags" (i.e. integers) for the fields of `l`.
*)

let tags' (l: P.struct_typ') : Tot Type0 =
  tl: list UInt32.t {
    List.Tot.length tl == List.Tot.length l /\
    List.Tot.noRepeats tl
  }

let tags (l: P.union_typ) : Tot Type0 =
  tags' l.P.fields

(* Get a field from its physical tag. *)
let rec field_of_tag'
  (#l: P.struct_typ')
  (tgs: tags' l)
  (t: UInt32.t)
: Pure (P.struct_field' l)
  (requires (List.Tot.mem t tgs))
  (ensures (fun _ -> True))
= let ((f, _) :: l') = l in
  let (t' :: tgs') = tgs in
  if t = t' then f
  else (
    assert (Cons? l');
    let ff' : string = field_of_tag' #l' tgs' t in
    ff'
  )

let field_of_tag
  (#l: P.union_typ)
  (tgs: tags l)
  (t: UInt32.t)
: Pure (P.struct_field l)
  (requires (List.Tot.mem t tgs))
  (ensures (fun _ -> True))
= field_of_tag' tgs t

(* Get the physical tag corresponding to a field. *)
let rec tag_of_field'
  (#l: P.struct_typ')
  (tgs: tags' l)
  (f: P.struct_field' l)
: Pure UInt32.t
  (requires True)
  (ensures (fun t -> List.Tot.mem t tgs))
= let ((f', _) :: l') = l in
  let (t :: tgs') = tgs in
  if f = f' then t
  else (
    assert (Cons? l');
    let ff : string = f in
    tag_of_field' #l' tgs' ff
  )

let tag_of_field
  (#l: P.union_typ)
  (tgs: tags l)
  (f: P.struct_field l)
: Pure UInt32.t
  (requires True)
  (ensures (fun t -> List.Tot.mem t tgs))
= tag_of_field' tgs f

(* Abstract predicate providing a proof that some field matches some tag.

   It is directly implemented using `tag_of_field`, but is useful on its own:
   typically, we want to only use `tag_of_field` (or `field_of_tag`) at
   normalization time, because unfolding them in Z3 does not scale. However, we
   still want to require that some field matches some tag in lemmas
   automatically used by Z3 - and at that stage, the normalizer cannot run.

   The strategy is therefore for operations that are called by the user to use
   `tag_of_field`/`field_of_tag` in a `normalize_term`, and provide as a
   post-condition that `field_matches_tag` holds. This fact can then be used by
   lemmas triggered in Z3.
*)
val field_matches_tag
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Tot Type0

val field_of_tag_of_field
  (#l: P.union_typ)
  (tgs: tags l)
  (f: P.struct_field l)
: Lemma (field_of_tag #l tgs (tag_of_field #l tgs f) == f)
  [SMTPat (field_of_tag #l tgs (tag_of_field #l tgs f))]

val tag_of_field_of_tag
  (#l: P.union_typ)
  (tgs: tags l)
  (t: UInt32.t)
: Lemma
  (requires (List.Tot.mem t tgs))
  (ensures (
    List.Tot.mem t tgs /\
    tag_of_field #l tgs (field_of_tag #l tgs t) == t
  ))
  [SMTPat (tag_of_field #l tgs (field_of_tag #l tgs t))]

val field_matches_tag_intro
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Lemma
  (requires (tag_of_field tgs f == t))
  (ensures (field_matches_tag tgs f t))

val field_matches_tag_elim
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Lemma
  (requires (field_matches_tag tgs f t))
  (ensures (tag_of_field tgs f == t))

val assert_field_matches_tag
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Lemma
  (requires (normalize_term (tag_of_field tgs f) == t))
  (ensures (field_matches_tag tgs f t))

(******************************************************************************)

(* Stateful invariant

   `valid h tgs p` states that p points to a tagged union:
   - which physical tag is readable and valid wrt `tgs`
   - which union has an active field corresponding to its physical tag
*)

val valid
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: GTot Type0

val valid_live
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: Lemma (requires (valid h tgs p))
        (ensures (P.live h p))
  [SMTPat (valid h tgs p)]


(******************************************************************************)

(* Operations *)

val gread_tag
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: GTot UInt32.t

val read_tag
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
: HST.Stack UInt32.t
  (requires (fun h -> valid h tgs p))
  (ensures (fun h0 t h1 ->
    h0 == h1 /\
    List.Tot.mem t tgs /\
    t == gread_tag h0 tgs p))


val gfield
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
: GTot (p': P.pointer (P.typ_of_struct_field l f) { P.includes p p' })


val field
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
: HST.Stack (P.pointer (P.typ_of_struct_field l f))
  (requires (fun h ->
    valid h tgs p /\
    gread_tag h tgs p == normalize_term (tag_of_field tgs f)
  ))
  (ensures (fun h0 p' h1 ->
    h0 == h1 /\
    field_matches_tag tgs f (gread_tag h0 tgs p) /\
    p' == gfield tgs p f
  ))


val write
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (v: P.type_of_typ (P.typ_of_struct_field l f))
: HST.Stack unit
  (requires (fun h ->
    P.live h p
  ))
  (ensures (fun h0 _ h1 ->
    P.live h0 p /\ P.live h1 p /\
    P.modifies_1 p h0 h1 /\
    P.readable h1 p /\
    valid h1 tgs p /\
    gread_tag #l h1 tgs p == normalize_term (tag_of_field tgs f) /\
    field_matches_tag tgs f (gread_tag h1 tgs p) /\
    P.gread h1 (gfield tgs p f) == v
  ))

val write_tag
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
: HST.Stack unit
  (requires (fun h ->
    valid h tgs p
  ))
  (ensures (fun h0 _ h1 ->
    valid h0 tgs p /\ valid h1 tgs p
    /\ P.modifies_1 p h0 h1
    /\ gread_tag #l h1 tgs p == normalize_term (tag_of_field tgs f)
    /\ field_matches_tag tgs f (gread_tag h1 tgs p)
  ))

(******************************************************************************)

(* Lemmas *)

val includes_gfield
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
: Lemma
  (requires True)
  (ensures (P.includes p (gfield tgs p f)))

let includes_gfield_gen
  (#t: P.typ)
  (q: P.pointer t)
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
: Lemma
  (requires (P.includes q p))
  (ensures (P.includes q (gfield tgs p f)))
  [SMTPat (P.includes q (gfield tgs p f))]
= includes_gfield tgs p f;
  P.includes_trans q p (gfield tgs p f)

val live_gfield
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h: HS.mem)
: Lemma
  (P.live h (gfield tgs p f) <==> P.live h p)
  [SMTPat (P.live h (gfield tgs p f))]

val modifies_1_valid
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h0 h1: HS.mem)
  (#t': P.typ)
  (p': P.pointer t')
: Lemma
  (requires (
    valid h0 tgs p /\
    field_matches_tag tgs f (gread_tag h0 tgs p) /\
    P.modifies_1 (gfield tgs p f) h0 h1 /\
    P.includes (gfield tgs p f) p' /\
    P.readable h1 p'
  ))
  (ensures (valid h1 tgs p))
  [SMTPat (valid #l h0 tgs p);
    SMTPat (P.readable h1 p');
    SMTPat (gfield #l tgs p f)]

val modifies_1_field_tag
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h0 h1: HS.mem)
: Lemma
  (requires (
    valid h0 tgs p /\
    P.modifies_1 (gfield tgs p f) h0 h1
  ))
  (ensures (gread_tag h1 tgs p == gread_tag h0 tgs p))
  [SMTPat (valid #l h0 tgs p); SMTPat (gfield tgs p f); SMTPat (gread_tag h1 tgs p)]

val modifies_1_field
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h0 h1: HS.mem)
: Lemma
  (requires (valid h0 tgs p /\ P.modifies_1 (gfield tgs p f) h0 h1))
  (ensures (P.modifies_1 p h0 h1))
  [SMTPat (valid #l h0 tgs p); SMTPat (P.modifies_1 (gfield #l tgs p f) h0 h1)]

val modifies_1_field_tag_equal
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h0 h1: HS.mem)
: Lemma
  (requires (valid h0 tgs p /\ P.modifies_1 (gfield tgs p f) h0 h1))
  (ensures (gread_tag h0 tgs p == gread_tag h1 tgs p))
  [SMTPat (valid h0 tgs p); SMTPat (gread_tag h1 tgs p); SMTPat (gfield tgs p f)]

val readable_intro
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h: HS.mem)
: Lemma
  (requires (
    valid h tgs p /\
    P.readable h (gfield tgs p f)
  ))
  (ensures (P.readable h p))
  [SMTPat (valid #l h tgs p); SMTPat (P.readable h (gfield #l tgs p f))]


val readable_field
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h: HS.mem)
: Lemma
  (requires (
    valid h tgs p /\ P.readable h p /\
    field_matches_tag tgs f (gread_tag h tgs p)
  ))
  (ensures (P.readable h (gfield tgs p f)))
  [SMTPat (P.readable h (gfield #l tgs p f))]


(******************************************************************************)

(* Logical representation of a tagged union.
*)

let raw (l: P.union_typ) : Tot Type0 = P.type_of_typ (typ l)

val raw_get_tag (#l: P.union_typ) (tu: raw l): Tot UInt32.t
val raw_get_field (#l: P.union_typ) (tu: raw l): GTot (P.struct_field l)

val raw_get_value (#l: P.union_typ) (tu: raw l) (f: P.struct_field l)
: Pure (P.type_of_typ (P.typ_of_struct_field l f))
  (requires (raw_get_field tu == f))
  (ensures (fun _ -> True))

let matching_tags
  (#l: P.union_typ)
  (raw_tu: raw l)
  (tgs: tags l)
: Tot Type
=
  let t = raw_get_tag raw_tu in
  List.Tot.mem t tgs /\
  field_of_tag tgs t == raw_get_field raw_tu


let t (l: P.union_typ) (tgs: tags l) : Tot Type0 =
  tu : raw l { matching_tags tu tgs }

let get_field (#l: P.union_typ) (#tgs: tags l) (tu: t l tgs)
: GTot (P.struct_field l)
=
  raw_get_field tu

let get_tag (#l: P.union_typ) (#tgs: tags l) (tu: t l tgs)
: Pure (UInt32.t)
  (requires True)
  (ensures (fun t ->
    List.Tot.mem t tgs /\
    t == tag_of_field tgs (get_field tu)))
=
  raw_get_tag #l tu

let get_value
  (#l: P.union_typ) (#tgs: tags l)
  (tu: t l tgs)
  (f: P.struct_field l)
: Pure (P.type_of_typ (P.typ_of_struct_field l f))
  (requires (get_field tu == f))
  (ensures (fun _ -> True))
=
  raw_get_value #l tu f

(* Lemma: "valid p ==> matching_tags (gread p)" *)

val valid_matching_tags
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: Lemma
  (requires (valid h tgs p))
  (ensures (matching_tags (P.gread h p) tgs))
  [SMTPatOr [[SMTPat (valid h tgs p)]; [SMTPat (matching_tags (P.gread h p) tgs)]]]
