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

(** Code of a tagged union *)

let typ_l (l: P.union_typ) = {
  P.name = "__tagged__" ^ l.P.name;
  P.fields = P.([("tag", TBase TUInt32); ("union", TUnion l)]);
}

let tag_field (l: P.union_typ) : P.struct_field (typ_l l) = "tag"
let union_field (l: P.union_typ) : P.struct_field (typ_l l) = "union"

let typ (l: P.union_typ) : P.typ = P.TStruct (typ_l l)

(******************************************************************************)

(* Tagging, at the logical level *)

(* Abstract predicate providing a proof that some field matches some tag. *)

let field_matches_tag
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Tot Type0
= tag_of_field tgs f == t

let rec field_of_tag_of_field'
  (#l: P.struct_typ')
  (tgs: tags' l)
  (f: P.struct_field' l)
: Lemma (field_of_tag' #l tgs (tag_of_field' #l tgs f) == f)
  [SMTPat (field_of_tag' #l tgs (tag_of_field' #l tgs f))]
= let ((f', _) :: l') = l in
  let (t' :: tgs') = tgs in
  if f = f' then ()
  else (
    let ff : string = f in
    field_of_tag_of_field' #l' tgs' ff
  )

let field_of_tag_of_field
  (#l: P.union_typ)
  (tgs: tags l)
  (f: P.struct_field l)
: Lemma (field_of_tag #l tgs (tag_of_field #l tgs f) == f)
  [SMTPat (field_of_tag #l tgs (tag_of_field #l tgs f))]
= field_of_tag_of_field' tgs f

let rec tag_of_field_of_tag'
  (#l: P.struct_typ')
  (tgs: tags' l)
  (t: UInt32.t)
: Lemma
  (requires (List.Tot.mem t tgs))
  (ensures (
    List.Tot.mem t tgs /\
    tag_of_field' #l tgs (field_of_tag' #l tgs t) == t
  ))
  [SMTPat (tag_of_field' #l tgs (field_of_tag' #l tgs t))]
= let ((f', _) :: l') = l in
  let (t' :: tgs') = tgs in
  if t = t' then ()
  else (
    tag_of_field_of_tag' #l' tgs' t
  )

let tag_of_field_of_tag
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
= tag_of_field_of_tag' tgs t

let field_matches_tag_intro
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Lemma
  (requires (tag_of_field tgs f == t))
  (ensures (field_matches_tag tgs f t))
= ()

let field_matches_tag_elim
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Lemma
  (requires (field_matches_tag tgs f t))
  (ensures (tag_of_field tgs f == t))
= ()

let assert_field_matches_tag
  (#l: P.union_typ) (tgs: tags l)
  (f: P.struct_field l) (t: UInt32.t)
: Lemma
  (requires (normalize_term (tag_of_field tgs f) == t))
  (ensures (field_matches_tag tgs f t))
= ()

(******************************************************************************)

(* Stateful invariant *)

let valid
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: GTot Type0
=
  let tag_ptr = P.gfield p (tag_field l) in
  let u_ptr = P.gfield p (union_field l) in
  let t = P.gread h tag_ptr in
  P.readable h tag_ptr /\
  List.Tot.mem t tgs /\
  (let f = field_of_tag #l tgs t in
   P.is_active_union_field h u_ptr f)

let valid_live
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: Lemma (requires (valid h tgs p))
        (ensures (P.live h p))
  [SMTPat (valid h tgs p)]
= ()

(******************************************************************************)

(* Operations *)

let gread_tag
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: GTot UInt32.t
= P.gread h (P.gfield p (tag_field l))

let read_tag
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
: HST.Stack UInt32.t
  (requires (fun h -> valid h tgs p))
  (ensures (fun h0 t h1 ->
    h0 == h1 /\
    List.Tot.mem t tgs /\
    t == gread_tag h0 tgs p))
= P.read (P.field p (tag_field l))


let gfield
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
: GTot (p': P.pointer (P.typ_of_struct_field l f) { P.includes p p' })
= P.gufield (P.gfield p (union_field l)) f


let field
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
= P.ufield (P.field p (union_field l)) f

// We could also require the user to manually provide the integer tagged. I
// claim it should not be needed since we need to normalise/inline write before
// extraction anyway

let write
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
    gread_tag h1 tgs p == normalize_term (tag_of_field tgs f) /\
    field_matches_tag tgs f (gread_tag h1 tgs p) /\
    P.gread h1 (gfield tgs p f) == v
  ))
=
  let tag_ptr = P.field p (tag_field l) in
  let u_ptr = P.field p (union_field l) in
  let t = tag_of_field #l tgs f in
  P.write tag_ptr t;
  let h11 = HST.get () in
  P.write (P.ufield u_ptr f) v;
  let h1 = HST.get () in
  // SMTPats for this lemma do not seem to trigger?
//  P.no_upd_lemma_1 h11 h1 u_ptr tag_ptr;
  assert (P.readable h1 tag_ptr);
  assert (P.readable h1 u_ptr);
  P.readable_struct_fields_readable_struct h1 p;
  let uf = P.ufield u_ptr f in
  P.is_active_union_field_includes_readable #l h1 u_ptr f uf;
  assert (P.is_active_union_field #l h1 u_ptr f)

let write_tag
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
    /\ gread_tag h1 tgs p == normalize_term (tag_of_field tgs f)
    /\ field_matches_tag tgs f (gread_tag h1 tgs p)
  ))
=
  let tag_ptr = P.field p (tag_field l) in
  let u_ptr : P.pointer (P.TUnion l) = P.field p (union_field l) in
  let t = tag_of_field #l tgs f in
  P.write tag_ptr t;
  P.write_union_field u_ptr f

(******************************************************************************)

(* Lemmas *)

let includes_gfield
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
: Lemma
  (requires True)
  (ensures (P.includes p (gfield tgs p f)))
  [SMTPat (P.includes p (gfield tgs p f))]
= ()

let live_gfield #l tgs p f h = ()

let modifies_1_valid
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
  [SMTPat (valid #l h0 tgs p); SMTPat (P.modifies_1 (gfield #l tgs p f) h0 h1);
   SMTPat (P.includes #_ #t' (gfield #l tgs p f) p')]
=
  let u_ptr = P.gfield p (union_field l) in
  P.is_active_union_field_includes_readable h1 u_ptr f p'

let modifies_1_field_tag
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
  [SMTPat (valid #l h0 tgs p); SMTPat (P.modifies_1 (gfield #l tgs p f) h0 h1)]
= ()

let modifies_1_field
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h0 h1: HS.mem)
: Lemma
  (requires (valid h0 tgs p /\ P.modifies_1 (gfield tgs p f) h0 h1))
  (ensures (P.modifies_1 p h0 h1))
  [SMTPat (valid #l h0 tgs p); SMTPat (P.modifies_1 (gfield #l tgs p f) h0 h1)]
= ()

let modifies_1_field_tag_equal
  (#l: P.union_typ)
  (tgs: tags l)
  (p: P.pointer (typ l))
  (f: P.struct_field l)
  (h0 h1: HS.mem)
: Lemma
  (requires (valid h0 tgs p /\ P.modifies_1 (gfield tgs p f) h0 h1))
  (ensures (gread_tag h0 tgs p == gread_tag h1 tgs p))
  [SMTPat (valid h0 tgs p); SMTPat (gread_tag h1 tgs p); SMTPat (gfield tgs p f)]
= ()

let readable_intro
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
= P.readable_struct_fields_readable_struct h p

let readable_field
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
  [SMTPat (P.readable h (gfield tgs p f))]
= ()

(******************************************************************************)

(* Logical representation of a tagged union.
*)

let raw_get_tag (#l: P.union_typ) (tu: raw l)
: Tot UInt32.t
=
  P.struct_sel #(typ_l l) tu (tag_field l)

let raw_get_field (#l: P.union_typ) (tu: raw l)
: GTot (P.struct_field l)
=
  P.union_get_key #l (P.struct_sel #(typ_l l) tu (union_field l))

let raw_get_value (#l: P.union_typ) (tu: raw l) (f: P.struct_field l)
: Pure (P.type_of_typ (P.typ_of_struct_field l f))
  (requires (raw_get_field tu == f))
  (ensures (fun _ -> True))
=
  let u : P.union l = P.struct_sel #(typ_l l) tu (union_field l) in
  P.union_get_value u f

(* Lemma: "valid p ==> matching_tags (gread p)" *)

let valid_matching_tags
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: Lemma
  (requires (valid h tgs p))
  (ensures (matching_tags (P.gread h p) tgs))
  [SMTPatOr [[SMTPat (valid h tgs p)]; [SMTPat (matching_tags (P.gread h p) tgs)]]]
= ()


// Not sure if useful
(*
let read
  (#l: P.union_typ)
  (h: HS.mem)
  (tgs: tags l)
  (p: P.pointer (typ l))
: HST.Stack (t l tgs)
  (requires (fun h ->
    P.live h p /\ P.readable h p /\
    valid h tgs p))
  (ensures (fun h0 tu h1 ->
    h0 == h1 /\
    (let raw_tu : raw l = tu in
     raw_tu == P.gread h0 p)
  ))
= P.read p
*)
