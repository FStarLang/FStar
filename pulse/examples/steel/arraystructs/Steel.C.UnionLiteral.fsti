module Steel.C.UnionLiteral

open Steel.Memory
open Steel.Effect
open Steel.Effect.Common
open Steel.Effect.Atomic

open Steel.C.PCM
open Steel.C.Union
open Steel.C.Typedef
open Steel.C.Ref
open Steel.C.Connection
open Steel.C.Opt
open Steel.C.Fields

open FStar.List.Tot
open FStar.FunctionalExtensionality
open FStar.FSet

module TS = Typestring

val mk_union_def (tag: Type0) (field_descriptions: Type0): Type0

let mk_c_union (tag: Type0) (fields: c_fields) =
  mk_union_def tag (c_fields_t fields)

let union_views (fields: c_fields) (field: field_of fields): Type0 =
  (fields.get_field field).view_type

val union (tag: Type0) (fields: c_fields): Type0

val mk_union (tag: Type0) (fields: c_fields)
  (field: field_of fields) (x: (fields.get_field field).view_type)
: Pure (union tag fields)
    (requires fields.has_field field == true)
    (ensures fun _ -> True)

val union_pcm_carrier (tag: Type0) (fields: c_fields): Type0

val union_pcm (tag: Type0) (fields: c_fields): pcm (union_pcm_carrier tag fields)

let nonempty_c_fields = fields:c_fields{Some? fields.nonempty_witness}

val union_view (tag: Type0) (fields: nonempty_c_fields)
: sel_view (union_pcm tag fields) (union tag fields) false

val dtuple2_of_union (#tag: Type0) (#fields: c_fields) (x: union tag fields)
: dtuple2 (field_of fields) (union_views fields)

val union_of_dtuple2 (#tag: Type0) (#fields: c_fields) 
  (x: dtuple2 (field_of fields) (union_views fields))
: union tag fields

val dtuple2_of_union_of_dtuple2 
  (#tag: Type0) (#fields: c_fields)
  (x: dtuple2 (field_of fields) (union_views fields))
: Lemma (dtuple2_of_union (union_of_dtuple2 #tag #fields x) == x)

val union_of_dtuple2_of_union
  (#tag: Type0) (#fields: c_fields)
  (x: union tag fields)
: Lemma (union_of_dtuple2 (dtuple2_of_union #tag #fields x) == x)

val union_field
  (tag: Type0) (fields: c_fields) (field: field_of fields)
: connection (union_pcm tag fields) (fields.get_field field).pcm

val union_is_unit (tag:Type0) (fields:c_fields) (v:union_pcm_carrier tag fields)
: b:bool{b <==> v == one (union_pcm tag fields)}

[@@c_typedef]
let typedef_union (tag: Type0) (fields: nonempty_c_fields): typedef = {
  carrier = union_pcm_carrier tag fields;
  pcm = union_pcm tag fields;
  view_type = union tag fields;
  view = union_view tag fields;
  is_unit = union_is_unit tag fields;
}

open Steel.C.Reference

val addr_of_union_field
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
: Steel (ref 'a
          (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
          (fields.get_field field).pcm)
    (p `pts_to_view` union_view tag fields)
    (fun q ->
      pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view)))
    (requires fun h ->
       dfst (dtuple2_of_union (h (p `pts_to_view` union_view tag fields))) == field)
    (ensures fun h q h' -> 
      q == ref_focus p (union_field tag fields field) /\
      dfst (dtuple2_of_union (h (p `pts_to_view` union_view tag fields))) == field /\
      dsnd (dtuple2_of_union (h (p `pts_to_view` union_view tag fields)))
        ==
        h' (q `pts_to_view` (fields.get_field field).view))

val unaddr_of_union_field
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
  (q: ref 'a (fields.get_field field).view_type (fields.get_field field).pcm)
: Steel unit
    (pts_to_view u#0
                 #'a
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                 q
                 (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view)))
    (fun q -> p `pts_to_view` union_view tag fields)
    (requires fun _ -> q == ref_focus p (union_field tag fields field))
    (ensures fun h _ h' -> 
      dfst (dtuple2_of_union (h' (p `pts_to_view` union_view tag fields))) == field /\
      dsnd (dtuple2_of_union (h' (p `pts_to_view` union_view tag fields)))
        ==
        h (q `pts_to_view` (fields.get_field field).view))

val switch_union_field
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields) (v: (fields.get_field field).view_type)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
: Steel unit
    (p `pts_to_view` union_view tag fields)
    (fun _ -> p `pts_to_view` union_view tag fields)
    (requires fun h ->
      let (|field, v|) = dtuple2_of_union (h (p `pts_to_view` union_view tag fields)) in
      exclusive (fields.get_field field).pcm ((fields.get_field field).view.to_carrier v))
    (ensures fun _ _ h' ->
      dtuple2_of_union (h' (p `pts_to_view` union_view tag fields)) == (|field, v|))

[@@c_typedef]
let typedef_union (tag: Type0) (fields: c_fields): typedef = {
  carrier = union_pcm_carrier tag fields;
  pcm = union_pcm tag fields;
  view_type = union tag fields;
  view = union_view tag fields;
}
