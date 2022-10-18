module Steel.C.UnionLiteral

open Steel.Memory
open Steel.Effect
open Steel.Effect.Common
open Steel.Effect.Atomic

open Steel.C.Model.PCM
open Steel.C.Model.Union
open Steel.C.Typedef
open Steel.C.Model.Ref
open Steel.C.Model.Connection
open Steel.C.Opt
open Steel.C.Fields

open FStar.List.Tot
open FStar.FunctionalExtensionality
open FStar.FSet

module TS = Steel.C.Typestring

val mk_union_def (tag: Type0) (field_descriptions: Type0): Type0

(** To declare a struct definition, one needs to write
      let _ = norm norm_c_typedef (mk_c_struct <struct_tag> <struct_fields>).
    See Steel.C.StructLiteral.mk_c_struct for more details. *)
let mk_c_union (tag: Type0) (fields: c_fields) =
  mk_union_def tag (c_fields_t fields)

let union_views (fields: c_fields) (field: field_of fields): Type0 =
  (fields.get_field field).view_type

(** A [union tag fields] is a view type for C union with tag [tag] and fields [fields]. *)
val union (tag: Type0) (fields: c_fields): Type0

(** [mk_union tag fields field x] represents the union literal (union tag) {.field = x} *)
val mk_union (tag: Type0) (fields: c_fields)
  (field: field_of fields) (x: (fields.get_field field).view_type)
: Pure (union tag fields)
    (requires fields.has_field field == true)
    (ensures fun _ -> True)

(** The carrier of the PCM representing unions with tag [tag] and fields [fields]. *)
val union_pcm_carrier (tag: Type0) (fields: c_fields): Type0

(** The PCM representing unions with tag [tag] and fields [fields]. *)
val union_pcm (tag: Type0) (fields: c_fields): pcm (union_pcm_carrier tag fields)

let nonempty_c_fields = fields:c_fields{Some? fields.nonempty_witness}

val union_view (tag: Type0) (fields: nonempty_c_fields)
: sel_view (union_pcm tag fields) (union tag fields) false

(** For now we expose an isomorphism between values of type [union tag fields] and dependent tuples.
    This allows a particularly dedicated Steel programmer to bypass the nominality of C unions, because
    it reveals the fact that the tag name is completely unused. In the future we should essentially expose
    (dfst . dtuple2_of_union) and (dsnd . dtuple2_of_union) and the right laws, but not the whole isomorphism. *)

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

(** A connection from a union to any of its fields *)
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

val addr_of_union_field''
  (return_view_type: Type0)
  (return_carrier: Type0)
  (tag: Type0) (fields: c_fields)
  (field: field_of fields{
    return_view_type == (fields.get_field field).view_type /\
    return_carrier == (fields.get_field field).carrier})
  (p: ref (union tag fields) (union_pcm tag fields))
: Steel (ref return_view_type #return_carrier (fields.get_field field).pcm)
    (p `pts_to_view` union_view tag fields)
    (fun q ->
      pts_to_view u#0
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view)))
    (requires fun h ->
       dfst (dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))) == field)
    (ensures fun h q h' -> 
      q == ref_focus p (union_field tag fields field) /\
      dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))
        == (|field, h' (q `pts_to_view` (fields.get_field field).view)|))

(** Take the address of a field of a union.
    The definitions and normalization strategies are identical to
    those described in Steel.C.StructLiteral.addr_of_struct_field. *)
inline_for_extraction noextract
let addr_of_union_field
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields)
  (p: ref (union tag fields) (union_pcm tag fields))
: Steel (ref
          (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
          #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
          (fields.get_field field).pcm)
    (p `pts_to_view` union_view tag fields)
    (fun q ->
      pts_to_view u#0
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view)))
    (requires fun h ->
       dfst (dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))) == field)
    (ensures fun h q h' -> 
      q == ref_focus p (union_field tag fields field) /\
      dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))
        == (|field, h' (q `pts_to_view` (fields.get_field field).view)|))
= addr_of_union_field''
    (normalize (fields.get_field field).view_type)
    (normalize (fields.get_field field).carrier)
    tag fields field p

(** Inverse of addr_of_union_field. *)
val unaddr_of_union_field
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields)
  (p: ref (union tag fields) (union_pcm tag fields))
  (q: ref (fields.get_field field).view_type (fields.get_field field).pcm)
: Steel unit
    (pts_to_view u#0
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                 #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                 q
                 (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view)))
    (fun q -> p `pts_to_view` union_view tag fields)
    (requires fun _ -> q == ref_focus p (union_field tag fields field))
    (ensures fun h _ h' -> 
      dtuple2_of_union #tag #fields (h' (p `pts_to_view` union_view tag fields))
        == (|field, h (q `pts_to_view` (fields.get_field field).view)|))

val switch_union_field'
  (new_value_ty: Type0) (tag: Type0) (fields: c_fields)
  (field: field_of fields{new_value_ty == (fields.get_field field).view_type})
  (new_value: new_value_ty)
  (p: ref (union tag fields) (union_pcm tag fields))
: Steel unit
    (p `pts_to_view` union_view tag fields)
    (fun _ -> p `pts_to_view` union_view tag fields)
    (requires fun h ->
      let (|old_field, v|) =
        dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))
      in
      exclusive (fields.get_field old_field).pcm ((fields.get_field old_field).view.to_carrier v) /\
      p_refine (fields.get_field field).pcm ((fields.get_field field).view.to_carrier new_value)
    )
    (ensures fun _ _ h' ->
      dtuple2_of_union #tag #fields (h' (p `pts_to_view` union_view tag fields))
        == (|field, new_value|))

(** Switch the case of a union to field [field] by writing [new_value] to it. *)
noextract inline_for_extraction
let switch_union_field
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields) (new_value: (fields.get_field field).view_type)
  (p: ref (union tag fields) (union_pcm tag fields))
  // TODO it would be nice permute the arguments so that their order matches the C code p->field = new_value
: Steel unit
    (p `pts_to_view` union_view tag fields)
    (fun _ -> p `pts_to_view` union_view tag fields)
    (requires fun h ->
      let (|old_field, v|) =
        dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))
      in
      exclusive (fields.get_field old_field).pcm ((fields.get_field old_field).view.to_carrier v) /\
      p_refine (fields.get_field field).pcm ((fields.get_field field).view.to_carrier new_value)
    )
    (ensures fun _ _ h' ->
      dtuple2_of_union #tag #fields (h' (p `pts_to_view` union_view tag fields))
        == (|field, new_value|))
= switch_union_field' (normalize (fields.get_field field).view_type) tag fields field new_value p
