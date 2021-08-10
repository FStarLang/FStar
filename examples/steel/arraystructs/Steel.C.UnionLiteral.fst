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

let mk_union_def (tag: Type0) (field_descriptions: Type0): Type0 = unit

let union (tag: Type0) (fields: c_fields): Type0 =
  dtuple2 (field_of fields) (union_views fields)

let mk_union (tag: Type0) (fields: c_fields)
  (field: field_of fields) (x: (fields.get_field field).view_type)
: Pure (union tag fields)
    (requires fields.has_field field == true)
    (ensures fun _ -> True)
= (|field, x|)

let union_carriers (fields: c_fields) (field: field_of fields): Type0 =
  (fields.get_field field).carrier

let union_pcms (fields: c_fields) (field: field_of fields): pcm (union_carriers fields field) =
  (fields.get_field field).pcm

let union_pcm_carrier (tag: Type0) (fields: c_fields): Type0 =
  Steel.C.Union.union (union_pcms fields)

let union_pcm (tag: Type0) (fields: c_fields): pcm (union_pcm_carrier tag fields) =
  union_pcm (union_pcms fields)

let is_units (fields: c_fields) (field: field_of fields)
: x:(fields.get_field field).carrier ->
  b:bool{b <==> x == one (fields.get_field field).pcm}
= (fields.get_field field).is_unit

let rec case_of_union_aux (fields: c_fields)
  (fields_list: list string)
  (u: Steel.C.Union.union (union_pcms fields))
: Pure (option (field_of fields))
    (requires forall (field:string). field `mem` fields_list ==> fields.has_field field == true)
    (ensures fun field ->
      (None? field ==> (forall (field:field_t). field `mem` fields_list ==> u field == one (union_pcms fields field))) /\
      (Some? field ==> u (Some?.v field) =!= one (union_pcms fields (Some?.v field))))
    (decreases fields_list)
= match fields_list with
  | [] -> None
  | field :: fields_list ->
    match case_of_union_aux fields fields_list u with
    | Some field -> Some field
    | None ->
      if field = "" then None else
      if (fields.get_field field).is_unit (u field) then None else Some field

let case_of_union (fields: nonempty_c_fields)
  (u: Steel.C.Union.union (union_pcms fields))
: field:field_of fields{case_refinement_f (union_pcms fields) field u}
= match case_of_union_aux fields fields.cfields u with
  | None -> Some?.v fields.nonempty_witness
  | Some field -> field

let union_views' (fields: c_fields) (field: field_of fields)
: sel_view (union_pcms fields field) (union_views fields field) false
= (fields.get_field field).view

let union_view (tag: Type0) (fields: nonempty_c_fields)
: sel_view (union_pcm tag fields) (union tag fields) false
= Steel.C.Union.union_view (union_views' fields) (case_of_union fields)

let dtuple2_of_union (#tag: Type0) (#fields: c_fields) (x: union tag fields)
: dtuple2 (field_of fields) (union_views fields)
= x

let union_of_dtuple2 (#tag: Type0) (#fields: c_fields) 
  (x: dtuple2 (field_of fields) (union_views fields))
: union tag fields
= x

let dtuple2_of_union_of_dtuple2 
  (#tag: Type0) (#fields: c_fields)
  (x: dtuple2 (field_of fields) (union_views fields))
: Lemma (dtuple2_of_union (union_of_dtuple2 #tag #fields x) == x)
= ()

let union_of_dtuple2_of_union
  (#tag: Type0) (#fields: c_fields)
  (x: union tag fields)
: Lemma (union_of_dtuple2 (dtuple2_of_union #tag #fields x) == x)
= ()

let union_field
  (tag: Type0) (fields: c_fields) (field: field_of fields)
: connection (union_pcm tag fields) (fields.get_field field).pcm
= union_field (union_pcms fields) field

let rec union_is_unit_aux (tag: Type0) (fields: c_fields)
  (fields_list: list string)
  (v: union_pcm_carrier tag fields)
: Pure bool
    (requires forall field. field `mem` fields_list ==> fields.has_field field == true)
    (ensures fun b -> b <==> (forall (field: field_t). field `mem` fields_list ==> v field == one (union_pcm tag fields) field))
    (decreases fields_list)
= match fields_list with
  | [] -> true
  | field :: fields_list ->
    if field = "" then union_is_unit_aux tag fields fields_list v else
    (fields.get_field field).is_unit (v field) &&
    union_is_unit_aux tag fields fields_list v

let union_is_unit tag fields v
: b:bool{b <==> v == one (union_pcm tag fields)}
= let b = union_is_unit_aux tag fields fields.cfields v in
  assert (b <==> v `feq` one (union_pcm tag fields));
  b

open Steel.C.Reference

assume val addr_of_union_field
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
       dfst (dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))) == field)
    (ensures fun h q h' -> 
      q == ref_focus p (union_field tag fields field) /\
      dfst (dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))) == field /\
      dsnd (dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields)))
        ==
        h' (q `pts_to_view` (fields.get_field field).view))

assume val unaddr_of_union_field
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
      dfst (dtuple2_of_union #tag #fields (h' (p `pts_to_view` union_view tag fields))) == field /\
      dsnd (dtuple2_of_union #tag #fields (h' (p `pts_to_view` union_view tag fields)))
        ==
        h (q `pts_to_view` (fields.get_field field).view))

assume val switch_union_field
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields) (v: (fields.get_field field).view_type)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
: Steel unit
    (p `pts_to_view` union_view tag fields)
    (fun _ -> p `pts_to_view` union_view tag fields)
    (requires fun h ->
      let (|field, v|) = dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields)) in
      exclusive (fields.get_field field).pcm ((fields.get_field field).view.to_carrier v))
    (ensures fun _ _ h' ->
      dtuple2_of_union #tag #fields (h' (p `pts_to_view` union_view tag fields)) == (|field, v|))
