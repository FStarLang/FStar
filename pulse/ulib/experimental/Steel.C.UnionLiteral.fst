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

module TS = Steel.C.Typestring

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

#push-options "--z3rlimit 64"
#restart-solver
let addr_of_union_field'
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
: Steel (ref 'a
          (fields.get_field field).view_type
          (fields.get_field field).pcm)
    (p `pts_to_view` union_view tag fields)
    (fun q ->
      pts_to_view u#0
                  #'a
                  #(fields.get_field field).view_type
                  #(fields.get_field field).view_type
                  #(fields.get_field field).carrier
                  #(fields.get_field field).pcm
                  q
                  (fields.get_field field).view)
    (requires fun h ->
       dfst (dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))) == field)
    (ensures fun h q h' -> 
      q == ref_focus p (union_field tag fields field) /\
      dtuple2_of_union #tag #fields (h (p `pts_to_view` union_view tag fields))
        == (|field, h' (q `pts_to_view` (fields.get_field field).view)|))
= let v: Ghost.erased (union tag fields) =
    gget (p `pts_to_view` union_view tag fields)
  in
  let s: Ghost.erased (union_pcm_carrier tag fields) =
    pts_to_view_elim p (union_view tag fields)
  in
//  assert (Ghost.reveal s == (union_view tag fields).to_carrier v);
  let q = Steel.C.Union.addr_of_union_field #'a #_ #_ #(union_pcms fields) p field s in
  change_equal_slprop (q `pts_to` _) (q `pts_to` _);
  pts_to_view_intro q (Ghost.reveal s field)
    (fields.get_field field).view
    (dsnd (Ghost.reveal v));
  assert (Ghost.reveal v == (|field, dsnd (Ghost.reveal v)|));
  return q
#pop-options

let addr_of_union_field'' #a return_view_type return_carrier tag fields field p =
  addr_of_union_field' #a #tag #fields field p

let unaddr_of_union_field'
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
  (q: ref 'a (fields.get_field field).view_type (fields.get_field field).pcm)
: Steel unit
    (pts_to_view u#0
                 #'a
                 #(fields.get_field field).view_type
                 #(fields.get_field field).view_type
                 #(fields.get_field field).carrier
                 #(fields.get_field field).pcm
                 q
                 (fields.get_field field).view)
    (fun q -> p `pts_to_view` union_view tag fields)
    (requires fun _ -> q == ref_focus p (union_field tag fields field))
    (ensures fun h _ h' -> 
      dtuple2_of_union #tag #fields (h' (p `pts_to_view` union_view tag fields))
        == (|field, h (q `pts_to_view` (fields.get_field field).view)|))
= let v: Ghost.erased (fields.get_field field).view_type =
    gget (q `pts_to_view` (fields.get_field field).view)
  in
  let s: Ghost.erased (fields.get_field field).carrier =
    pts_to_view_elim q (fields.get_field field).view
  in
  Steel.C.Union.unaddr_of_union_field #_ #_ #_ #_ #(union_pcms fields) field q p s;
  pts_to_view_intro p
    (field_to_union_f (union_pcms fields) field s)
    (union_view tag fields)
    (|field, Ghost.reveal v|);
  return ()

let unaddr_of_union_field #a #tag #fields field p q =
  unaddr_of_union_field' #a #tag #fields field p q

#restart-solver
#push-options "--z3rlimit 64"
let exclusive_refine_union_field
  (tag: Type0) (fields: c_fields)
  (old_field new_field: field_of fields)
  (old_value: (fields.get_field old_field).view_type)
  (new_value: (fields.get_field new_field).view_type)
: Lemma
 (requires
   exclusive (fields.get_field old_field).pcm ((fields.get_field old_field).view.to_carrier old_value) /\
   p_refine (fields.get_field new_field).pcm ((fields.get_field new_field).view.to_carrier new_value))
 (ensures
   exclusive (union_pcm tag fields) ((union_view tag fields).to_carrier (|old_field, old_value|)) /\
   p_refine (union_pcm tag fields) ((union_view tag fields).to_carrier (|new_field, new_value|)))
= assert (
    one (fields.get_field old_field).pcm =!=
    (fields.get_field old_field).view.to_carrier old_value);
  let aux frame
  : Lemma
    (requires 
     Steel.C.PCM.composable
      (union_pcm tag fields)
      ((union_view tag fields).to_carrier (|old_field, old_value|))
      frame)
    (ensures frame == one (union_pcm tag fields))
  = assert (frame old_field == one (fields.get_field old_field).pcm);
    assert (frame `feq` one (union_pcm tag fields))
  in
  FStar.Classical.(forall_intro (move_requires aux))
#pop-options

let switch_union_field''
  (#tag: Type0) (#fields: c_fields)
  (field: field_of fields) (new_value: (fields.get_field field).view_type)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
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
= let v: Ghost.erased (union tag fields) =
    gget (p `pts_to_view` union_view tag fields)
  in
  let s: Ghost.erased (union_pcm_carrier tag fields) =
    pts_to_view_elim p (union_view tag fields)
  in
  let s': Ghost.erased (union_pcm_carrier tag fields) =
   Ghost.hide ((union_view tag fields).to_carrier (Ghost.reveal v))
  in
  assert (Ghost.reveal s == Ghost.reveal s');
  let old_field: Ghost.erased (field_of fields) =
    Ghost.hide (dfst (Ghost.reveal v))
  in
  let old_value: Ghost.erased (fields.get_field old_field).view_type =
    Ghost.hide (dsnd (Ghost.reveal v))
  in
  let new_s: union_pcm_carrier tag fields =
     (union_view tag fields).to_carrier (|field, new_value|)
  in
  exclusive_refine_union_field tag fields old_field field old_value new_value;
  assert (exclusive (union_pcm tag fields) s);
  assert (p_refine (union_pcm tag fields) new_s);
  let upd: frame_preserving_upd (union_pcm tag fields) s new_s =
    base_fpu (union_pcm tag fields) s new_s
  in
  Steel.C.Ref.ref_upd p s new_s upd;
  pts_to_view_intro p new_s
    (union_view tag fields)
    (|field, new_value|);
  return ()

let switch_union_field'
  (new_value_ty: Type0) (tag: Type0) (fields: c_fields)
  (field: field_of fields{new_value_ty == (fields.get_field field).view_type})
  (new_value: new_value_ty)
  (p: ref 'a (union tag fields) (union_pcm tag fields))
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
= switch_union_field'' #'a #tag #fields field new_value p
