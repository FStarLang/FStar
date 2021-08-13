module Steel.C.StructLiteral

open Steel.Memory
open Steel.Effect
open Steel.Effect.Common
open Steel.Effect.Atomic

open Steel.C.PCM
open Steel.C.Struct
open Steel.C.Typedef
open Steel.C.Ref
open Steel.C.Connection
open Steel.C.Opt
open Steel.C.Fields

open FStar.List.Tot
open FStar.FunctionalExtensionality

let mk_struct_def (tag: Type0) (field_descriptions: Type0): Type0 = unit

let field_of' (fields: c_fields) = field:string{fields.has_field field == true}

let struct_dom (fields: c_fields) (excluded: excluded_fields) =
  refine (field_of' fields) (notin excluded)

let struct_cod (fields: c_fields) (excluded: excluded_fields) (field: struct_dom fields excluded) =
  (fields.get_field field).view_type

let struct' tag fields excluded =
  restricted_t (struct_dom fields excluded) (struct_cod fields excluded)

let mk_nil tag = on_dom _ (fun _ -> ())

let mk_cons tag fields field td x v =
  on_dom (struct_dom (fields_cons field td fields) emptyset) (fun field' ->
    if field = field' then x
    else v field' <: ((fields_cons field td fields).get_field field').view_type)

let struct_pcm_carrier_cod (fields: c_fields) (field: field_of' fields) =
  (fields.get_field field).carrier

let struct_pcms (fields: c_fields) (field: field_of' fields)
: pcm (struct_pcm_carrier_cod fields field)
= (fields.get_field field).pcm

let struct_pcm_carrier tag fields =
  restricted_t (field_of' fields) (struct_pcm_carrier_cod fields)

let struct_pcm tag fields = prod_pcm (struct_pcms fields)

let struct_get x field = x field
let struct_put x field v = on_dom _ (fun field' -> if field = field' then v else x field')
      
let struct_get_put x field v = ()

let struct_put_get x field =
  assert (struct_put x field (x `struct_get` field) `feq` x)

let struct_put_put x field v w =
  assert (struct_put (struct_put x field v) field w `feq` struct_put x field w)

let struct_get_put_ne x field1 field2 v = ()

let struct_put_put_ne x field1 v field2 w = 
  assert (
    struct_put (struct_put x field1 v) field2 w `feq`
    struct_put (struct_put x field2 w) field1 v)

let struct_pcm_get x field = x field
let struct_pcm_put x field v = on_dom _ (fun field' -> if field = field' then v else x field')

let struct_pcm_get_put x field v = ()

let struct_pcm_put_get x field =
  assert (struct_pcm_put x field (x `struct_pcm_get` field) `feq` x)

let struct_pcm_put_put x field v w =
  assert (struct_pcm_put (struct_pcm_put x field v) field w `feq` struct_pcm_put x field w)

let struct_pcm_get_put_ne x field1 field2 v = ()

let struct_pcm_put_put_ne x field1 v field2 w =
   assert (
     struct_pcm_put (struct_pcm_put x field1 v) field2 w `feq`
     struct_pcm_put (struct_pcm_put x field2 w) field1 v)

let struct_view_to_view_prop (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
: struct_pcm_carrier tag fields -> prop
= fun x -> forall (field: struct_dom fields excluded).
  (fields.get_field field).view.to_view_prop (x field) /\
  (fields.has_field field == false ==> x field =!= one (fields.get_field field).pcm)

let struct_view_to_view (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
: refine (struct_pcm_carrier tag fields) (struct_view_to_view_prop tag fields excluded) -> 
  struct' tag fields excluded
= fun x -> on_dom (struct_dom fields excluded) (fun field -> (fields.get_field field).view.to_view (x field))

let struct_view_to_carrier (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
: struct' tag fields excluded ->
  refine (struct_pcm_carrier tag fields) (struct_view_to_view_prop tag fields excluded)
= fun x ->
  let y: struct_pcm_carrier tag fields =
    on_dom (field_of' fields) (fun field ->
      if excluded field then one (fields.get_field field).pcm else
      if field = "" then Some () else
      (fields.get_field field).view.to_carrier (x field)
      <: (fields.get_field field).carrier)
  in y

module S = FStar.String

(*
let rec max_len (excluded: list string)
: Ghost nat True (fun n -> forall s'. memP s' excluded ==> n >= S.strlen s')
= match excluded with
  | [] -> 0
  | field :: excluded -> 
    let ih = max_len excluded in
    if S.strlen field > ih then S.strlen field else ih
    
let arbitrary_unexcluded_witness (excluded: list string)
: Ghost string True (fun s -> forall s'. memP s' excluded ==> S.strlen s > S.strlen s')
= S.make (max_len excluded + 1) ' '

let arbitrary_unexcluded (excluded: excluded_fields): GTot (struct_dom fields excluded) =
  arbitrary_unexcluded_witness (set_as_list excluded)
  *)

let struct_view_to_carrier_not_one (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
: Lemma 
    (~ (exists x. struct_view_to_carrier tag fields excluded x == one (struct_pcm tag fields)) /\
     ~ (struct_view_to_view_prop tag fields excluded (one (struct_pcm tag fields))))
= (fields.get_field "").view.to_carrier_not_one

let struct_view_to_view_frame (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
: (x: struct' tag fields excluded) ->
  (frame: struct_pcm_carrier tag fields) ->
  Lemma
    (requires (composable (struct_pcm tag fields) (struct_view_to_carrier tag fields excluded x) frame))
    (ensures
      struct_view_to_view_prop tag fields excluded
        (op (struct_pcm tag fields) (struct_view_to_carrier tag fields excluded x) frame) /\
      struct_view_to_view tag fields excluded
        (op (struct_pcm tag fields) (struct_view_to_carrier tag fields excluded x) frame) == x)
= fun x frame ->
  let p = struct_pcms fields in
  Classical.forall_intro_2 (fun k -> is_unit (p k));
  let aux (k:struct_dom fields excluded)
  : Lemma (
      (fields.get_field k).view.to_view_prop
        (op (p k) (struct_view_to_carrier tag fields excluded x k) (frame k)) /\
      (fields.get_field k).view.to_view
        (op (p k) (struct_view_to_carrier tag fields excluded x k) (frame k)) == x k)
  = assert (composable (p k) ((fields.get_field k).view.to_carrier (x k)) (frame k));
    (fields.get_field k).view.to_view_frame (x k) (frame k)
  in FStar.Classical.forall_intro aux;
  assert (
    struct_view_to_view tag fields excluded
       (op (prod_pcm p) (struct_view_to_carrier tag fields excluded x) frame) `feq` x)

let struct_view tag fields excluded = {
  to_view_prop = struct_view_to_view_prop tag fields excluded;
  to_view = struct_view_to_view tag fields excluded;
  to_carrier = struct_view_to_carrier tag fields excluded;
  to_carrier_not_one = Classical.move_requires (struct_view_to_carrier_not_one tag fields) excluded;
  to_view_frame = struct_view_to_view_frame tag fields excluded;
}

let rec struct_is_unit_aux (tag: Type0) (fields: c_fields)
  (fields_list: list string)
  (v: struct_pcm_carrier tag fields)
: Pure bool
    (requires forall field. field `mem` fields_list ==> fields.has_field field == true)
    (ensures fun b -> b <==> (forall (field: string). field `mem` fields_list ==> v field == one (struct_pcm tag fields) field))
    (decreases fields_list)
= match fields_list with
  | [] -> true
  | field :: fields_list ->
    (fields.get_field field).is_unit (v field) &&
    struct_is_unit_aux tag fields fields_list v

let struct_is_unit tag fields v
: b:bool{b <==> v == one (struct_pcm tag fields)}
= let b = struct_is_unit_aux tag fields fields.cfields v in
  assert (b <==> v `feq` one (struct_pcm tag fields));
  b

let struct_field tag fields field = struct_field (struct_pcms fields) field

let struct'_without_field
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields) (field: field_t)
  (v: struct' tag fields excluded)
: struct' tag fields (insert field excluded)
= on_dom (struct_dom fields (insert field excluded)) v

let struct_without_field_to_carrier
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields) (field: field_of fields)
  (s: struct_pcm_carrier tag fields)
  (v: struct' tag fields excluded)
: Lemma
    (requires s == (struct_view tag fields excluded).to_carrier v)
    (ensures
      struct_without_field (struct_pcms fields) field s
      == (struct_view tag fields (insert field excluded)).to_carrier
           (struct'_without_field tag fields excluded field v))
= assert (
    struct_without_field (struct_pcms fields) field s
    `feq` (struct_view tag fields (insert field excluded)).to_carrier
         (struct'_without_field tag fields excluded field v))

let extract_field
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (v: struct' tag fields excluded)
: Pure (struct' tag fields (insert field excluded) & (fields.get_field field).view_type)
    (requires not (excluded field))
    (ensures fun _ -> True)
= (struct'_without_field tag fields excluded field v, v field)

let extract_field_extracted
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (v: struct' tag fields excluded)
= ()

let extract_field_unextracted
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (field': field_of fields)
  (v: struct' tag fields excluded)
= ()

val addr_of_struct_field_ref'
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
: Steel (ref 'a (fields.get_field field).pcm)
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (q `pts_to_view` (fields.get_field field).view))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == ref_focus p (struct_field tag fields field) /\
      fst (extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded)))
       ==
        h' (p `pts_to_view` struct_view tag fields (insert field excluded)) /\
      snd
        (extract_field tag fields excluded field
          (h (p `pts_to_view` struct_view tag fields excluded)))
       ==
        h' (q `pts_to_view` (fields.get_field field).view))

#push-options "--z3rlimit 30"
let addr_of_struct_field_ref' #a #tag #fields #excluded field p =
  let v: Ghost.erased (struct' tag fields excluded) =
    gget (p `pts_to_view` struct_view tag fields excluded)
  in
  let s: Ghost.erased (struct_pcm_carrier tag fields) =
    pts_to_view_elim p (struct_view tag fields excluded)
  in
  let q = addr_of_struct_field p field s in
  struct_without_field_to_carrier tag fields excluded field s v;
  pts_to_view_intro p (struct_without_field (struct_pcms fields) field s)
    (struct_view tag fields (insert field excluded))
    (struct'_without_field tag fields excluded field v);
  pts_to_view_intro q (Ghost.reveal s field)
    (fields.get_field field).view
    (Ghost.reveal v field);
  return q
#pop-options

let addr_of_struct_field_ref #a #tag #fields #excluded field p =
  addr_of_struct_field_ref' field p

let struct'_with_field
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields) (w: (fields.get_field field).view_type)
  (v: struct' tag fields excluded)
: Pure (struct' tag fields (remove field excluded))
    (requires excluded field == true)
    (ensures fun _ -> True)
= on_dom (struct_dom fields (remove field excluded))
    (fun field' -> if field = field' then w else v field')

let struct_with_field_to_carrier'
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields) (field: field_of fields)
  (s: struct_pcm_carrier tag fields)
  (t: (fields.get_field field).carrier)
  (v: struct' tag fields excluded)
  (w: (fields.get_field field).view_type)
  (h1: squash (excluded field == true))
  (h2: squash (s == (struct_view tag fields excluded).to_carrier v))
  (h3: squash (t == (fields.get_field field).view.to_carrier w))
: Lemma
    (struct_with_field (struct_pcms fields) field t s
      == (struct_view tag fields (remove field excluded)).to_carrier
           (struct'_with_field tag fields excluded field w v))
= assert
    (struct_with_field (struct_pcms fields) field t s
      `feq` (struct_view tag fields (remove field excluded)).to_carrier
           (struct'_with_field tag fields excluded field w v))

let extract_field_with_field
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (v: struct' tag fields excluded)
  (w: (fields.get_field field).view_type)
: Lemma
    (requires excluded field == true)
    (ensures
      extract_field tag fields (remove field excluded) field
         (struct'_with_field tag fields excluded field w v)
         == (v, w))
= assert (struct'_without_field tag fields (remove field excluded) field
    (struct'_with_field tag fields excluded field w v)
    `feq` v)

let unaddr_of_struct_field_ref' #a #tag #fields #excluded field p q =
  let v: Ghost.erased (struct' tag fields excluded) =
    gget (p `pts_to_view` struct_view tag fields excluded)
  in
  let s: Ghost.erased (struct_pcm_carrier tag fields) =
    pts_to_view_elim p (struct_view tag fields excluded)
  in
  let w: Ghost.erased (fields.get_field field).view_type =
    gget (q `pts_to_view` (fields.get_field field).view)
  in
  let t: Ghost.erased (fields.get_field field).carrier =
    pts_to_view_elim q (fields.get_field field).view
  in
  unaddr_of_struct_field #_ #_ #_ #(struct_pcms fields) field q p s t;
  let h1: squash (excluded field == true) = () in
  let h2: squash (Ghost.reveal s == (struct_view tag fields excluded).to_carrier v) = () in
  let h3: squash (Ghost.reveal t == (fields.get_field field).view.to_carrier w) = () in
  struct_with_field_to_carrier' tag fields excluded field
    (Ghost.reveal s) (Ghost.reveal t) (Ghost.reveal v) (Ghost.reveal w)
    h1 h2 h3; // TODO why need pass explicitly
  pts_to_view_intro p
    (struct_with_field (struct_pcms fields) field t s)
    (struct_view tag fields (remove field excluded))
    (struct'_with_field tag fields excluded field w v);
  extract_field_with_field tag fields excluded field (Ghost.reveal v) (Ghost.reveal w);
  return ()

let unaddr_of_struct_field_ref #a #tag #fields #excluded field p q =
  unaddr_of_struct_field_ref' field p q
