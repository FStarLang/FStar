module Steel.C.StructLiteral

open Steel.Memory
open Steel.Effect.Common
open Steel.Effect.Atomic

open Steel.C.PCM
open Steel.C.Struct
open Steel.C.Typedef
open Steel.C.Ref // for refine
open Steel.C.Connection
open FStar.List.Tot
open FStar.FunctionalExtensionality

let struct_view_types (fields: struct_fields) (field: field_of fields) =
  (get_field fields field).view_type

let struct tag fields = restricted_t (field_of fields) (struct_view_types fields)

let rec mk_struct (tag: string) (fields: struct_fields)
: mk_struct_ty tag fields
= match fields with
  | [(field, td)] -> fun (x:td.view_type) -> on_dom _ (fun field -> x <: struct_view_types fields field)
  | (field, td) :: fields' ->
    fun (x:td.view_type) ->
    let f: map struct_field_view_type fields' `list_fn` struct tag fields' = mk_struct tag fields' in
    let lift_struct (g: struct tag fields'): struct tag fields =
      let h (field': field_of fields): struct_view_types fields field' =
        if field' = field then x else g field'
      in on_dom _ h
    in
    list_fn_map lift_struct f

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

(*
define attribute on mk_struct_view_type, etc..

mk_struct_view': fields:list (string * _) ->
  norm [delta_attr ..; delta Fstar.list.map; ..] .. (mk_struct_view_type fields ..)
  (See FStar.Pervasives.fsti)

to translate t

  typedef_t: typedef t = { ... }

to translate struct tag { S s; ... }

  assume val struct (tag: string) (fields: list (string * typedef)): Type
  assume val mk_struct_typedef (tag: string) (fields: list (string * typedef)):
    typedef (struct tag ["s", typedef_S; ..))
  
  typedef_struct_tag: typedef (struct "tag" ["s", typedef_S; ..]) =
     mk_struct_typedef "tag" ["s", typedef_S; ..]

to translate struct loop { struct loop *again; }

// Done (assuming can store pointers in heap)
  carrier: Type0; 
  pcm: pcm carrier; 

view_type = {loop: ref struct_loop_carrier struct_loop_pcm}

mk_view_type
  (carrier: Type0)
  (pcm: pcm carrier)
-> view_type : {loop: ref struct_loop_carrier struct_loop_pcm}

mk_rec_typedef:
  (carrier: Type0)
  (pcm: pcm carrier)
-> t:typedef (mk_view_type carrier pcm) { t.carrier == carrier /\ t.pcm == pcm}

noeq type typedef = { 

// _
  view_type: Type0; 

// Should be fine
  can_view_unit: bool; 
  view: sel_view pcm view_type can_view_unit; 
} 

  typedef_struct_loop_f (recur:typedef)
  : typedef (struct "loop" ["again", ref_typedef recur.carrier recur.pcm])
  = mk_struct_typedef "loop" ["again", ref_typedef recur.carrier recur.pcm]

  typedef_struct_loop
  : typedef (struct "loop"
      ["again",
       ref_typedef
         typedef_struct_loop.carrier
         typedef_struct_loop.pcm])
  = typedef_struct_loop_f typedef_struct_loop

*)

/// TODO Would be nice to have somtehing like this but proofs get tricky

/// struct_put and struct_get are sound w.r.t. a model of structs as n-tuples

(* BEGIN public *)

let rec list_fn_args (dom: list Type) = match dom with
  | [] -> unit
  | d :: dom -> d & list_fn_args dom

let rec list_apply #dom #b (f: dom `list_fn` b) (xs: list_fn_args dom): b = match dom with
  | [] -> f
  | a :: dom ->
    let (x, xs): a & list_fn_args dom = xs in
    let f: a -> dom `list_fn` b = f in
    f x `list_apply` xs

let rec struct_get_model
  (#tag: string) (#fields: struct_fields) 
  (vs: list_fn_args (mk_struct_ty_dom tag fields))
  (field: field_of fields)
: (get_field fields field).view_type
= match fields with
  | [] -> assert false
  | (field', td) :: fields ->
    let (v, vs): td.view_type & list_fn_args (mk_struct_ty_dom tag fields) = vs in
    if field = field' then v else struct_get_model vs field

let rec struct_put_model
  (#tag: string) (#fields: struct_fields) 
  (vs: list_fn_args (mk_struct_ty_dom tag fields))
  (field: field_of fields)
  (v: (get_field fields field).view_type)
: list_fn_args (mk_struct_ty_dom tag fields)
= match fields with
  | [] -> vs
  | (field', td) :: fields ->
    let (v', vs): td.view_type & list_fn_args (mk_struct_ty_dom tag fields) = vs in
    if field = field' then (v, vs) else (v', struct_put_model vs field v)

(* END public *)

val struct_get_sound
  (#tag: string) (#fields: struct_fields) 
  (vs: list_fn_args (mk_struct_ty_dom tag fields))
  (field: field_of fields)
: Lemma (
    (mk_struct tag fields `list_apply` vs) `struct_get` field ==
    struct_get_model vs field)

(*
let rec struct_get_sound #tag #fields vs field : Lemma (ensures
    (mk_struct tag fields `list_apply` vs) `struct_get` field ==
    struct_get_model vs field) (decreases fields) = match fields with
  | [] -> ()
  | (field', td) :: fields ->
    let (v, vs): td.view_type & list_fn_args (mk_struct_ty_dom tag fields) = vs in
    let field: field_of ((field', td) :: fields) = field in
    if field = field' then begin
      let f = mk_struct tag ((field', td) :: fields) in
      assert ((list_apply #(mk_struct_ty_dom tag ((field', td) :: fields)) f (v, vs)) `struct_get` field ==
        begin
          let (x, xs): (struct_field_view_type (field', td) & list_fn_args (mk_struct_ty_dom tag fields)) = (v, vs) in
          let f: struct_field_view_type (field', td) -> (mk_struct_ty_dom tag fields `list_fn` struct tag fields) = admit() in
          f x `list_apply` xs
        end);
      assume ((list_apply #(mk_struct_ty_dom tag ((field', td) :: fields)) (mk_struct tag ((field', td) :: fields)) (v, vs)) `struct_get` field == v)
    end else admit()//struct_get_sound #tag #fields vs field
    *)

let struct_pcm_carrier tag fields = restricted_t (field_of fields) (struct_carriers fields)

let struct_pcm tag fields = prod_pcm (struct_pcms tag fields)

let rec mk_struct_pcm (tag: string) (fields: struct_fields)
: mk_struct_pcm_ty tag fields
= match fields with
  | [(field, td)] -> fun (x:td.carrier) -> on_dom _ (fun field -> x <: struct_carriers fields field)
  | (field, td) :: fields' ->
    fun (x:td.carrier) ->
    let f: map struct_field_carrier fields' `list_fn` struct_pcm_carrier tag fields' = mk_struct_pcm tag fields' in
    let lift_struct (g: struct_pcm_carrier tag fields'): struct_pcm_carrier tag fields =
      let h (field': field_of fields): struct_carriers fields field' =
        if field' = field then x else g field'
      in on_dom _ h
    in
    list_fn_map lift_struct f

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

let field_views (tag: string) (fields: struct_fields) (field: field_of fields)
: sel_view (struct_pcms tag fields field) (struct_view_types fields field) false
= (get_field fields field).view

let struct_view_to_view_prop (tag: string) (fields: struct_fields)
: struct_pcm_carrier tag fields -> prop
= fun x -> forall (field:field_of fields). (field_views tag fields field).to_view_prop (x field)

let struct_view_to_view (tag: string) (fields: struct_fields)
: refine (struct_pcm_carrier tag fields) (struct_view_to_view_prop tag fields) ->
  Tot (struct tag fields)
= fun x -> on_dom _ (fun (field: field_of fields) -> (field_views tag fields field).to_view (x field))

let struct_view_to_carrier (tag: string) (fields: struct_fields)
: struct tag fields ->
  Tot (refine (struct_pcm_carrier tag fields) (struct_view_to_view_prop tag fields))
= fun x ->
  let y: struct_pcm_carrier tag fields =
    on_dom _ (fun (field: field_of fields) ->
      (field_views tag fields field).to_carrier (x field)
      <: struct_carriers fields field)
  in y

let struct_view_to_view_frame (tag: string) (fields: struct_fields)
  (x: struct tag fields)
  (frame: struct_pcm_carrier tag fields)
: Lemma
    (requires (composable (struct_pcm tag fields) (struct_view_to_carrier tag fields x) frame))
    (ensures
      struct_view_to_view_prop tag fields
        (op (struct_pcm tag fields) (struct_view_to_carrier tag fields x) frame) /\ 
      struct_view_to_view tag fields
        (op (struct_pcm tag fields) (struct_view_to_carrier tag fields x) frame) == x)
= let p = struct_pcms tag fields in
  let aux (k:field_of fields)
  : Lemma (
      (field_views tag fields k).to_view_prop
        (op (p k) ((field_views tag fields k).to_carrier (x k)) (frame k)) /\
      (field_views tag fields k).to_view
        (op (p k) ((field_views tag fields k).to_carrier (x k)) (frame k)) == x k)
  = assert (composable (p k) ((field_views tag fields k).to_carrier (x k)) (frame k));
    (field_views tag fields k).to_view_frame (x k) (frame k)
  in FStar.Classical.forall_intro aux;
  assert (
    struct_view_to_view tag fields
       (op (prod_pcm p) (struct_view_to_carrier tag fields x) frame) `feq` x)

let struct_view_to_carrier_not_one (tag: string) (fields: struct_fields)
: squash (
    ~ (exists x. struct_view_to_carrier tag fields x == one (struct_pcm tag fields)) /\
    ~ (struct_view_to_view_prop tag fields (one (struct_pcm tag fields))))
= let (field, _) :: _ = fields in
  let field: field_of fields = field in
  (field_views tag fields field).to_carrier_not_one

let struct_view tag fields = {
  to_view_prop = struct_view_to_view_prop tag fields;
  to_view = struct_view_to_view tag fields;
  to_carrier = struct_view_to_carrier tag fields;
  to_carrier_not_one = struct_view_to_carrier_not_one tag fields;
  to_view_frame = struct_view_to_view_frame tag fields;
}

let struct_field tag fields field = struct_field (struct_pcms tag fields) field
