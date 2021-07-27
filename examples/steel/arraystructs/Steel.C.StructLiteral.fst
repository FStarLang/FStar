module Steel.C.StructLiteral

open Steel.C.PCM
open Steel.C.Struct
open Steel.C.Typedef
open Steel.C.Ref // for refine
open FStar.List.Tot
open FStar.FunctionalExtensionality

let struct_view_types (fields: struct_fields) (field: field_of fields) =
  (get_field fields field).view_type

let struct tag fields = restricted_t (field_of fields) (struct_view_types fields)

let rec mk_struct (tag: string) (fields: list (string * typedef))
: mk_struct_ty tag fields
= match fields with
  | [] -> on_dom _ (fun field -> () <: struct_view_types fields field)
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

let struct_carriers (fields: struct_fields) (field: field_of fields) =
  (get_field fields field).carrier

let struct_pcm_carrier tag fields = restricted_t (field_of fields) (struct_carriers fields)

let struct_pcms (tag: string) (fields: struct_fields) (field: field_of fields)
: pcm (struct_carriers fields field)
= (get_field fields field).pcm

let struct_pcm tag fields = prod_pcm (struct_pcms tag fields)

let rec mk_struct_pcm (tag: string) (fields: list (string * typedef))
: mk_struct_pcm_ty tag fields
= match fields with
  | [] -> on_dom _ (fun field -> () <: struct_carriers fields field)
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
