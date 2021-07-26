module PointStruct

open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection
open Steel.C.Struct
open FStar.FunctionalExtensionality
open Steel.Effect
module A = Steel.Effect.Atomic

open Steel.C.Typedef
open FStar.List.Tot
open FStar.FunctionalExtensionality

let c_int: typedef = {
  carrier = option int;
  pcm = opt_pcm #int;
  view_type = int;
  can_view_unit = false;
  view = opt_view int;
}

let point_fields = [
  "x", c_int;
  "y", c_int;
]

(* TODO move to Steel.C.Typedef *)
let struct_field_view_types fields = restricted_t (field_of fields) (type_family_of fields)
let struct_field_pcm_carriers (fields: _) (field: field_of fields) = (get_field fields field).carrier
let struct_field_pcms (fields: _) (field: field_of fields) = (get_field fields field).pcm
let struct_pcm_carrier (fields: list (string * typedef)) =
  restricted_t (field_of fields) (struct_field_pcm_carriers fields)
let struct_pcm (fields: list (string * typedef)) = prod_pcm (struct_field_pcms fields)

let point = struct_field_view_types point_fields
let point_fields_pcm_carriers = struct_field_pcm_carriers point_fields
let point_fields_pcms = struct_field_pcms point_fields
let point_pcm_carrier = struct_pcm_carrier point_fields
let point_pcm = struct_pcm point_fields

(* TODO move to Typedef *)
let rec mk_struct_curried_dom (fields: list (string * typedef)): Type =
  match fields with
  | [] -> unit
  | [(_, td)] -> td.carrier
  | (_, td) :: fields -> td.carrier * mk_struct_curried_dom fields

let rec mk_struct_curried (fields: list (string * typedef))
: mk_struct_curried_dom fields -> struct_pcm_carrier fields
= match fields with
  | [] -> 
    fun () -> on_dom _ (fun field -> () <: struct_field_pcm_carriers fields field)
  | [(field, td)] ->
    fun x -> on_dom (field_of fields) (fun field' ->
    assert (field == field'); x <: struct_field_pcm_carriers fields field')
  | (field, td) :: fields' ->
    fun ((x, xs): td.carrier * mk_struct_curried_dom fields') ->
    on_dom (field_of fields) (fun field'' ->
    if field'' = field then x
    else mk_struct_curried fields' xs field'' <: struct_field_pcm_carriers fields field'')

let mk_point_f_lame (x y: option int) (field: field_of point_fields)
: point_fields_pcm_carriers field
= match field with
  | "x" -> x
  | "y" -> y

let mk_point_curried
: option int * option int -> struct_pcm_carrier point_fields
= mk_struct_curried point_fields

let _ =
  let test (k: field_of point_fields) (x y: option int) =
    assert (mk_point_f_lame x y k == mk_point_curried (x, y) k)
  in ()

let rec list_fn (dom: list Type) (cod: Type) =
  match dom with
  | [] -> cod
  | d :: dom -> d -> list_fn dom cod

let rec list_fn_map #dom (f: 'a -> 'b) (g: dom `list_fn` 'a): dom `list_fn` 'b =
  match dom with 
  | [] -> f g <: [] `list_fn` 'b
  | d :: dom' ->
    let g: d -> dom' `list_fn` 'a = g in
    fun (x:d) -> list_fn_map f (g x) <: dom' `list_fn` 'b

(* TODO move to Typedef *)
let field_pcm_carrier ((_, td): string * typedef) = td.carrier
let mk_struct_ty (fields: list (string * typedef)): Type =
  map field_pcm_carrier fields `list_fn` struct_pcm_carrier fields

let rec mk_struct (fields: list (string * typedef)): mk_struct_ty fields
= match fields with
  | [] -> on_dom _ (fun field -> () <: struct_field_pcm_carriers fields field)
  | (field, td) :: fields' ->
    fun (x:td.carrier) ->
    let f: map field_pcm_carrier fields' `list_fn` struct_pcm_carrier fields' = mk_struct fields' in
    let lift_struct (g: struct_pcm_carrier fields'): struct_pcm_carrier fields =
      let h (field': field_of fields): struct_field_pcm_carriers fields field' =
        if field' = field then x else g field'
      in on_dom _ h
    in
    list_fn_map lift_struct f

let mk_point_uncurried
: option int -> option int -> struct_pcm_carrier point_fields
= mk_struct point_fields

let _ =
  let test (k: field_of point_fields) (x y: option int) =
    assert (mk_point_f_lame x y k == mk_point_uncurried x y k)
  in ()

let mk_point (x y: Ghost.erased (option int)): Ghost.erased point =
  Ghost.hide (on_dom _ (mk_point_f_lame (Ghost.reveal x) (Ghost.reveal y)))

let _x = struct_field point_fields_pcms "x"
let _y = struct_field point_fields_pcms "y"

/// Taking pointers to the x and y fields of a point

let point_without_x x y
: Lemma (struct_without_field point_fields_pcms "x" (mk_point x y) `feq` Ghost.reveal (mk_point none y))
  [SMTPat (mk_point x y)]
= ()

let point_with_x x y
: Lemma (struct_with_field point_fields_pcms "x" (Ghost.reveal x) (mk_point none y) `feq`
         Ghost.reveal (mk_point x y))
  [SMTPat (mk_point x y)]
= ()

let point_without_y x y
: Lemma (struct_without_field point_fields_pcms "y" (mk_point x y) `feq` Ghost.reveal (mk_point x none))
  [SMTPat (mk_point x y)]
= ()

let point_with_y x y
: Lemma (struct_with_field point_fields_pcms "y" (Ghost.reveal y) (mk_point x none) `feq`
         Ghost.reveal (mk_point x y))
  [SMTPat (mk_point x y)]
= ()

let aux x y : unit
= assert ((struct_without_field point_fields_pcms "x" (mk_point x y)
      <: restricted_t (field_of point_fields) point_fields_pcm_carriers) `feq`
    (Ghost.reveal (mk_point none y) 
      <: restricted_t (field_of point_fields) point_fields_pcm_carriers)
    );
  assert ((struct_without_field point_fields_pcms "x" (mk_point x y)
      <: restricted_t (field_of point_fields) point_fields_pcm_carriers) ==
    (Ghost.reveal (mk_point none y) 
      <: restricted_t (field_of point_fields) point_fields_pcm_carriers)
    );
  ()

let aux x y : unit
= assert (Ghost.hide (struct_without_field point_fields_pcms "x" (mk_point x y)) == mk_point none y);
  ()

let addr_of_x #a #x #y p =
  let q = addr_of_struct_field p "x" (mk_point x y) in
  assert (Ghost.hide (struct_without_field point_fields_pcms "x" (mk_point x y)) == mk_point none y);
  //A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point none y);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  A.sladmit();
  A.return q

let addr_of_struct_field
  (#base:Type) (#a:eqtype) (#b: a -> Type u#b) (#p:(k:a -> pcm (b k)))
  (r: ref base (prod_pcm p)) (k:a)
  (xs: Ghost.erased (restricted_t a b))
: Steel (ref base (p k))
    (r `pts_to` xs)
    (fun s ->
      (r `pts_to` struct_without_field p k xs) `star` 
      (s `pts_to` Ghost.reveal xs k))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r (struct_field p k))
= struct_peel p k xs;
  split r xs (struct_without_field p k xs) (field_to_struct_f p k (Ghost.reveal xs k));
  let r = focus r (struct_field p k) (field_to_struct_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k) in
  A.return r

let unaddr_of_x #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #point_fields_pcms "x" q p (mk_point none y) x; // FIXME: WHY WHY WHY does F* infer the constant function (due to the type of q) instead?
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_y #a #x #y p =
  let q = addr_of_struct_field p "y" (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point x none);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` y);
  A.return q

let unaddr_of_y #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #point_fields_pcms "y" q p (mk_point x none) y; // same here
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let struct_point_fields = [
  "x", c_int;
  "y", c_int;
]

let point_field_of_string (field: field_of struct_point_fields): point_field =
  match field with
  | "x" -> X
  | "y" -> Y

let struct_point_view_t (k: field_of struct_point_fields): Type =
  (get_field struct_point_fields k).view_type

let struct_point_view_pcm_t (k: field_of struct_point_fields): Type =
  point_fields (point_field_of_string k)
  
let struct_point_view_pcm (k: field_of struct_point_fields)
: pcm (struct_point_view_pcm_t k)
= point_fields_pcms (point_field_of_string k)

let struct_point_fields_view (k:field_of struct_point_fields)
: sel_view (point_fields_pcms (point_field_of_string k)) (struct_point_view_t k) false
= (get_field struct_point_fields k).view

(*
let struct_view
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: sel_view (prod_pcm p)
    (restricted_t (refine a (mem included)) view_t)
    (can_view_units || Nil? included) *)

let point_view
//: sel_view (prod_pcm struct_point_view_pcm_t) (view_type_of struct_point_fields) false
= struct_view struct_point_fields_view (map (admit() )struct_point_fields)

// = {
//   to_view_prop = (fun x -> Some? x == true);
//   to_view = (fun x -> Some?.v x);
//   to_carrier = (fun z  -> Some z);
//   to_carrier_not_one = ();
//   to_view_frame = (fun x frame -> ());
// }
