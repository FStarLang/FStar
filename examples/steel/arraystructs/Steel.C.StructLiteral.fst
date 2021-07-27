module Steel.C.StructLiteral

open Steel.C.Typedef
open Steel.C.Ref // for refine
open FStar.List.Tot
open FStar.FunctionalExtensionality

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

/// For a fixed field name, struct_get and struct_put form a lens

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

x: struct' tag fields excluded

mk_struct_view v .. = mk_struct_view' (Some v) ..

mk_struct_view' (Some v) None

struct_type tag fields =

without:
  (#tag: string) (#fields: struct_fields) (#excluded: list string)
  (x: struct' tag fields excluded)
  (field: field_of fields excluded)
*)

(*

struct_put x field v `without_field` field
x `without_field` field

struct s excluded
struct s excluded'
f in excluded <==> f in excluded'

without_field : 
  (field: string)
  (x: struct s excluded fields) ->
  struct s (field :: excluded)

*)

(*
let struct_field_view_types fields = restricted_t (field_of fields) (type_family_of fields)

let struct_field_pcm_carriers (fields: _) (field: field_of fields) =
  (get_field fields field).carrier

let struct_field_pcms (fields: _) (field: field_of fields)
: pcm (struct_field_pcm_carriers fields field)
= (get_field fields field).pcm

let struct_pcm_carrier (fields: list (string * typedef)) =
  restricted_t (field_of fields) (struct_field_pcm_carriers fields)
  
let struct_pcm (fields: list (string * typedef))
: pcm (struct_pcm_carrier fields)
= prod_pcm (struct_field_pcms fields)

val point : Type0

let point = struct_pcm_carrier point_fields


/// PCM for struct point:

val point_pcm : pcm point

/// (mk_point x y) represents (struct point){.x = x, .y = y}

val mk_point (x y: Ghost.erased (option int)): Ghost.erased point

/// Connections for the fields of a point

val _x : connection point_pcm (opt_pcm #int)
val _y : connection point_pcm (opt_pcm #int)

/// Taking pointers to the x and y fields of a point

val addr_of_x (#x #y: Ghost.erased (option int)) (p: ref 'a point_pcm)
: SteelT (q:ref 'a (opt_pcm #int){q == ref_focus p _x})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point none y) `star`
       (q `pts_to` x))

unfold
let point_fields_pcm_carriers = struct_field_pcm_carriers point_fields

unfold
let point_fields_pcms
: field:field_of point_fields -> pcm (point_fields_pcm_carriers field)
= struct_field_pcms point_fields

unfold
let point_pcm_carrier = struct_pcm_carrier point_fields

unfold
let point_pcm: pcm point_pcm_carrier = struct_pcm point_fields

let mk_point_f_lame (x y: option int) (field: field_of point_fields)
: point_fields_pcm_carriers field
= match field with
  | "x" -> x
  | "y" -> y

(* BEGIN TODO move to Typedef *)

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

let field_pcm_carrier ((_, td): string * typedef) = td.carrier

let mk_struct_ty (fields: list (string * typedef)): Type =
  map field_pcm_carrier fields `list_fn` struct_pcm_carrier fields

let rec mk_struct (fields: list (string * typedef))
: mk_struct_ty fields
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
    
(* END move to Typedef *)

let mk_point_f
: option int -> option int -> struct_pcm_carrier point_fields
= mk_struct point_fields

let _ =
  let test (k: field_of point_fields) (x y: option int) =
    assert (mk_point_f_lame x y k == mk_point_f x y k)
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

#restart-solver

let feq' (f: restricted_t 'a 'b) (g: restricted_t 'c 'd)
= 'a == 'c /\
  normalize ('b == 'd) /\
  f `feq` g

let ext (f: restricted_t 'a 'b) (g: restricted_t 'c 'd)
: Lemma (requires f `feq'` g) (ensures f == g) //[SMTPat (f `feq'` g)]
= extensionality 'a 'b f g
  //FStar.Classical.forall_intro fg

//let ext (f g: restricted_t 'a 'b) (fg:(x:'a -> Lemma (f x == g x))) : Lemma (f == g) =
//  extensionality 'a 'b f g;
//  FStar.Classical.forall_intro fg

// let feq' (f g: restricted_t 'a 'b): prop = forall x. f x == g x

// let ext' (f g: restricted_t 'a 'b)
// : Lemma (requires f `feq'` g) (ensures f == g) [SMTPat (f `feq'` g)]
// = extensionality 'a 'b f g
//   //FStar.Classical.forall_intro fg

let aux x y : unit
= assert (Ghost.hide (struct_without_field point_fields_pcms "x" (mk_point x y)) `feq` mk_point none y);
  ()


let addr_of_x #a #x #y p =
  let q = addr_of_struct_field p "x" (mk_point x y) in
  //A.change_equal_slprop (p `pts_to` Ghost.hide (struct_without_field point_fields_pcms "x" (Ghost.reveal (mk_point x y)))) (p `pts_to` Ghost.hide (struct_without_field point_fields_pcms "x" (Ghost.reveal (mk_point x y))));
  //A.change_equal_slprop (p `pts_to` _) (p `pts_to` Ghost.hide (struct_without_field point_fields_pcms "x" (Ghost.reveal (mk_point x y))));
  //assume (Ghost.hide (struct_without_field point_fields_pcms "x" (mk_point x y)) == mk_point none y);
  //(field_of fields) (struct_field_pcm_carriers fields)
  assert (
    struct_without_field point_fields_pcms "x" (mk_point x y)
    `feq'`
    Ghost.reveal (mk_point none y));
  A.change_equal_slprop (p `pts_to` Ghost.hide (struct_without_field point_fields_pcms "x" (mk_point x y))) (p `pts_to` mk_point none y);
  //A.change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  A.sladmit();
  A.return q

// (f `feq` Ghost.reveal g)
// (Ghost.hide f == g)

(*

struct : string -> list string -> list (string & typedef) -> Type

without_field
  (field: string)
  (x: struct s excluded fields) ->
  struct s excluded
*)
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
*)


(*

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
