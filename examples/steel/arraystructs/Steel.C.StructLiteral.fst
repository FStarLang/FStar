module Steel.C.StructLiteral

open Steel.Memory
open Steel.Effect
open Steel.Effect.Common
open Steel.Effect.Atomic

open Steel.C.PCM
open Steel.C.Struct
open Steel.C.Typedef
open Steel.C.Ref // for refine
open Steel.C.Connection
open FStar.List.Tot
open FStar.FunctionalExtensionality

// open ChurchList

(**** MOVE TO ChurchList *)

let rec list_elim (xs: list 'a)
  (b:(list 'a -> Type))
  (base:b [])
  (ind:(x:'a -> xs:list 'a -> b xs -> b (x :: xs)))
: b xs
= match xs with
  | [] -> base
  | x :: xs -> ind x xs (list_elim xs b base ind)

let elim_t (#a: Type u#a) (xs: list a): Tot (Type u#(max a (1 + b))) =
  b:(list a -> Type u#b) ->
  base:b [] ->
  ind:(x:a -> xs:list a -> b xs -> b (x :: xs)) ->
  b xs

//[@@__reduce__]
noeq type clist (a:Type u#a): Type = {
  raw: list a;
  elim0: elim_t u#_ u#0 raw;
  elim1: elim_t u#_ u#1 raw;
  elim2: elim_t u#_ u#2 raw;
  elim3: elim_t u#_ u#3 raw;
}

//[@@__reduce__]
let clist_elim0
  (c: clist 'a)
  (b:(list 'a -> Type0))
  (base:b [])
  (ind:(x:'a -> xs:list 'a -> b xs -> b (x :: xs)))
: Pure (b c.raw)
  (requires True)
  (ensures (fun y -> y == list_elim c.raw b base ind))
= let b' (l2: list 'a) : Type =
    (x: b l2 { x == list_elim l2 b base ind })
  in
  c.elim0
    b'
    base
    (fun x xs x' -> ind x xs x')

//[@@__reduce__]
let clist_elim1
  (c: clist 'a)
  (b:(list 'a -> Type u#1))
  (base:b [])
  (ind:(x:'a -> xs:list 'a -> b xs -> b (x :: xs)))
: Pure (b c.raw)
  (requires True)
  (ensures (fun y -> y == list_elim c.raw b base ind))
= let b' (l2: list 'a) : Type =
    (x: b l2 { x == list_elim l2 b base ind })
  in
  c.elim1
    b'
    base
    (fun x xs x' -> ind x xs x')

//[@@__reduce__]
let clist_elim2
  (c: clist 'a)
  (b:(list 'a -> Type u#2))
  (base:b [])
  (ind:(x:'a -> xs:list 'a -> b xs -> b (x :: xs)))
: Pure (b c.raw)
  (requires True)
  (ensures (fun y -> y == list_elim c.raw b base ind))
= let b' (l2: list 'a) : Type =
    (x: b l2 { x == list_elim l2 b base ind })
  in
  c.elim2
    b'
    base
    (fun x xs x' -> ind x xs x')

#push-options "--print_universes --print_implicits"

#push-options "--fuel 0"
let mk_clist (xs: list 'a) = {
  raw = xs;
  elim0 = list_elim xs;
  elim1 = list_elim xs;
  elim2 = list_elim xs;
  elim3 = list_elim xs;
}
let _ =
  let xs = normalize_term (mk_clist [1; 2; 3; 4]) in
  assert (clist_elim0 xs (fun _ -> int) 0 (fun x xs sum_xs -> x + sum_xs) == 10)
#pop-options

//[@@__reduce__]
let nil (#a: Type u#a): clist u#a a = {
  raw = [];
  elim0 = (fun _ base _ -> base);
  elim1 = (fun _ base _ -> base);
  elim2 = (fun _ base _ -> base);
  elim3 = (fun _ base _ -> base);
}

//[@@__reduce__]
let cons (#a: Type u#a) (x: a) (xs: clist u#a a): clist u#a a = {
  raw = x :: xs.raw;
  elim0 = (fun b base ind -> ind x xs.raw (xs.elim0 b base ind));
  elim1 = (fun b base ind -> ind x xs.raw (xs.elim1 b base ind));
  elim2 = (fun b base ind -> ind x xs.raw (xs.elim2 b base ind));
  elim3 = (fun b base ind -> ind x xs.raw (xs.elim3 b base ind));
}

//[@@__reduce__]
let cmem (#a:eqtype) (#b: Type u#b) (x: a) (xs: clist u#0 a): bool
= clist_elim0 xs (fun _ -> bool) false (fun x' xs recur -> x = x' || recur)

//[@@__reduce__]
let cmem_ok (#a:eqtype) (x: a) (xs: clist u#0 a)
: Lemma (cmem x xs == mem x xs.raw)
= let rec aux (xs: list a)
  : Lemma (list_elim xs (fun _ -> bool) false (fun x' xs recur -> x = x' || recur) == mem x xs)
  = match xs with [] -> () | x :: xs -> aux xs
  in aux xs.raw

(**** END MOVE TO ChurchList *)

(**** BEGIN PUBLIC *)

let struct_fields = clist u#1 (string * typedef)

//[@@__reduce__]
let has_field_bool (fields: struct_fields) (field: string): bool =
  clist_elim0 fields (fun _ -> bool)
    false
    (fun (field', td) fields recur -> field = field' || recur)

let has_field_bool_spec (fields: struct_fields) (field: string)
: Lemma (has_field_bool fields field == field `mem` map fst fields.raw)
  [SMTPat (has_field_bool fields field)]
= let rec aux (fields: list (string * typedef))
  : Lemma (list_elim fields (fun _ -> bool) false
      (fun (field', td) fields recur -> field = field' || recur)
      == field `mem` map fst fields)
  = match fields with [] -> () | _ :: fields -> aux fields
  in aux fields.raw

//[@@__reduce__]
let has_field (fields: struct_fields)
: (string ^-> prop)
= on_dom string (fun field -> has_field_bool fields field == true <: prop)

let field_of (fields: struct_fields) = refine string (has_field fields)

assume val trivial_typedef: typedef

//[@@__reduce__]
let get_field (fields: struct_fields) (field: field_of fields): typedef =
  clist_elim1 fields (fun fields -> typedef) trivial_typedef
    (fun (field', td) fields recur -> if field = field' then td else recur)

(**** END PUBLIC *)

let has_field_bool' (fields: list (string * typedef)) (field: string): bool =
  field `mem` map fst fields

let has_field' (fields: list (string * typedef))
: (string ^-> prop)
= on_dom _ (fun field -> has_field_bool' fields field == true <: prop)

let field_of' (fields: list (string * typedef)) =
  refine string (has_field' fields)

let get_field' (fields: list (string * typedef)) (field: field_of' fields): typedef =
  assoc_mem field fields;
  Some?.v (assoc field fields)

let get_field_spec_aux (fields: struct_fields) (field: field_of fields)
: Lemma (get_field fields field
    == (match assoc field fields.raw with Some td -> td | None -> trivial_typedef))
= let rec aux (fields: list (string * typedef))
  : Lemma (
      list_elim fields (fun fields -> typedef) trivial_typedef
        (fun (field', td) fields recur -> if field = field' then td else recur)
      == (match assoc field fields with Some td -> td | None -> trivial_typedef))
  = match fields with [] -> () | _ :: fields -> aux fields
  in aux fields.raw

let get_field_spec (fields: struct_fields) (field: field_of fields)
: Lemma (get_field fields field == get_field' fields.raw field)
  [SMTPat (get_field fields field)]
= assoc_mem field fields.raw;
  get_field_spec_aux fields field

#push-options "--fuel 0"
assume val nontrivial_typedef: typedef
let _ =
  let test_fields = normalize_term (mk_clist [
    "a", trivial_typedef;
    "b", trivial_typedef;
    "c", trivial_typedef;
    "d", trivial_typedef;
    "e", trivial_typedef;
    "f", trivial_typedef;
    "g", trivial_typedef;
    "h", trivial_typedef;
    "i", trivial_typedef;
    "j", nontrivial_typedef;
  ]) in
  assert (has_field_bool test_fields "e" == true);
  assert (get_field test_fields "j" == nontrivial_typedef)
#pop-options

(**** BEGIN PUBLIC *)

/// A view type for structs

//[@@__reduce__]
let struct_views (fields: struct_fields) (field: field_of fields)
: sel_view ((get_field fields field).pcm) ((get_field fields field).view_type) false
= (get_field fields field).view

let const_Type (x: 'a) = Type

//[@@__reduce__]
let struct_view_types (fields: struct_fields)
: restricted_t (field_of fields) const_Type
= on_dom _ (fun field -> (get_field fields field).view_type)

val struct (tag: string) (fields: struct_fields): Type0

(**** END PUBLIC *)

let struct_view_types' (fields: list (string * typedef))
: restricted_t (field_of' fields) const_Type
= on_dom _ (fun field -> (get_field' fields field).view_type)

let struct tag fields = restricted_t (field_of fields) (struct_view_types fields)

(**** BEGIN PUBLIC *)

let struct_field_view_type ((_, td): string * typedef): Type = td.view_type

(*
let mk_struct_ty_dom (tag: string) (fields: struct_fields)
: clist u#1 u#2 Type0
= cmap struct_field_view_type fields

let clist_fn (dom: clist u#(1 + c) u#(max b (1 + c)) (Type u#c)) (cod: Type u#c): Type u#c =
  raise_clist_elim dom (fun _ -> Type u#c) cod (fun d dom recur -> d -> recur)

let mk_struct_ty (tag: string) (fields: struct_fields): Type =
  clist_fn u#0 u#2 (mk_struct_ty_dom tag fields) (struct tag fields)

/// A struct literal
val mk_struct (tag: string) (fields: struct_fields): mk_struct_ty tag fields
*)
(**** END PUBLIC *)

let struct' tag fields = restricted_t (field_of' fields) (struct_view_types' fields)

let field_of_eq fields
: Lemma (field_of fields == field_of' fields.raw)
  [SMTPat (field_of fields)]
= assert (has_field fields `feq` has_field' fields.raw)

let ext' (a a': Type) (b: a -> Type) (b': a' -> Type)
  (f: restricted_t a b)
  (g: restricted_t a' b')
: Lemma (requires a == a' /\ b == b' /\ f `feq` g) (ensures f == g)
= ()

let struct_view_types_eq fields
: Lemma (struct_view_types fields == struct_view_types' fields.raw)
  [SMTPat (struct_view_types fields)]
= ext' _ _ _ _ (struct_view_types fields) (struct_view_types' fields.raw)

let list_fn (dom: list (Type u#a)) (cod: Type u#a): Type u#a =
  list_elim dom (fun _ -> Type) cod (fun d dom recur -> d -> recur)

let mk_struct_ty' tag fields =
  map struct_field_view_type fields `list_fn` struct' tag fields

(*
let mk_struct_ty_eq tag fields
: Lemma (mk_struct_ty tag fields == mk_struct_ty' tag fields.raw)
= ()

let unreachable (a: Type) : Pure a (requires False) (ensures fun _ -> True)
= ()

let rec list_fn_map #dom (f: 'a -> 'b) (g: dom `list_fn` 'a): dom `list_fn` 'b = match dom with 
  | [] -> f g <: [] `list_fn` 'b
  | d :: dom' ->
    let g: d -> dom' `list_fn` 'a = g in
    fun (x:d) -> list_fn_map f (g x) <: dom' `list_fn` 'b

let rec mk_struct' (tag: string) (fields: list (string * typedef))
: mk_struct_ty' tag fields
= match fields with
  | [] -> on_dom (field_of' []) (fun field -> unreachable (struct_view_types' [] field))
  | (field, td) :: fields' ->
    fun (x:td.view_type) ->
    let lift_struct (g: struct' tag fields'): struct' tag fields =
      let h (field': field_of' fields): struct_view_types' fields field' =
        if field' = field then x else g field'
      in on_dom _ h
    in
    list_fn_map lift_struct (mk_struct' tag fields')

let mk_struct tag fields = mk_struct' tag fields.raw
*)

(*
let one_list_elim
  (b:(list Type -> Type))
  (base:b [])
  (ind:(x:Type -> xs:list Type -> b xs -> b (x :: xs)))
: b [int]
= ind int [] base

let one_list_elim'
  (base:Type)
  (ind:(x:Type -> xs:list Type -> Type -> Type))
: Type
= ind int [] base

let one_list_elim''
  (base:Type)
: Type
= int -> base
*)

(*
let f (a:Type): Type = int -> a

let _ = assert (f bool == (int -> bool))
*)

#push-options "--fuel 0"

(*
let _ =
  //let c_int: typedef = {
  //  carrier = option int;
  //  pcm = Steel.C.Opt.opt_pcm #int;
  //  view_type = int;
  //  view = Steel.C.Opt.opt_view int;
  //} in
  //let fields = normalize_term (mk_clist [
  //  "x", c_int;
  //  //"y", c_int;
  //  //"z", c_int;
  //]) in
  //let args = normalize_term (fun b base ind -> list_elim (int :: ([] #Type))) in
  //assert (args `clist_fn` bool == (int -> bool));
  //assert (one_list_elim (fun _ -> Type) bool (fun d dom recur -> int -> recur)
  //  == (int -> bool));
  //assert (one_list_elim' bool (fun d dom recur -> int -> recur)
  //  == (int -> bool));
  assert (one_list_elim'' bool == (int -> bool));
  //assert (args.elim (fun _ -> int) 0 (fun n ns sum -> n + sum)
  //  == 3);
  //assert (mk_struct_ty "a" fields == (int -> struct "a" fields));
  //let _ : int -> int -> int -> struct "a" fields =
  //  mk_struct "a" fields
  //in ()
  ()
*)

#pop-options

(**** BEGIN PUBLIC *)
/// Reading a struct field
val struct_get
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields) (field: field_of fields)
: (get_field fields field).view_type

/// Writing a struct field
val struct_put
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v: (get_field fields field).view_type)
: struct tag fields
(**** END PUBLIC *)

let struct_get x field = x field
let struct_put x field v = on_dom _ (fun field' -> if field = field' then v else x field')

(**** BEGIN PUBLIC *)

/// For a fixed field name, struct_get and struct_put form a lens

val struct_get_put 
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v: (get_field fields field).view_type)
: Lemma (struct_put x field v `struct_get` field == v)
  [SMTPat (struct_put x field v `struct_get` field)]

val struct_put_get
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
: Lemma (struct_put x field (x `struct_get` field) == x)
  [SMTPat (struct_put x field (x `struct_get` field))]

val struct_put_put
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v w: (get_field fields field).view_type)
: Lemma (struct_put (struct_put x field v) field w == struct_put x field w)
  [SMTPat (struct_put (struct_put x field v) field w)]

/// struct_get/struct_put pairs for different fields don't interfere with each other

val struct_get_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (get_field fields field1).view_type)
: Lemma
    (requires field1 =!= field2)
    (ensures struct_put x field1 v `struct_get` field2 == x `struct_get` field2)
  [SMTPat (struct_put x field1 v `struct_get` field2)]
  
val struct_put_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field1: field_of fields)
  (v: (get_field fields field1).view_type)
  (field2: field_of fields)
  (w: (get_field fields field2).view_type)
: Lemma
    (requires field1 =!= field2)
    (ensures
      struct_put (struct_put x field1 v) field2 w ==
      struct_put (struct_put x field2 w) field1 v)
(**** END PUBLIC *)

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

(**** BEGIN PUBLIC *)
/// Similarly, a PCM for structs

//[@@__reduce__]
let struct_carriers (fields: struct_fields)
: restricted_t (field_of fields) const_Type
= on_dom _ (fun (field: field_of fields) -> (get_field fields field).carrier)

//[@@__reduce__]
let struct_pcms (tag: string) (fields: struct_fields) (field: field_of fields)
: pcm (struct_carriers fields field)
= (get_field fields field).pcm

val struct_pcm_carrier (tag: string) (fields: struct_fields): Type0
(**** END PUBLIC *)

let struct_carriers' (fields: list (string * typedef))
: restricted_t (field_of' fields) const_Type
= on_dom _ (fun field -> (get_field' fields field).carrier)

let struct_carriers_eq fields
: Lemma (struct_carriers fields == struct_carriers' fields.raw)
  [SMTPat (struct_carriers fields)]
= ext' _ _ _ _ (struct_carriers fields) (struct_carriers' fields.raw)
  
let struct_pcm_carrier' tag fields = restricted_t (field_of' fields) (struct_carriers' fields)

let struct_pcm_carrier tag fields = restricted_t (field_of fields) (struct_carriers fields)

let struct_pcms' (tag: string) (fields: list (string * typedef)) (field: field_of' fields)
: pcm (struct_carriers' fields field)
= (get_field' fields field).pcm

(**** BEGIN PUBLIC *)
val struct_pcm (tag: string) (fields: struct_fields): pcm (struct_pcm_carrier tag fields)
(**** END PUBLIC *)
let struct_pcm tag fields = prod_pcm (struct_pcms tag fields)

let struct_field_carrier ((_, td): string * typedef): Type = td.carrier

(**** BEGIN PUBLIC *)
let struct_pcm_one (tag: string) (fields: struct_fields)
: struct_pcm_carrier tag fields
= one (struct_pcm tag fields)

/// Reading a pcm_struct_carrier field
val struct_pcm_get
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields) (field: field_of fields)
: (get_field fields field).carrier

/// Writing a struct_pcm_carrier field
val struct_pcm_put
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (get_field fields field).carrier)
: struct_pcm_carrier tag fields

(**** END PUBLIC *)

let struct_pcm_get x field = x field
let struct_pcm_put x field v = on_dom _ (fun field' -> if field = field' then v else x field')

(**** BEGIN PUBLIC *)

/// For a fixed field name, struct_pcm_get and struct_pcm_put form a lens

val struct_pcm_get_put 
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (get_field fields field).carrier)
: Lemma (struct_pcm_put x field v `struct_pcm_get` field == v)
  [SMTPat (struct_pcm_put x field v `struct_pcm_get` field)]

val struct_pcm_put_get
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
: Lemma (struct_pcm_put x field (x `struct_pcm_get` field) == x)
  [SMTPat (struct_pcm_put x field (x `struct_pcm_get` field))]

val struct_pcm_put_put
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v w: (get_field fields field).carrier)
: Lemma (struct_pcm_put (struct_pcm_put x field v) field w == struct_pcm_put x field w)
  [SMTPat (struct_pcm_put (struct_pcm_put x field v) field w)]
  
/// struct_pcm_get/struct_pcm_put pairs for different fields don't interfere with each other

val struct_pcm_get_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (get_field fields field1).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures struct_pcm_put x field1 v `struct_pcm_get` field2 == x `struct_pcm_get` field2)
  [SMTPat (struct_pcm_put x field1 v `struct_pcm_get` field2)]
  
val struct_pcm_put_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (v: (get_field fields field1).carrier)
  (field2: field_of fields)
  (w: (get_field fields field2).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures
      struct_pcm_put (struct_pcm_put x field1 v) field2 w ==
      struct_pcm_put (struct_pcm_put x field2 w) field1 v)

/// Struct PCM carrier values are extensional

let struct_eq
  (#tag: string) (#fields: struct_fields)
  (x y: struct_pcm_carrier tag fields)
= forall (field: field_of fields).
  x `struct_pcm_get` field == y `struct_pcm_get` field

// let struct_eq
//   (#tag: string) (#fields: struct_fields)
//   (x y: struct_pcm_carrier tag fields)
// = raise_clist_elim u#1 u#2 u#_ fields (fun _ -> prop) True
//     (fun (field, td) _ recur ->
//       has_field_bool fields field /\
//       x `struct_pcm_get` field == y `struct_pcm_get` field /\
//       recur)

val struct_pcm_ext
  (#tag: string) (#fields: struct_fields)
  (x y: struct_pcm_carrier tag fields)
: Lemma
    (requires x `struct_eq` y)
    (ensures x == y)
    [SMTPat (x `struct_eq` y)]

(**** END PUBLIC *)

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

let struct_pcm_ext x y = assert (x `feq` y)

#push-options "--fuel 0"
let _ =
  let c_int: typedef = {
    carrier = option int;
    pcm = Steel.C.Opt.opt_pcm #int;
    view_type = int;
    view = Steel.C.Opt.opt_view int;
  } in
  let fields = normalize_term (mk_clist [
    "x", c_int;
    "y", c_int;
    "z", c_int;
    //"w", c_int;
  ]) in
  let aux (s t: struct_pcm_carrier "" fields) =
    //assert (has_field_bool fields "x");
    //assert (has_field_bool fields "y");
    //assert (has_field_bool fields "z");
    let x: field_of fields = "x" in
    let y: field_of fields = "y" in
    let z: field_of fields = "z" in
    //assert (has_field_bool fields "w");
    //assume (s `struct_pcm_get` "x" == t `struct_pcm_get` "x");
    //assume (s `struct_pcm_get` "y" == t `struct_pcm_get` "y");
    //assume (s `struct_pcm_get` "z" == t `struct_pcm_get` "z");
    //assume (s `struct_pcm_get` "w" == t `struct_pcm_get` "w");
    assume (s `struct_pcm_get` x == t `struct_pcm_get` x);
    assume (s `struct_pcm_get` y == t `struct_pcm_get` y);
    assume (s `struct_pcm_get` z == t `struct_pcm_get` z);
    //assume (s `struct_pcm_get` w == t `struct_pcm_get` w);
    //assert (s `struct_eq` t);
    ()
  in ()
#pop-options

(**** BEGIN PUBLIC *)

/// View a struct_pcm_carrier as a struct
val struct_view (tag: string) (fields: struct_fields{Cons? fields.raw})
: sel_view (struct_pcm tag fields) (struct tag fields) false

(**** END PUBLIC *)

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
      <: struct_carriers' fields.raw field)
  in y

#push-options "--z3rlimit 30"
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
       
let struct_view_to_carrier_not_one (tag: string) (fields: struct_fields{Cons? fields.raw})
: squash (
    ~ (exists x. struct_view_to_carrier tag fields x == one (struct_pcm tag fields)) /\
    ~ (struct_view_to_view_prop tag fields (one (struct_pcm tag fields))))
= let (field, _) :: _ = fields.raw in
  let field: field_of fields = field in
  (field_views tag fields field).to_carrier_not_one

let struct_view tag fields = {
  to_view_prop = struct_view_to_view_prop tag fields;
  to_view = struct_view_to_view tag fields;
  to_carrier = struct_view_to_carrier tag fields;
  to_carrier_not_one = struct_view_to_carrier_not_one tag fields;
  to_view_frame = struct_view_to_view_frame tag fields;
}

(**** MOVE EVERYTHING BELOW TO SEPARATE FILES *)

/// TODO move and dedup with Steel.C.Ptr.fst

let vpure_sel'
  (p: prop)
: Tot (selector' (squash p) (Steel.Memory.pure p))
= fun (m: Steel.Memory.hmem (Steel.Memory.pure p)) -> pure_interp p m

let vpure_sel
  (p: prop)
: Tot (selector (squash p) (Steel.Memory.pure p))
= vpure_sel' p

[@@ __steel_reduce__]
let vpure'
  (p: prop)
: GTot vprop'
= {
  hp = Steel.Memory.pure p;
  t = squash p;
  sel = vpure_sel p;
}

[@@ __steel_reduce__]
let vpure (p: prop) : Tot vprop = VUnit (vpure' p)

let intro_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    emp
    (fun _ -> vpure p)
    (fun _ -> p)
    (fun _ _ h' -> p)
=
  change_slprop_rel
    emp
    (vpure p)
    (fun _ _ -> p)
    (fun m -> pure_interp p m)

let elim_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    (vpure p)
    (fun _ -> emp)
    (fun _ -> True)
    (fun _ _ _ -> p)
=
  change_slprop_rel
    (vpure p)
    emp
    (fun _ _ -> p)
    (fun m -> pure_interp p m; reveal_emp (); intro_emp m)

assume val pts_to_v
  (#pcm: pcm 'b) (#can_view_unit: bool)
  (p: ref 'a pcm) (view: sel_view pcm 'c can_view_unit)
  (v: 'c)
: vprop
//= (p `pts_to_view` view) `vdep` (fun x -> vpure (x == v))

assume val struct_get'
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields) (field: field_of fields)
: (get_field fields field).view_type

assume val struct_field':
  tag: string -> fields: struct_fields -> field: field_of fields
    -> Prims.Tot
      (connection #(struct_pcm_carrier tag fields)
          #(struct_carriers fields field)
          (struct_pcm tag fields)
          (struct_pcms tag fields field))

//[@@__reduce__]
let pts_to_field
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
  (s: struct tag fields)
  (field: field_of fields)
: vprop
= pts_to_v
    (ref_focus p (struct_field' tag fields field))
    (struct_views fields field)
    (s `struct_get'` field)

//[@@__reduce__]
let pts_to_fields'
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
  (s: struct tag fields)
  (fields': struct_fields)
: vprop
= clist_elim2 fields' (fun _ -> vprop)
    emp
    (fun (field, _) _ recur ->
      if has_field_bool fields field then begin
        pts_to_field tag fields p s field `star` recur
      end else emp)

//[@@__reduce__]
let pts_to_fields
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
  (s: struct tag fields)
: vprop
= pts_to_fields' tag fields p s fields

assume val explode (#opened: inames)
  (tag: string) (fields: struct_fields{Cons? fields.raw})
  (p: ref 'a (struct_pcm tag fields))
  (s: Ghost.erased (struct tag fields))
: SteelGhostT unit opened
    (pts_to_v p (struct_view tag fields) s)
    (fun _ -> pts_to_fields tag fields p s)

assume val recombine (#opened: inames)
  (tag: string) (fields: struct_fields{Cons? fields.raw})
  (p: ref 'a (struct_pcm tag fields))
  (s: Ghost.erased (struct tag fields))
: SteelGhostT unit opened
    (pts_to_fields tag fields p s)
    (fun _ -> pts_to_v p (struct_view tag fields) s)

/// Point struct

open Steel.C.Opt

//[@@__reduce__]
let c_int: typedef = {
  carrier = option int;
  pcm = opt_pcm #int;
  view_type = int;
  view = opt_view int;
}

//[@@__reduce__]
//let point_fields: struct_fields =
//  cons ("x", c_int) (cons ("y", c_int) nil)
//  //normalize_term (fun c_int -> cons ("x", c_int) (cons ("y", c_int) nil)) c_int
  
//[@@__reduce__]
let point_fields: struct_fields = normalize_term (fun c_int -> mk_clist [
  "x", c_int;
  "y", c_int;
]) c_int // NOTE: tricky! pull c_int out to avoid normalizing into lambdas
  
//[@@__reduce__]
let point_fields': struct_fields = point_fields

//[@@__reduce__]
let point = struct "point" point_fields

//[@@__reduce__]
let point_pcm_carrier = struct_pcm_carrier "point" point_fields
//[@@iter_unfold]
//[@@__reduce__]
let point_pcm: pcm point_pcm_carrier = struct_pcm "point" point_fields

/// (mk_point x y) represents (struct point){.x = x, .y = y}
/// (mk_point_pcm x y) same, but where x and y are PCM carrier values

//let mk_point: int -> int -> point = mk_struct "point" point_fields
//let mk_point_pcm: option int -> option int -> point_pcm_carrier = mk_struct_pcm "point" point_fields

#push-options "--fuel 0"

let _ = assert (struct_pcm_carrier "point" point_fields == point_pcm_carrier)

let _ = assert (struct_carriers point_fields "x" == option int)

let _ = assert (struct_pcm "point" point_fields == point_pcm)

let _ = assert (struct_pcms "point" point_fields "x" == c_int.pcm)

let _ = assert (struct_pcms "point" point_fields "x" === opt_pcm #int)

/// Connections for the fields of a point

// //[@@iter_unfold]
// val _x: connection point_pcm (opt_pcm #int)
// let _x =
//   //assert (struct_pcms "point" point_fields "x" === opt_pcm #int);
// assume (connection u#0
//   u#0
//   #point_pcm_carrier
//   #(Pervasives.Native.option u#0 int)
//   point_pcm
//   (opt_pcm u#0 #int)
//   == connection u#0
//   u#0
//   #(struct_pcm_carrier "point" point_fields)
//   #(struct_carriers point_fields "x")
//   (struct_pcm "point" point_fields)
//   (struct_pcms "point" point_fields "x"));
//   struct_field' "point" point_fields "x"
// 
// //[@@iter_unfold]
// val _y: connection point_pcm (opt_pcm #int)
// let _y = struct_field' "point" point_fields "y"
// 
// //[@@iter_unfold]
// [@@__reduce__]
// let x: field_of point_fields = mk_field_of point_fields "x"
// [@@__reduce__]
// let y: field_of point_fields = mk_field_of point_fields "y"
// 
// /// View for points
// 
// [@@__reduce__]
// val point_view: sel_view point_pcm point false
// let point_view = struct_view "point" point_fields
// 
// /// Explode and recombine
// 
// //val explode' (#opened: inames)
// //  (p: ref 'a point_pcm)
// //  (s: Ghost.erased point)
// //: SteelGhostT unit opened
// //    (pts_to_v p point_view s)
// //    (fun _ -> pts_to_fields "point" point_fields p s)

//[@@__reduce__]
//let point_view = struct_view "point" point_fields

val explode' (#opened: inames)
  (p: ref 'a (struct_pcm "point" point_fields))
  (s: Ghost.erased (struct "point" point_fields))
: SteelGhostT unit opened
    (pts_to_v p (struct_view "point" point_fields) s)
    (fun _ -> pts_to_fields "point" point_fields p s)

let explode' p s =
  explode "point" point_fields p s

(*

struct_def = f:(#a:Type -> (map: string&typedef -> a) -> (reduce: a -> a -> b) -> b){
  exists fields. 
}

struct_def_of_fields fields = fun f g -> reduce g (map f fields)

point_struct = normalize_term (struct_def_of_fields f g ["x", c_int; "y", c_int])
===> fun f g -> f ("x", c_int) `g` f ("y", c_int)

pcm_carrier (s: struct_def) = s (fun (_, td) -> td.carrier) (&)

struct_def a = {
  fields: s:a -> typedef; //itrivial typedef for undefined fields
}

struct_view : sel_view (struct_pcm fields) (struct_def (refine string p)) false
p ~~~> p /\ (fun x -> x =!= removed_field)


*)

//[@@__reduce__]
let x: field_of point_fields = "x"
//[@@__reduce__]
let y: field_of point_fields = "y"

//[@@__reduce__]
let point_view = struct_view "point" point_fields

//[@@__reduce__]
let _x = struct_field' "point" point_fields x
//[@@__reduce__]
let _y = struct_field' "point" point_fields y

let aux
  (p: ref 'a (struct_pcm "point" point_fields))
  (s: Ghost.erased (struct "point" point_fields))
: Lemma (pts_to_fields "point" point_fields p s
    == 
      (pts_to_field "point" point_fields p s x `star`
        (pts_to_field "point" point_fields p s y `star`
         emp)))
= ()

let aux1
  (p: ref 'a (struct_pcm "point" point_fields))
  (s: Ghost.erased (struct "point" point_fields))
: Lemma (pts_to_fields "point" point_fields p s
    == 
      (pts_to_v (ref_focus p _x) (struct_views point_fields x) (s `struct_get'` x) `star`
        (pts_to_v (ref_focus p _y) (struct_views point_fields y) (s `struct_get'` y) `star`
         emp)))
= ()
  

// = pts_to_v
//     (ref_focus p (struct_field' tag fields field))
//     (struct_views fields field)
//     (s `struct_get'` field)
// = ()

val explode'' (#opened: inames)
  (p: ref 'a (struct_pcm "point" point_fields))
  (s: Ghost.erased (struct "point" point_fields))
: SteelGhostT unit opened
    (pts_to_v p point_view s)
    (fun _ ->
  pts_to_v
    (ref_focus p _x)
    (struct_views point_fields x)
    (s `struct_get'` x)
    `star`
  pts_to_v
    (ref_focus p _y)
    (struct_views point_fields y)
    (s `struct_get'` y))

let explode'' p s =
  explode "point" point_fields p s;
  change_equal_slprop (pts_to_fields "point" point_fields p s)
  (pts_to_v (ref_focus p _x) (struct_views point_fields x) (s `struct_get'` x) `star`
        (pts_to_v (ref_focus p _y) (struct_views point_fields y) (s `struct_get'` y) `star`
         emp))

(*
(*

struct tag fields : Type

struct_pcm_carrier tag fields : Type
struct_pcm tag fields : pcm (struct_pcm_carrier tag fields)

fields : list (string * typedef)

type struct_fields = {fields: list string; get: string ^-> typedef; get_prf: dom(get) ⊆ fields}

fields : struct_fields

nil : struct_fields
cons : string -> typedef -> struct_fields -> struct_fields

struct_view tag fields excluded
  carrier = struct_pcm tag fields
  view_type = restricted_t (refine string (notin excluded)) (struct_pcm_carriers tag fields)

mk_nil : nil

mk_cons #tag #fields
  (s: string) (t: typedef) (x: t.view_type) (v: struct tag fields)
: struct tag (cons s t fields)

get_field fields s = fields.get s

val addr_of_struct_field 

addr_of_struct_field #tag #point_fields p "x" <--- "x" should be a valid field name
  p : ref base_type (struct_pcm tag fields)
  "x" notin excluded
  excluded : string ^-> bool
  {p `pts_to_view` struct_view tag fields excluded}
  {p `pts_to_view` struct_view tag fields (cons "x" excluded)
   q `pts_to_view` struct_field_view tag fields "x"}

unaddr_of_struct_field p "x"
  p : ref base_type (struct_pcm tag fields)
  "x" in excluded
  excluded : string ^-> bool
  q = ref_focus p ..
  {p `pts_to_view` struct_view tag fields excluded
   q `pts_to_view` struct_field_view tag fields "x"}
  {p `pts_to_view` struct_view tag fields (excluded \ "x")}

sel_view (struct_pcm tag fields) (struct tag (fields \ excluded)) false

val explode'' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    (p `pts_to_view` point_view)
    (fun _ ->
      (ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      h' (ref_focus p _x `pts_to_view` c_int.view) == h (p `pts_to_view` point_view) `struct_get` "x" /\
      h' (ref_focus p _y `pts_to_view` c_int.view) == h (p `pts_to_view` point_view) `struct_get` "y")

let explode'' p = explode "point" point_fields p
*)

(*
val recombine' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    ((ref_focus p _x `pts_to_view` c_int.view) `star`
     (ref_focus p _y `pts_to_view` c_int.view))
    (fun _ -> p `pts_to_view` point_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      h (ref_focus p _x `pts_to_view` c_int.view) == h' (p `pts_to_view` point_view) `struct_get` "x" /\
      h (ref_focus p _y `pts_to_view` c_int.view) == h' (p `pts_to_view` point_view) `struct_get` "y")

let recombine' p = recombine "point" point_fields p
*)

#push-options "--debug PointStructSelectors --debug_level SMTQuery --log_queries --query_stats --fuel 0"
#restart-solver

[@@iter_unfold] let x: field_of point_fields = mk_field_of point_fields "x"
[@@iter_unfold] let y: field_of point_fields = mk_field_of point_fields "y"


module T = FStar.Tactics

let aux (p: ref 'a point_pcm) (h: rmem (p `pts_to_view` point_view))
  (h': rmem
     ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view)))
: Tot (squash (
   (norm norm_list
      (pts_to_fields "point" point_fields p h h' point_fields)
      ==
   norm norm_list (begin
      let pointprop =
      ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view))
      in
      (can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
      h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get'` x) /\
      (can_be_split pointprop (ref_focus p _y `pts_to_view` c_int.view) /\
      h' (ref_focus p _y `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get'` y)
   end))))
= _ by (T.dump ""; T.smt ())

val explode' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    (p `pts_to_view` point_view)
    (fun _ -> pts_to_fields_vprop "point" point_fields p point_fields)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      norm norm_list
        (pts_to_fields "point" point_fields p h h' point_fields))
//(iter_and_fields fields (pts_to_field "point" fields p h h')))

let explode' p = explode "point" point_fields p

val explode'' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "point" point_fields)
    (fun _ -> pts_to_fields_vprop "point" point_fields p point_fields)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      (
      let pointprop =
      (pts_to_fields_vprop "point" point_fields p point_fields)
      in
      (can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
      h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get'` x)))

// let explode'' p = explode "point" point_fields p

assume val recombine (#opened: inames)
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
: SteelGhost unit opened
    (pts_to_fields_vprop tag fields p fields)
    (fun _ -> p `pts_to_view` struct_view tag fields)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      norm norm_list
        (pts_to_fields tag fields p h' h fields))


val explode''' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    (p `pts_to_view` point_view)
    (fun _ -> 
    ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view)))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      norm norm_list
        (pts_to_fields "point" point_fields p h h' point_fields))
//(iter_and_fields fields (pts_to_field "point" fields p h h')))

#push-options "--print_implicits"

unfold let norm' (s: list norm_step) (#a: Type) (x: a) : Tot (norm s a) =
  norm_spec s a;
  norm s x

unfold let norm''  (#a: Type) (x: a) : Tot (norm norm_list a) =
  norm_spec norm_list a;
  norm norm_list x

let aux'
  (p: ref 'a (struct_pcm "point" point_fields))
  (h': rmem (p `pts_to_view` point_view))
  : GTot int
= 
    ((h' (p `pts_to_view` point_view) `struct_get'` x))
    // <: (get_field point_fields x).view_type)) in
//  in let j: int = i in j
//= (norm norm_list (h' (p `pts_to_view` point_view) `struct_get` x) <: (get_field point_fields x).view_type) <: int
// TODO why are two coercions necessary?

//let aux'' (s: (Mktypedef?.view_type (get_field point_fields xc_)): int
//= s <: int

/// Reading a struct field
val struct_get
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields) (field: field_of fields)
: (get_field fields field).view_type

let explode''' p =
  explode "point" point_fields p;
  change_equal_slprop
    (pts_to_fields_vprop "point" point_fields p point_fields)
    ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view))

val zero_x
  (p: ref 'a (struct_pcm "point" point_fields))
: Steel unit
    (p `pts_to_view` point_view)
    (fun _ -> p `pts_to_view` point_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      norm norm_list (h' (p `pts_to_view` point_view) `struct_get` x == (0 <: c_int.view_type)))

let zero_x p =
  explode "point" point_fields p;
  slassert (
     ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view)));
  //recombine "point" point_fields p;
  sladmit(); return()

(*
val explode''' (#opened: inames)
  (p: ref 'a (struct_pcm "point" point_fields))
: SteelGhost unit opened
    (p `pts_to_view` struct_view "point" point_fields)
    (fun _ -> pts_to_fields_vprop "point" point_fields p point_fields)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let pointprop =
      (pts_to_fields_vprop "point" point_fields p point_fields)
      in
      (can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
      h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` x))

let testlemma p
    (h: rmem (p `pts_to_view` struct_view "point" point_fields))
    (h': rmem( pts_to_fields_vprop "point" point_fields p point_fields))
: Lemma
  (requires
  norm norm_list (let pointprop =
  (pts_to_fields_vprop "point" point_fields p point_fields)
  in
  (can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
  h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` x)
  ))
  (ensures
  norm norm_list (let pointprop =
  (pts_to_fields_vprop "point" point_fields p point_fields)
  in
  (can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
  h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` x)
  ))
= ()
*)
(*
let testlemma' (p: ref 'a point_pcm)
    (h: rmem (p `pts_to_view` struct_view "point" point_fields))
    (h': rmem( pts_to_fields_vprop "point" point_fields p point_fields))
: Lemma
  (requires
  norm norm_list (let pointprop =
  (pts_to_fields_vprop "point" point_fields p point_fields)
  in
  (can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
  h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` x)
  ))
  (ensures
  (let pointprop =
  (pts_to_fields_vprop "point" point_fields p point_fields)
  in
  (can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
  h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` x)
  ))
= _ by (T.dump "") // T.norm norm_list; T.dump ""; T.tadmit()); admit()
*)

//let explode''' p = explode'' p

let aux p (h: rmem (p `pts_to_view` point_view))
  (h': rmem
     ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view)))
: Lemma
   (requires
      //norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
      norm norm_list
      (pts_to_fields "point" point_fields p h h' point_fields))
   (ensures begin
      let pointprop =
      ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view))
      in
      can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
      h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` x /\
      can_be_split pointprop (ref_focus p _y `pts_to_view` c_int.view) /\
      h' (ref_focus p _y `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` y
   end)
= ()

/// Now, a contrived struct with twice as many fields (to stress-test)

//[@@__reduce__;iter_unfold]
let quad_fields: struct_fields = [
  "x", c_int;
  "y", c_int;
  "z", c_int;
  "w", c_int;
]
let quad = struct "quad" quad_fields

let quad_pcm_carrier = struct_pcm_carrier "quad" quad_fields
let quad_pcm: pcm quad_pcm_carrier = struct_pcm "quad" quad_fields

/// (mk_quad x y) represents (struct quad){.x = x, .y = y}
/// (mk_quad_pcm x y) same, but where x and y are PCM carrier values

let mk_quad: int -> int -> int -> int -> quad = mk_struct "quad" quad_fields
let mk_quad_pcm: option int -> option int -> option int -> option int -> quad_pcm_carrier = mk_struct_pcm "quad" quad_fields

/// Connections for the fields of a quad

[@@iter_unfold] let _quad_x: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "x"
[@@iter_unfold] let _quad_y: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "y"
[@@iter_unfold] let _quad_z: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "z"
[@@iter_unfold] let _quad_w: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "w"

/// View for quads

[@@iter_unfold] let quad_view: sel_view quad_pcm quad false = struct_view "quad" quad_fields

/// Explode and recombine

(*
val explode_quad' (#opened: inames)
  (p: ref 'a quad_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "quad" quad_fields)
    (fun _ -> iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
        (iter_and_fields quad_fields (pts_to_field "quad" quad_fields p h h')))

let explode_quad' p = explode "quad" quad_fields p
*)

(*
val explode_quad'' (#opened: inames)
  (p: ref 'a quad_pcm)
: SteelGhost unit opened
    (p `pts_to_view` quad_view)
    (fun _ ->
      (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
        (ref_focus p _quad_w `pts_to_view` c_int.view))))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quadprop =
        (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
          (ref_focus p _quad_w `pts_to_view` c_int.view)))
      in
      can_be_split quadprop (ref_focus p _quad_x `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_x `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "x" /\
      can_be_split quadprop (ref_focus p _quad_y `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_y `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "y" /\
      can_be_split quadprop (ref_focus p _quad_z `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_z `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "z" /\
      can_be_split quadprop (ref_focus p _quad_w `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_w `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "w")
*)

#push-options "--z3rlimit 30 --query_stats"

#pop-options
#push-options "--fuel 2 --query_stats"

[@@iter_unfold] let x: field_of quad_fields = mk_field_of quad_fields "x"
[@@iter_unfold] let y: field_of quad_fields = mk_field_of quad_fields "y"
[@@iter_unfold] let z: field_of quad_fields = mk_field_of quad_fields "z"
[@@iter_unfold] let w: field_of quad_fields = mk_field_of quad_fields "w"

module T = FStar.Tactics

let norm_list = [
  delta_attr [`%iter_unfold];
  delta_only [
    `%map; `%mem; `%fst; `%Mktuple2?._1;
    `%assoc;
    `%Some?.v
  ];
  iota; primops; zeta
]

let quad_aux (p: ref 'a quad_pcm) (h: rmem (p `pts_to_view` quad_view))
  (h': rmem
     ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
        (ref_focus p _quad_w `pts_to_view` c_int.view)))))
: squash
   ((
      norm norm_list//[delta_attr [`%iter_unfold]; iota; primops; zeta]
        (pts_to_fields "quad" quad_fields p h h' quad_fields))
   ==
   (begin
      let quadprop =
        (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
          (ref_focus p _quad_w `pts_to_view` c_int.view)))
      in
      (can_be_split quadprop (ref_focus p _quad_x `pts_to_view` c_int.view) /\
       h' (ref_focus p _quad_x `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` x) /\
      ((can_be_split quadprop (ref_focus p _quad_y `pts_to_view` c_int.view) /\
       h' (ref_focus p _quad_y `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` y) /\
       ((can_be_split quadprop (ref_focus p _quad_z `pts_to_view` c_int.view) /\
         h' (ref_focus p _quad_z `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` z) /\
         (can_be_split quadprop (ref_focus p _quad_w `pts_to_view` c_int.view) /\
          h' (ref_focus p _quad_w `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` w)))
   end))
= _ by (T.trefl ())
// assert_norm produces a stack overflow?
//_ by (
//    T.norm norm_list;
//    T.trefl ())

let quad_aux2 (p: ref 'a quad_pcm) (h: rmem (p `pts_to_view` quad_view))
  (h': rmem
     ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
        (ref_focus p _quad_w `pts_to_view` c_int.view)))))
: squash
   ((
      norm norm_list//[delta_attr [`%iter_unfold]; iota; primops; zeta]
        (pts_to_fields "quad" quad_fields p h h' quad_fields))
   <==>
   norm norm_list (begin
      let quadprop =
        (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
          (ref_focus p _quad_w `pts_to_view` c_int.view)))
      in
      (can_be_split quadprop (ref_focus p _quad_x `pts_to_view` c_int.view) /\
       h' (ref_focus p _quad_x `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` x) /\
      ((can_be_split quadprop (ref_focus p _quad_y `pts_to_view` c_int.view) /\
       h' (ref_focus p _quad_y `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` y) /\
       ((can_be_split quadprop (ref_focus p _quad_z `pts_to_view` c_int.view) /\
         h' (ref_focus p _quad_z `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` z) /\
         (can_be_split quadprop (ref_focus p _quad_w `pts_to_view` c_int.view) /\
          h' (ref_focus p _quad_w `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` w)))
   end))
= () // _ by (T.trefl ())

(*
let quad_unfold_iter_star_fields p
: Lemma
    (norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
    (iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p)) ==
     (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
        (ref_focus p _quad_w `pts_to_view` c_int.view))))
= ()
*)

#push-options "--query_stats"

let explode_quad'' p =
  explode "quad" quad_fields p;
  //quad_unfold_iter_star_fields p;
  //change_equal_slprop
  //  (iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p))
  //  ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
  //   ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
  //    ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
  //     (ref_focus p _quad_w `pts_to_view` c_int.view))));
  ()

(*
val recombine_quad' (#opened: inames)
  (p: ref 'a quad_pcm)
: SteelGhost unit opened
    ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
       (ref_focus p _quad_w `pts_to_view` c_int.view))))
    (fun _ -> p `pts_to_view` quad_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quadprop =
        (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
          (ref_focus p _quad_w `pts_to_view` c_int.view)))
      in
      // assert (can_be_split' quadprop (ref_focus p _quad_x `pts_to_view` c_int.view));
      // assert (can_be_split' quadprop (ref_focus p _quad_y `pts_to_view` c_int.view));
      // assert (can_be_split' quadprop (ref_focus p _quad_z `pts_to_view` c_int.view));
      // assert (can_be_split' quadprop (ref_focus p _quad_w `pts_to_view` c_int.view));
      h (ref_focus p _quad_x `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "x" /\
      h (ref_focus p _quad_y `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "y" /\
      h (ref_focus p _quad_z `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "z" /\
      h (ref_focus p _quad_w `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "w")

let recombine_quad' p =
  quad_unfold_iter_star_fields p;
  change_equal_slprop
    ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
       (ref_focus p _quad_w `pts_to_view` c_int.view))))
    (iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p));
  recombine "quad" quad_fields p
*)

/// 5 fields!

//[@@__reduce__;iter_unfold]
let quint_fields: struct_fields = [
  "x", c_int;
  "y", c_int;
  "z", c_int;
  "w", c_int;
  "v", c_int;
]
let quint = struct "quint" quint_fields

let quint_pcm_carrier = struct_pcm_carrier "quint" quint_fields
let quint_pcm: pcm quint_pcm_carrier = struct_pcm "quint" quint_fields

let mk_quint: int -> int -> int -> int -> int -> quint = mk_struct "quint" quint_fields
let mk_quint_pcm: option int -> option int -> option int -> option int -> option int -> quint_pcm_carrier = mk_struct_pcm "quint" quint_fields

/// Connections for the fields of a quint

let _quint_x: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "x"
let _quint_y: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "y"
let _quint_z: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "z"
let _quint_w: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "w"
let _quint_v: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "v"

/// View for quints

let quint_view: sel_view quint_pcm quint false = struct_view "quint" quint_fields

/// Explode and recombine

(*
val explode_quint' (#opened: inames)
  (p: ref 'a quint_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "quint" quint_fields)
    (fun _ -> iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p))
    (requires fun _ -> True)
    (ensures fun h _ h' -> iter_and_fields quint_fields (pts_to_field "quint" quint_fields p h h'))

let explode_quint' p = explode "quint" quint_fields p
*)

#restart-solver

val explode_quint'' (#opened: inames)
  (p: ref 'a quint_pcm)
: SteelGhost unit opened
    (p `pts_to_view` quint_view)
    (fun _ ->
      (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
         (ref_focus p _quint_v `pts_to_view` c_int.view)))))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quintprop =
        (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
          ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
           (ref_focus p _quint_v `pts_to_view` c_int.view))))
      in
      can_be_split quintprop (ref_focus p _quint_x `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_x `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "x" /\
      can_be_split quintprop (ref_focus p _quint_y `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_y `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "y" /\
      can_be_split quintprop (ref_focus p _quint_z `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_z `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "z" /\
      can_be_split quintprop (ref_focus p _quint_w `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_w `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "w" /\
      can_be_split quintprop (ref_focus p _quint_v `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_v `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "v")

let aux p (h: rmem (p `pts_to_view` quint_view))
  (h': rmem
     ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
         (ref_focus p _quint_v `pts_to_view` c_int.view))))))
: Lemma
   (requires
      norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
      (pts_to_fields "quint" quint_fields p h h' quint_fields))
   (ensures begin
      let quintprop =
        (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
          ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
           (ref_focus p _quint_v `pts_to_view` c_int.view))))
      in
      can_be_split quintprop (ref_focus p _quint_x `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_x `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "x" /\
      can_be_split quintprop (ref_focus p _quint_y `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_y `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "y" /\
      can_be_split quintprop (ref_focus p _quint_z `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_z `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "z" /\
      can_be_split quintprop (ref_focus p _quint_w `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_w `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "w" /\
      can_be_split quintprop (ref_focus p _quint_v `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_v `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "v"
   end)
= admit()

(*
let quint_unfold_iter_star_fields p
: Lemma
    (iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p) ==
     (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
         (ref_focus p _quint_v `pts_to_view` c_int.view)))))
= ()
*)

#restart-solver

//#push-options "--z3rlimit 30"

let explode_quint'' p =
  explode "quint" quint_fields p;
  //quint_unfold_iter_star_fields p;
  //change_equal_slprop
  //  (iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p))
  //  ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
  //   ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
  //    ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
  //     ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
  //      (ref_focus p _quint_v `pts_to_view` c_int.view)))));
  ()

//#pop-options

val recombine_quint' (#opened: inames)
  (p: ref 'a quint_pcm)
: SteelGhost unit opened
    ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
        (ref_focus p _quint_v `pts_to_view` c_int.view)))))
    (fun _ -> p `pts_to_view` quint_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quintprop =
        ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
         ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
          ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
           ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
            (ref_focus p _quint_v `pts_to_view` c_int.view)))))
      in
      assert (can_be_split' quintprop (ref_focus p _quint_x `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_y `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_z `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_w `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_v `pts_to_view` c_int.view));
      h (ref_focus p _quint_x `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "x" /\
      h (ref_focus p _quint_y `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "y" /\
      h (ref_focus p _quint_z `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "z" /\
      h (ref_focus p _quint_w `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "w" /\
      h (ref_focus p _quint_v `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "v")

#push-options "--z3rlimit 20"

let recombine_quint' p =
  quint_unfold_iter_star_fields p;
  change_equal_slprop
    ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
        (ref_focus p _quint_v `pts_to_view` c_int.view)))))
    (iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p));
  recombine "quint" quint_fields p

#pop-options

/// 8 fields:

let oct_fields: struct_fields = [
  "x", c_int;
  "y", c_int;
  "z", c_int;
  "w", c_int;
  "v", c_int;
  "u", c_int;
  "t", c_int;
  "s", c_int;
]
let oct = struct "oct" oct_fields

let oct_pcm_carrier = struct_pcm_carrier "oct" oct_fields
let oct_pcm: pcm oct_pcm_carrier = struct_pcm "oct" oct_fields

let mk_oct: int -> int -> int -> int -> int -> int -> int -> int -> oct = mk_struct "oct" oct_fields
let mk_oct_pcm: option int -> option int -> option int -> option int -> option int -> option int -> option int -> option int -> oct_pcm_carrier = mk_struct_pcm "oct" oct_fields

/// Connections for the fields of a oct

let _oct_x: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "x"
let _oct_y: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "y"
let _oct_z: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "z"
let _oct_w: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "w"
let _oct_v: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "v"
let _oct_u: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "u"
let _oct_t: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "t"
let _oct_s: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "s"

/// View for octs

let oct_view: sel_view oct_pcm oct false = struct_view "oct" oct_fields

/// Explode and recombine

val explode_oct' (#opened: inames)
  (p: ref 'a oct_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "oct" oct_fields)
    (fun _ -> iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p))
    (requires fun _ -> True)
    (ensures fun h _ h' -> iter_and_fields oct_fields (pts_to_field "oct" oct_fields p h h'))

let explode_oct' p = explode "oct" oct_fields p

val explode_oct'' (#opened: inames)
  (p: ref 'a oct_pcm)
: SteelGhost unit opened
    (p `pts_to_view` oct_view)
    (fun _ ->
      ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
            ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
             (ref_focus p _oct_s `pts_to_view` c_int.view)))))))))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      True)
      // let octprop =
      //   ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      //    ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
      //     ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
      //      ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
      //       ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
      //        ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
      //         ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
      //          (ref_focus p _oct_s `pts_to_view` c_int.view))))))))
      // in
      // assert (can_be_split' octprop (ref_focus p _oct_x `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_y `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_z `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_w `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_v `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_u `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_t `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_s `pts_to_view` c_int.view));
      // h' (ref_focus p _oct_x `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "x" /\
      // h' (ref_focus p _oct_y `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "y" /\
      // h' (ref_focus p _oct_z `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "z" /\
      // h' (ref_focus p _oct_w `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "w" /\
      // h' (ref_focus p _oct_v `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "v" /\
      // h' (ref_focus p _oct_u `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "u" /\
      // h' (ref_focus p _oct_t `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "t" /\
      // h' (ref_focus p _oct_s `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "s")

let oct_unfold_iter_star_fields p
: Lemma
    (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p) ==
     ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view)))))))))
= assert_norm (
    iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p) ==
     ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view)))))))))

#restart-solver
#push-options "--z3rlimit 40 --query_stats"

let explode_oct'' p =
  explode "oct" oct_fields p;
  // OOMs
  //change_slprop_rel
  //  (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p))
  //  ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
  //    ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
  //     ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
  //      ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
  //       ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
  //        ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
  //         ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
  //          (ref_focus p _oct_s `pts_to_view` c_int.view))))))))
  //  (fun _ _ -> True)
  //  (fun m ->
  //    assert_norm
  //      (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p) ==
  //      ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
  //        ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
  //         ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
  //          ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
  //           ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
  //            ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
  //             ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
  //              (ref_focus p _oct_s `pts_to_view` c_int.view))))))))));
  oct_unfold_iter_star_fields p;
  change_equal_slprop
    (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p))
    ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view))))))));
  ()

#pop-options

val recombine_oct' (#opened: inames)
  (p: ref 'a oct_pcm)
: SteelGhost unit opened
    ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
        (ref_focus p _oct_v `pts_to_view` c_int.view)))))
    (fun _ -> p `pts_to_view` oct_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let octprop =
        ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_v `pts_to_view` c_int.view)))))
      in
      assert (can_be_split' octprop (ref_focus p _oct_x `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_y `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_z `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_w `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_v `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_u `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_t `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_s `pts_to_view` c_int.view));
      h (ref_focus p _oct_x `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "x" /\
      h (ref_focus p _oct_y `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "y" /\
      h (ref_focus p _oct_z `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "z" /\
      h (ref_focus p _oct_w `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "w" /\
      h (ref_focus p _oct_v `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "v" /\
      h (ref_focus p _oct_u `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "u" /\
      h (ref_focus p _oct_t `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "t" /\
      h (ref_focus p _oct_s `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "s")

#restart-solver
#push-options "--z3rlimit 20"

let recombine_oct' p =
  oct_unfold_iter_star_fields p;
  change_equal_slprop
    ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view))))))))
    (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p));
  recombine "oct" oct_fields p

#pop-options
*)
