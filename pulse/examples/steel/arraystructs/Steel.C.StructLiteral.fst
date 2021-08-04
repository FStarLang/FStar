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
open Steel.C.Opt
open FStar.List.Tot
open FStar.FunctionalExtensionality

let has_elements (#a:eqtype) (f: a ^-> bool) (xs: list a): prop =
  forall x. f x == x `mem` xs

// Finite sets
let set (a:eqtype) = f:(a ^-> bool){exists xs. f `has_elements` xs}

let set_as_list (s: set 'a): GTot (list 'a) =
  FStar.IndefiniteDescription.indefinite_description_ghost (list 'a)
    (has_elements s)

let intro_set (#a:eqtype) (f: a ^-> bool) (xs: Ghost.erased (list a))
: Pure (set a)
    (requires f `has_elements` xs)
    (ensures fun _ -> True)
= Classical.exists_intro (fun xs -> f `has_elements` xs) xs;
  f 

let emptyset #a: set a = intro_set (on_dom a (fun _ -> false)) []

let insert x (s: set 'a): set 'a =
  intro_set (on_dom _ (fun x' -> x = x' || s x')) (x :: set_as_list s)

let set_remove (#a:eqtype) x (s: a ^-> bool): (a ^-> bool) =
  on_dom _ (fun x' -> not (x = x') && s x')

let rec list_remove (#a:eqtype) x (xs: list a) = match xs with
  | [] -> []
  | x' :: xs ->
    if x = x' then list_remove x xs
    else x' :: list_remove x xs

let rec list_remove_spec (#a:eqtype) f x (xs: list a)
: Lemma
    (requires f `has_elements` xs)
    (ensures set_remove x f `has_elements` list_remove x xs)
    (decreases xs)
= match xs with
  | [] -> ()
  | x' :: xs ->
    let g: (a ^-> bool) = on_dom _ (fun x -> x `mem` xs) in
    let f': (a ^-> bool) = on_dom _ (fun x'' -> x'' = x' || g x'') in
    assert (f `feq` f');
    assert (g `has_elements` xs);
    list_remove_spec g x xs;
    assert (set_remove x g `has_elements` list_remove x xs)

let remove x (s: set 'a): set 'a =
  list_remove_spec s x (set_as_list s);
  intro_set (set_remove x s) (list_remove x (set_as_list s))

let notin (s: set 'a) (x: 'a): prop = s x == false

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

noeq type struct_fields = {
  //cfields: clist string;
  cfields: list string;
  has_field: set string;
  //has_field_prf: squash (forall field. has_field field == field `mem` cfields);
  get_field: string ^-> typedef;
  // get_field_prf: forall field. has_field field == false ==> get_field field == trivial_typedef;
}

let trivial_typedef: typedef = {
  carrier = option unit;
  pcm = opt_pcm #unit;
  view_type = unit;
  view = opt_view unit;
}

let fields_nil: struct_fields = {
  cfields = [];
  has_field = emptyset;
  //has_field_prf = ();
  get_field = on_dom _ (fun _ -> trivial_typedef);
}

let fields_cons (field: string) (td: typedef) (fields: struct_fields): struct_fields = {
  cfields = field :: fields.cfields;
  has_field = insert field fields.has_field;
  //has_field_prf = ();
  get_field = on_dom _ (fun field' -> if field = field' then td else fields.get_field field');
}

val struct' (tag: string) (fields: struct_fields) (excluded: set string): Type0

let struct_dom (excluded: set string) = refine string (notin excluded)

let struct_cod (fields: struct_fields) (excluded: set string) (field: struct_dom excluded) =
  (fields.get_field field).view_type

let struct' tag fields excluded =
  restricted_t (struct_dom excluded) (struct_cod fields excluded)

let struct (tag: string) (fields: struct_fields) = struct' tag fields emptyset

val mk_nil (tag: string): struct tag fields_nil

let mk_nil tag = on_dom _ (fun _ -> ())

val mk_cons (tag: string) (fields: struct_fields)
  (field: string) (td: typedef) (x: td.view_type) (v: struct tag fields)
: Pure (struct tag (fields_cons field td fields))
    (requires fields.has_field field == false)
    (ensures fun _ -> True)

let mk_cons tag fields field td x v =
  on_dom (refine string (notin emptyset)) (fun field' ->
    if field = field' then x
    else v field' <: ((fields_cons field td fields).get_field field').view_type)

val struct_pcm_carrier (tag: string) (fields: struct_fields): Type0

let struct_pcm_carrier_cod (fields: struct_fields) (field: string) =
  (fields.get_field field).carrier

let struct_pcm_carrier tag fields =
  restricted_t string (struct_pcm_carrier_cod fields)

val struct_pcm (tag: string) (fields: struct_fields): pcm (struct_pcm_carrier tag fields)

let struct_pcms (fields: struct_fields) (field: string)
: pcm (struct_pcm_carrier_cod fields field)
= (fields.get_field field).pcm

let struct_pcm tag fields = prod_pcm (struct_pcms fields)

(* public *) let field_of (fields: struct_fields) = field:string{fields.has_field field == true}

/// Reading a struct field
val struct_get
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields) (field: field_of fields)
: (fields.get_field field).view_type

/// Writing a struct field
val struct_put
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v: (fields.get_field field).view_type)
: struct tag fields

let struct_get x field = x field
let struct_put x field v = on_dom _ (fun field' -> if field = field' then v else x field')

/// For a fixed field name, struct_get and struct_put form a lens

val struct_get_put 
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v: (fields.get_field field).view_type)
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
  (v w: (fields.get_field field).view_type)
: Lemma (struct_put (struct_put x field v) field w == struct_put x field w)
  [SMTPat (struct_put (struct_put x field v) field w)]

/// struct_get/struct_put pairs for different fields don't interfere with each other

val struct_get_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (fields.get_field field1).view_type)
: Lemma
    (requires field1 =!= field2)
    (ensures struct_put x field1 v `struct_get` field2 == x `struct_get` field2)
  [SMTPat (struct_put x field1 v `struct_get` field2)]
  
val struct_put_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field1: field_of fields)
  (v: (fields.get_field field1).view_type)
  (field2: field_of fields)
  (w: (fields.get_field field2).view_type)
: Lemma
    (requires field1 =!= field2)
    (ensures
      struct_put (struct_put x field1 v) field2 w ==
      struct_put (struct_put x field2 w) field1 v)
      
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

(* public *)
let struct_pcm_one (tag: string) (fields: struct_fields)
: struct_pcm_carrier tag fields
= one (struct_pcm tag fields)

/// Reading a pcm_struct_carrier field
val struct_pcm_get
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields) (field: field_of fields)
: (fields.get_field field).carrier

/// Writing a struct_pcm_carrier field
val struct_pcm_put
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (fields.get_field field).carrier)
: struct_pcm_carrier tag fields

let struct_pcm_get x field = x field
let struct_pcm_put x field v = on_dom _ (fun field' -> if field = field' then v else x field')

/// For a fixed field name, struct_pcm_get and struct_pcm_put form a lens

val struct_pcm_get_put 
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (fields.get_field field).carrier)
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
  (v w: (fields.get_field field).carrier)
: Lemma (struct_pcm_put (struct_pcm_put x field v) field w == struct_pcm_put x field w)
  [SMTPat (struct_pcm_put (struct_pcm_put x field v) field w)]
  
/// struct_pcm_get/struct_pcm_put pairs for different fields don't interfere with each other

val struct_pcm_get_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (fields.get_field field1).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures struct_pcm_put x field1 v `struct_pcm_get` field2 == x `struct_pcm_get` field2)
  [SMTPat (struct_pcm_put x field1 v `struct_pcm_get` field2)]
  
val struct_pcm_put_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (v: (fields.get_field field1).carrier)
  (field2: field_of fields)
  (w: (fields.get_field field2).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures
      struct_pcm_put (struct_pcm_put x field1 v) field2 w ==
      struct_pcm_put (struct_pcm_put x field2 w) field1 v)

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

val struct_view (tag: string) (fields: struct_fields) (excluded: set string)
: sel_view (struct_pcm tag fields) (struct' tag fields excluded) false

let struct_view_to_view_prop (tag: string) (fields: struct_fields) (excluded: set string)
: struct_pcm_carrier tag fields -> prop
= fun x -> forall (field: struct_dom excluded).
  (fields.get_field field).view.to_view_prop (x field) /\
  (fields.has_field field == false ==> x field =!= one (fields.get_field field).pcm)

let struct_view_to_view (tag: string) (fields: struct_fields) (excluded: set string)
: refine (struct_pcm_carrier tag fields) (struct_view_to_view_prop tag fields excluded) -> 
  struct' tag fields excluded
= fun x -> on_dom (struct_dom excluded) (fun field -> (fields.get_field field).view.to_view (x field))

let struct_view_to_carrier (tag: string) (fields: struct_fields) (excluded: set string)
: struct' tag fields excluded ->
  refine (struct_pcm_carrier tag fields) (struct_view_to_view_prop tag fields excluded)
= fun x ->
  let y: struct_pcm_carrier tag fields =
    on_dom _ (fun field ->
      if excluded field then one (fields.get_field field).pcm else
      (fields.get_field field).view.to_carrier (x field)
      <: (fields.get_field field).carrier)
  in y

module S = FStar.String

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

let arbitrary_unexcluded (excluded: set string): GTot (struct_dom excluded) =
  arbitrary_unexcluded_witness (set_as_list excluded)

let struct_view_to_carrier_not_one (tag: string) (fields: struct_fields) (excluded: set string)
: Lemma 
    (~ (exists x. struct_view_to_carrier tag fields excluded x == one (struct_pcm tag fields)) /\
     ~ (struct_view_to_view_prop tag fields excluded (one (struct_pcm tag fields))))
= (fields.get_field (arbitrary_unexcluded excluded)).view.to_carrier_not_one

let struct_view_to_view_frame (tag: string) (fields: struct_fields) (excluded: set string)
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
  let aux (k:struct_dom excluded)
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

val struct_field
  (tag: string) (fields: struct_fields) (field: field_of fields)
: connection (struct_pcm tag fields) (struct_pcms fields field)

let struct_field tag fields field = struct_field (struct_pcms fields) field

let struct'_without_field
  (tag: string) (fields: struct_fields) (excluded: set string) (field: string)
  (v: struct' tag fields excluded)
: struct' tag fields (insert field excluded)
= on_dom (struct_dom (insert field excluded)) v

let struct_without_field_to_carrier
  (tag: string) (fields: struct_fields) (excluded: set string) (field: string)
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
  (tag: string) (fields: struct_fields) (excluded: set string)
  (field: field_of fields)
  (v: struct' tag fields excluded)
: Pure (struct' tag fields (insert field excluded) & (fields.get_field field).view_type)
    (requires not (excluded field))
    (ensures fun _ -> True)
= (struct'_without_field tag fields excluded field v, v field)

val addr_of_struct_field
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
: Steel (ref 'a (struct_pcms fields field))
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (q `pts_to_view` (fields.get_field field).view))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == ref_focus p (struct_field tag fields field) /\
      extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded))
       ==
        (h' (p `pts_to_view` struct_view tag fields (insert field excluded)),
         h' (q `pts_to_view` (fields.get_field field).view)))

#push-options "--z3rlimit 30"
let addr_of_struct_field #a #tag #fields #excluded field p =
  let v: Ghost.erased (struct' tag fields excluded) =
    gget (p `pts_to_view` struct_view tag fields excluded)
  in
  let s: Ghost.erased (struct_pcm_carrier tag fields) =
    pts_to_view_elim p (struct_view tag fields excluded)
  in
  //assert (Ghost.reveal s == (struct_view tag fields excluded).to_carrier v);
  //slassert (p `pts_to` s);
  let q = addr_of_struct_field p field s in
  assert (q == ref_focus p (struct_field tag fields field));
  //slassert (
  //  (p `pts_to` struct_without_field (struct_pcms fields) field s) `star`
  //  (q `pts_to` Ghost.reveal s field));
  struct_without_field_to_carrier tag fields excluded field s v;
  pts_to_view_intro p (struct_without_field (struct_pcms fields) field s)
    (struct_view tag fields (insert field excluded))
    (struct'_without_field tag fields excluded field v);
  pts_to_view_intro q (Ghost.reveal s field)
    (fields.get_field field).view
    (Ghost.reveal v field);
  return q
#pop-options

let insert_remove x (s: set 'a)
: Lemma (requires s x == true) (ensures insert x (remove x s) == s)
  [SMTPat (insert x (remove x s))]
= assert (insert x (remove x s) `feq` s)

// let remove_insert x (s: set 'a)
// : Lemma (remove x (insert x s) == remove x s)
// = assert (remove x (insert x s) `feq` remove x s)

val unaddr_of_struct_field
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
  (q: ref 'a (struct_pcms fields field))
: Steel unit
    ((p `pts_to_view` struct_view tag fields excluded) `star`
     (q `pts_to_view` (fields.get_field field).view))
    (fun _ -> p `pts_to_view` struct_view tag fields (remove field excluded))
    (requires fun _ ->
      excluded field == true /\
      q == ref_focus p (struct_field tag fields field))
    (ensures fun h _ h' -> 
      excluded field == true /\
      extract_field tag fields (remove field excluded) field
        (h' (p `pts_to_view` struct_view tag fields (remove field excluded)))
       ==
        (h (p `pts_to_view` struct_view tag fields excluded),
         h (q `pts_to_view` (fields.get_field field).view)))

let struct'_with_field
  (tag: string) (fields: struct_fields) (excluded: set string)
  (field: string) (w: (fields.get_field field).view_type)
  (v: struct' tag fields excluded)
: Pure (struct' tag fields (remove field excluded))
    (requires excluded field == true)
    (ensures fun _ -> True)
= on_dom (struct_dom (remove field excluded))
    (fun field' -> if field = field' then w else v field')

let struct_with_field_to_carrier
  (tag: string) (fields: struct_fields) (excluded: set string) (field: string)
  (s: struct_pcm_carrier tag fields)
  (t: (fields.get_field field).carrier)
  (v: struct' tag fields excluded)
  (w: (fields.get_field field).view_type)
: Lemma
    (requires
      excluded field == true /\
      s == (struct_view tag fields excluded).to_carrier v /\
      t === (fields.get_field field).view.to_carrier w)
    (ensures
      struct_with_field (struct_pcms fields) field t s
      == (struct_view tag fields (remove field excluded)).to_carrier
           (struct'_with_field tag fields excluded field w v))
= assert
    (struct_with_field (struct_pcms fields) field t s
      `feq` (struct_view tag fields (remove field excluded)).to_carrier
           (struct'_with_field tag fields excluded field w v))

let struct_with_field_to_carrier'
  (tag: string) (fields: struct_fields) (excluded: set string) (field: string)
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
  (tag: string) (fields: struct_fields) (excluded: set string)
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

let unaddr_of_struct_field #a #tag #fields #excluded field p q =
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
  //slassert ((p `pts_to` s) `star` (q `pts_to` t));
  //assert (Ghost.reveal s field == one (struct_pcms fields field));
  //assert (q == ref_focus p (Struct.struct_field (struct_pcms fields) field));
  unaddr_of_struct_field #_ #_ #_ #(struct_pcms fields) field q p s t;
  let h1: squash (excluded field == true) = () in
  let h2: squash (Ghost.reveal s == (struct_view tag fields excluded).to_carrier v) = () in
  let h3: squash (Ghost.reveal t == (fields.get_field field).view.to_carrier w) = () in
  struct_with_field_to_carrier' tag fields excluded field
    (Ghost.reveal s) (Ghost.reveal t) (Ghost.reveal v) (Ghost.reveal w)
    h1 h2 h3; // TODO why need pass explicitly
  assert (struct_with_field (struct_pcms fields) field t s
      == (struct_view tag fields (remove field excluded)).to_carrier
           (struct'_with_field tag fields excluded field w v));
  pts_to_view_intro p
    (struct_with_field (struct_pcms fields) field t s)
    (struct_view tag fields (remove field excluded))
    (struct'_with_field tag fields excluded field w v);
  extract_field_with_field tag fields excluded field (Ghost.reveal v) (Ghost.reveal w);
  assert
     (extract_field tag fields (remove field excluded) field
         (struct'_with_field tag fields excluded field w v)
         == (Ghost.reveal v, Ghost.reveal w));
  return ()
  
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
: (fields.get_field field).view_type

(*
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

*)
