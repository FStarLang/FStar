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

open FStar.List.Tot
open FStar.FunctionalExtensionality

open FStar.FSet

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

//[@@__reduce__]
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

//[@@__reduce__]
let fields_nil: struct_fields = {
  cfields = [];
  has_field = emptyset;
  //has_field_prf = ();
  get_field = on_dom _ (fun _ -> trivial_typedef);
}

//[@@__reduce__]
let fields_cons (field: string) (td: typedef) (fields: struct_fields): struct_fields = {
  cfields = field :: fields.cfields;
  has_field = insert field fields.has_field;
  //has_field_prf = ();
  get_field = on_dom _ (fun field' -> if field = field' then td else fields.get_field field');
}

val struct' (tag: string) (fields: struct_fields) (excluded: set string): Type0

let struct (tag: string) (fields: struct_fields) = struct' tag fields emptyset

val mk_nil (tag: string): struct tag fields_nil

val mk_cons (tag: string) (fields: struct_fields)
  (field: string) (td: typedef) (x: td.view_type) (v: struct tag fields)
: Pure (struct tag (fields_cons field td fields))
    (requires fields.has_field field == false)
    (ensures fun _ -> True)

val struct_pcm_carrier (tag: string) (fields: struct_fields): Type0

val struct_pcm (tag: string) (fields: struct_fields): pcm (struct_pcm_carrier tag fields)

let field_of (fields: struct_fields) = field:string{fields.has_field field == true}

/// Reading a struct field
val struct_get
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (x: struct' tag fields excluded) (field: field_of fields)
: Pure (fields.get_field field).view_type
    (requires excluded field == false)
    (ensures fun _ -> True)

/// Writing a struct field
val struct_put
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (x: struct' tag fields excluded)
  (field: field_of fields)
  (v: (fields.get_field field).view_type)
: Pure (struct' tag fields excluded)
    (requires excluded field == false)
    (ensures fun _ -> True)

/// For a fixed field name, struct_get and struct_put form a lens

val struct_get_put 
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (x: struct' tag fields excluded)
  (field: field_of fields)
  (v: (fields.get_field field).view_type)
: Lemma
    (requires excluded field == false)
    (ensures struct_put x field v `struct_get` field == v)
  [SMTPat (struct_put x field v `struct_get` field)]

val struct_put_get
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (x: struct' tag fields excluded)
  (field: field_of fields)
: Lemma
    (requires excluded field == false)
    (ensures struct_put x field (x `struct_get` field) == x)
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
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (x: struct' tag fields excluded)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (fields.get_field field1).view_type)
: Lemma
    (requires field1 =!= field2 /\ excluded field1 == false /\ excluded field2 == false)
    (ensures struct_put x field1 v `struct_get` field2 == x `struct_get` field2)
  [SMTPat (struct_put x field1 v `struct_get` field2)]
  
val struct_put_put_ne
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (x: struct' tag fields excluded)
  (field1: field_of fields)
  (v: (fields.get_field field1).view_type)
  (field2: field_of fields)
  (w: (fields.get_field field2).view_type)
: Lemma
    (requires field1 =!= field2 /\ excluded field1 == false /\ excluded field2 == false)
    (ensures
      struct_put (struct_put x field1 v) field2 w ==
      struct_put (struct_put x field2 w) field1 v)

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

val struct_view (tag: string) (fields: struct_fields) (excluded: set string)
: sel_view (struct_pcm tag fields) (struct' tag fields excluded) false

val struct_field
  (tag: string) (fields: struct_fields) (field: field_of fields)
: connection (struct_pcm tag fields) (fields.get_field field).pcm

val extract_field
  (tag: string) (fields: struct_fields) (excluded: set string)
  (field: field_of fields)
  (v: struct' tag fields excluded)
: Pure (struct' tag fields (insert field excluded) & (fields.get_field field).view_type)
    (requires not (excluded field))
    (ensures fun _ -> True)
    
val extract_field_extracted
  (tag: string) (fields: struct_fields) (excluded: set string)
  (field: field_of fields)
  (v: struct' tag fields excluded)
: Lemma
    (requires not (excluded field))
    (ensures snd (extract_field tag fields excluded field v) == v `struct_get` field)
    [SMTPat (extract_field tag fields excluded field v)]

val extract_field_unextracted
  (tag: string) (fields: struct_fields) (excluded: set string)
  (field: field_of fields)
  (field': field_of fields)
  (v: struct' tag fields excluded)
: Lemma
    (requires not (excluded field) /\ not (excluded field') /\ (field =!= field'))
    (ensures 
      fst (extract_field tag fields excluded field v) `struct_get` field'
      == v `struct_get` field')
    [SMTPat (extract_field tag fields excluded field v);
     SMTPat (has_type field' string)]

irreducible let c_struct = 0

irreducible let c_typedef = 0

unfold let unfold_typedefs = [delta_attr [`%c_typedef]]

unfold let simplify_typedefs =
  [delta_attr [`%c_struct];
   delta_only
    [`%fields_cons;
     `%fields_nil;
     `%Mkstruct_fields?.get_field;
     `%Mktypedef?.carrier;
     `%Mktypedef?.pcm;
     `%Mktypedef?.view_type;
     `%Mktypedef?.view];
   iota; zeta; primops]

val addr_of_struct_field_ref
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
: Steel (ref 'a (fields.get_field field).pcm)
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #false
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == ref_focus p (struct_field tag fields field) /\
      extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded))
       ==
        (h' (p `pts_to_view` struct_view tag fields (insert field excluded)),
         h' (q `pts_to_view` (fields.get_field field).view)))

val unaddr_of_struct_field_ref'
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
  (q: ref 'a (fields.get_field field).pcm)
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

val unaddr_of_struct_field_ref
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
  (q: ref 'a (fields.get_field field).pcm)
: Steel unit
    ((p `pts_to_view` struct_view tag fields excluded) `star`
     (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #false
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
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

open Steel.C.Reference

let addr_of_struct_field
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (field: field_of fields)
  (p: ref 'a (struct tag fields) (struct_pcm tag fields))
: Steel (ref 'a
          (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
          (fields.get_field field).pcm)
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == ref_focus p (struct_field tag fields field) /\
      extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded))
       ==
        (h' (p `pts_to_view` struct_view tag fields (insert field excluded)),
         h' (q `pts_to_view` (fields.get_field field).view)))
=         
//let addr_of_struct_field #a #tag #fields #excluded field p =
  addr_of_struct_field_ref #'a #tag #fields #excluded field p

let unaddr_of_struct_field
  (#tag: string) (#fields: struct_fields) (#excluded: set string)
  (field: field_of fields)
  (p: ref 'a (struct tag fields) (struct_pcm tag fields))
  (q: ref 'a
    (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
    (fields.get_field field).pcm)
: Steel unit
    ((p `pts_to_view` struct_view tag fields excluded) `star`
     (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
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
=
//let unaddr_of_struct_field #a #tag #fields #excluded field p q =
  unaddr_of_struct_field_ref' field p q

[@@c_typedef]
let typedef_struct (tag: string) (fields: struct_fields): typedef = {
  carrier = struct_pcm_carrier tag fields;
  pcm = struct_pcm tag fields;
  view_type = struct tag fields;
  view = struct_view tag fields emptyset;
}
