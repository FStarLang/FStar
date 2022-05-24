module Universes

//SNIPPET_START: ty$
let ty : Type = Type
//SNIPPET_END: ty$

#push-options "--print_universes"

//SNIPPET_START: ty_constants$
let ty0 : Type u#1 = Type u#0
let ty0' : Type u#1 = Type0
let ty1 : Type u#2 = Type u#1
let ty2 : Type u#3 = Type u#2
//SNIPPET_END: ty_constants$


[@@expect_failure]
//SNIPPET_START: ty_bad$
let ty_bad : Type u#0 = Type u#0
//SNIPPET_END: ty_bad$

//SNIPPET_START: ty_poly$
let ty_poly : Type u#(a + 1) = Type u#a
//SNIPPET_END: ty_poly$


//SNIPPET_START: ty_poly_assert$
let _ = assert (ty_poly u#0 == ty0)
let _ = assert (ty_poly u#1 == ty1)
let _ = assert (ty_poly u#2 == ty2)
let _ = assert (ty_poly == ty0)
//SNIPPET_END: ty_poly_assert$


//SNIPPET_START: some common types$
let _ : Type0 = nat
let _ : Type0 = bool
let _ : Type0 = nat -> bool
//SNIPPET_END: some common types$
let _ : Type0 = nat & bool
let _ : Type u#1 = a:Type0 -> a -> a

//SNIPPET_START: poly_id$
let id_t : Type u#(i + 1) = a:Type u#i -> a -> a
let id : id_t = fun a x -> x
//SNIPPET_END: poly_id$

//SNIPPET_START: seemingly_self_application$
let seemingly_self_application : id_t = id _ id
//SNIPPET_END: seemingly_self_application$

//SNIPPET_START: stratified_application$
let stratified_application : id_t u#i = id u#(i + 1) (id_t u#i) (id u#i)
//SNIPPET_END: stratified_application$

//SNIPPET_START: list$
type list (a:Type u#a) : Type u#a  =
 | Nil : list a
 | Cons : hd:a -> tl:list a -> list a
//SNIPPET_END: list$ 

//SNIPPET_START: list'$
type list' (a:Type u#a) : Type u#(1 + a)  =
 | Nil' : list' a
 | Cons' : hd:a -> tl:list' a -> list' a
//SNIPPET_END: list'$ 

//SNIPPET_START: pair$
type pair (a:Type u#a) (b:Type u#b) : Type u#(max a b) =
  | Pair : fst:a -> snd:b -> pair a b
//SNIPPET_END: pair$

//SNIPPET_START: top$
noeq
type top : Type u#(a + 1) =
  | Top : a:Type u#a -> v:a -> top
//SNIPPET_END: top$  


//SNIPPET_START: prop$
let _ : Type u#1 = prop
//SNIPPET_END: prop$

//SNIPPET_START: prop impredicative$
let _ : Type u#1 = a:prop -> a
let _ : Type u#0 = squash (a:prop -> a)
let _ : prop = forall (a:prop). a
let _ : prop = exists (a:prop). a
//SNIPPET_END: prop impredicative$

//SNIPPET_START: id_top_level$
let i (#a:Type) (x:a) = x
let _ = i u#0 0, i u#1 nat, i u#2 (Type u#0)
//SNIPPET_END: id_top_level$

[@@expect_failure]
//SNIPPET_START: no_local_poly$
let no_universe_poly_locally () = 
  let i (#a:Type) (x:a) = x in
  let _ = i u#0 0, i u#1 nat, i u#2 (Type u#0) in
  ()
//SNIPPET_END: no_local_poly$

//SNIPPET_START: type_poly$
let type_poly_locally () = 
  let i (#a:Type) (x:a) = x in
  let _ = i #unit (), i #bool true, i #nat 0 in
  ()
//SNIPPET_END: type_poly$

//SNIPPET_START: val tup2$
val tup2 (a:Type) (b:Type) : Type
//SNIPPET_END: val tup2$

[@@expect_failure]
//SNIPPET_START: let tup2$
let tup2 a b = a & b
//SNIPPET_END: let tup2$

//SNIPPET_START: tuple2$
let tuple2 (a:Type) (b:Type) : Type = a & b
//SNIPPET_END: tuple2$

//SNIPPET_START: tup2_again$
val tup2_again (a:Type u#a) (b:Type u#b) : Type u#(max a b)
let tup2_again a b = a & b
//SNIPPET_END: tup2_again$

//SNIPPET_START: list_alt$
noeq
type list_alt : Type u#a -> Type u#(a + 1) = 
  | NilAlt: a:Type -> list_alt a
  | ConsAlt: a:Type -> hd:a -> tl:list_alt a -> list_alt a
//SNIPPET_END: list_alt$

//SNIPPET_START: crazy_index$
type t : Type u#100 -> Type u#0 = 
  | T : unit -> t (FStar.Universe.raise_t unit)
//SNIPPET_END: crazy_index$
