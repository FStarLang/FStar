module ProvableEquality
open FStar.Mul

//SNIPPET_START: vec$
type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)
//SNIPPET_END: vec$

//SNIPPET_START: vec_conversions$
let conv_vec_0 (#a:Type) (v:vec a ((fun x -> x) 0))
  : vec a 0
  = v

let conv_vec_1 (#a:Type) (v:vec a ((fun x -> x + 1) 0))
  : vec a 1
  = v
//SNIPPET_END: vec_conversions$

//SNIPPET_START: vec_conversions_fact$
let rec factorial (n:nat)
  : nat
  = if n = 0 then 1
    else n * factorial (n - 1)

let conv_vec_6 (#a:Type) (v:vec a (factorial 3))
  : vec a 6
  = v
//SNIPPET_END: vec_conversions_fact$

//SNIPPET_START: conv_int$
let conv_int (x : (fun b -> if b then int else bool) true)
  : int
  = x + 1
//SNIPPET_END: conv_int$

////////////////////////////////////////////////////////////////////////////////
// Provable equality
////////////////////////////////////////////////////////////////////////////////

//SNIPPET_START: equals$
type equals (#a:Type) : a -> a -> Type =
  | Reflexivity : #x:a -> equals x x
//SNIPPET_END: equals$

//SNIPPET_START: sample_equals_proofs$
let z_equals_z
  : equals 0 0
  = Reflexivity

let fact_3_eq_6
  : equals (factorial 3) 6
  = Reflexivity #_ #6
//SNIPPET_END: sample_equals_proofs$

//SNIPPET_START: equivalence_relation$
let reflexivity #a (x:a)
  : equals x x
  = Reflexivity

let symmetry #a (x y : a) (pf:equals x y)
  : equals y x
  = Reflexivity

let transitivity #a (x y z : a) (pf1:equals x y) (pf2:equals y z)
  : equals x z
  = Reflexivity
//SNIPPET_END: equivalence_relation$

//SNIPPET_START: uip_refl$
let uip_refl #a (x y:a) (pf:equals x y)
  : equals pf (Reflexivity #a #x)
  = Reflexivity
//SNIPPET_END: uip_refl$

//SNIPPET_START: uip_refl_explicit$
let uip_refl_explicit #a (x y:a) (pf:equals x y)
  : equals #(equals x y) pf (Reflexivity #a #x)
  = Reflexivity #(equals x y) #(Reflexivity #a #x)
//SNIPPET_END: uip_refl_explicit$

//SNIPPET_START: uip$
let uip #a (x y:a) (pf0 pf1:equals x y)
  : equals pf0 pf1
  = Reflexivity
//SNIPPET_END: uip$

//SNIPPET_START: conversion_with_equality_proofs$
let pconv_vec_z (#a:Type) (#n:nat) (_:(n == 0)) (v:vec a n)
  : vec a 0
  = v

let pconv_vec_nm (#a:Type) (#n #m:nat) (_:(n == m)) (v:vec a n)
  : vec a m
  = v

let pconv_int (#a:Type) (_:(a == int)) (x:a)
  : int
  = x + 1

let pconv_ab (#a #b:Type) (_:(a == b)) (v:a)
  : b
  = v
//SNIPPET_END: conversion_with_equality_proofs$

//SNIPPET_START: conversion_complex$
let pconv_der (#a #b:Type)
              (x y:int)
              (h:((x > 0 ==> a == int) /\
                  (y > 0 ==> b == int) /\
                  (x > 0 \/ y > 0)))
              (aa:a)
              (bb:b)
  : int
  = if x > 0 then aa - 1 else bb + 1
//SNIPPET_END: conversion_complex$


//SNIPPET_START: leibniz$
let lbz_eq (#a:Type) (x y:a) = p:(a -> Type) -> p x -> p y

// lbz_eq is an equivalence relation
let lbz_eq_refl #a (x:a)
  : lbz_eq x x
  = fun p px -> px
let lbz_eq_trans #a (x y z:a) (pf1:lbz_eq x y) (pf2:lbz_eq y z)
  : lbz_eq x z
  = fun p px -> pf2 p (pf1 p px)
let lbz_eq_sym #a (x y:a) (pf:lbz_eq x y)
  : lbz_eq y x
  = fun p -> pf (fun (z:a) -> (p z -> p x)) (fun (px: p x) -> px)

// equals and lbz_eq are isomorphic
let equals_lbz_eq (#a:Type) (x y:a) (pf:equals x y)
  : lbz_eq x y
  = fun p px -> px
let lbz_eq_equals (#a:Type) (x y:a) (pf:lbz_eq x y)
  : equals x y
  = pf (fun (z:a) -> equals x z) Reflexivity
//SNIPPET_END: leibniz$


open FStar.Tactics

//SNIPPET_START: funext_eta$
let eta (#a:Type) (#b: a -> Type) (f: (x:a -> b x)) = fun x -> f x
let funext_on_eta (#a : Type) (#b: a -> Type) (f g : (x:a -> b x))
                  (hyp : (x:a -> Lemma (f x == g x)))
  : squash (eta f == eta g)
  = _ by (norm [delta_only [`%eta]];
          pointwise (fun _ ->
             try_with
                     (fun _ -> mapply (quote hyp))
                     (fun _ -> trefl()));
           trefl())
//SNIPPET_END: funext_eta$


//SNIPPET_START: funext$
let funext =
  #a:Type ->
  #b:(a -> Type) ->
  f:(x:a -> b x) ->
  g:(x:a -> b x) ->
  Lemma (requires (forall (x:a). f x == g x))
        (ensures f == g)
//SNIPPET_END: funext$

//SNIPPET_START: funext_false$
let f (x:nat) : int = 0
let g (x:nat) : int = if x = 0 then 1 else 0
let pos = x:nat{x > 0}
let full_funext_false (ax:funext)
  : False
  = ax #pos f g;
    assert (f == g);
    assert (f 0 == g 0);
    false_elim()
//SNIPPET_END: funext_false$


//SNIPPET_START: eta_equiv_false$
let eta_equiv =
  #a:Type ->
  #b:(a -> Type) ->
  f:(x:a -> b x) ->
  Lemma (f == eta f)

let eta_equiv_false (ax:eta_equiv)
  : False
  = funext_on_eta #pos f g (fun x -> ());
    ax #pos f;
    ax #pos g;
    assert (f == g);
    assert (f 0 == g 0);
    false_elim()
//SNIPPET_END: eta_equiv_false$


//SNIPPET_START: dec_equals_dec$
let dec_equals (#a:eqtype) (x y:a) (_:squash (x = y))
  : equals x y
  = Reflexivity

let equals_dec (#a:eqtype) (x y:a) (_:equals x y)
  : squash (x = y)
  = ()
//SNIPPET_END: dec_equals_dec$


//SNIPPET_START: noeq$
noeq
type itree (a:Type) =
  | End : itree a
  | Node : hd:nat -> tl:(nat -> itree a) -> itree a
//SNIPPET_END: noeq$


//SNIPPET_START: unopteq$
unopteq
type t (f: Type -> Type) =
  | T : f bool -> t f

let _ = assert (hasEq (t list))

[@@expect_failure]
let _ = assert (hasEq (fun x -> x -> x))
//SNIPPET_END: unopteq$
