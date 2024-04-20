module BugBoxInjectivity

noeq
type ceq (#a:Type) x : a -> Type =
  | Refl : ceq #a x x

let test a (x y:a) (h:ceq #a x y) : Lemma (x == y) = ()
 
[@expect_failure]
let bad (h0:ceq true true) (h1:ceq false false) : Lemma (true == false) =
  let Refl = h0 in
  let Refl = h1 in
  ()

open FStar.Functions
module CC = FStar.Cardinality.Universes

type t (a:Type u#1) : Type u#0 =
  | Mk : t a

let inj_t (#a:Type u#1) (x:t a)
: Lemma (x == Mk #a)
= let Mk #_ = x in ()

[@@expect_failure]
let t_injective : squash (is_inj t) = 
  introduce forall f0 f1.
      t f0 == t f1 ==> f0 == f1
  with introduce _ ==> _
  with _ . (
    inj_t #f0 Mk;
    inj_t #f1 (coerce_eq () (Mk #f0)) 
  )


#push-options "--ext 'compat:injectivity'"
noeq
type test2 (a:Type u#2) : Type u#1 =
  | Mk2 : test2 a
#pop-options

let test2_inhabited (f:Type u#2) : test2 f = Mk2
let test2_injective (f0 f1:Type u#2) 
: Lemma
  (ensures test2 f0 == test2 f1 ==> f0 == f1)
= let x : test2 f0 = test2_inhabited f0 in
  let Mk2 #_ = x in
  ()
open FStar.Functions
let itest2_injective' : squash (is_inj test2) = 
  introduce forall f0 f1.
      test2 f0 == test2 f1 ==> f0 == f1
  with introduce _ ==> _
  with _ . (
    test2_injective f0 f1
  )
let fals () : squash False =
  CC.no_inj_universes_suc test2