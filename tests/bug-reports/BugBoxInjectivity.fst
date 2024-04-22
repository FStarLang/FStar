module BugBoxInjectivity

//The original bug; using an indirection to subvert the injectivity check
let mytype1 = Type u#1

type my_t (a:mytype1) : Type u#0 =
  | My : my_t a

let inj_my_t (#a:Type u#1) (x:my_t a)
: Lemma (x == My #a)
= ()

[@@expect_failure]
let my_t_injective : squash (is_inj my_t) = 
  introduce forall f0 f1.
      my_t f0 == my_t f1 ==> f0 == f1
  with introduce _ ==> _
  with _ . (
    inj_my_t #f0 My;
    inj_my_t #f1 (coerce_eq () (My #f0)) 
  )

//Same thing without the indirection
type t (a:Type u#1) : Type u#0 =
  | Mk : t a

let inj_t (#a:Type u#1) (x:t a)
: Lemma (x == Mk #a)
= ()

[@@expect_failure]
let t_injective : squash (is_inj t) = 
  introduce forall f0 f1.
      t f0 == t f1 ==> f0 == f1
  with introduce _ ==> _
  with _ . (
    inj_t #f0 Mk;
    inj_t #f1 (coerce_eq () (Mk #f0)) 
  )

open FStar.Functions
module CC = FStar.Cardinality.Universes
//Disabling the injectivity check on parameters is inconsistent
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
let itest2_injective' : squash (is_inj test2) = 
  introduce forall f0 f1.
      test2 f0 == test2 f1 ==> f0 == f1
  with introduce _ ==> _
  with _ . (
    test2_injective f0 f1
  )
let fals () : squash False =
  CC.no_inj_universes_suc test2


//Another test case to make sure that indexed types can be inverted properly
noeq
type ceq (#a:Type) x : a -> Type =
  | Refl : ceq #a x x

let test a (x y:a) (h:ceq #a x y) : Lemma (x == y) = ()

//But without collapsing
[@expect_failure]
let bad (h0:ceq true true) (h1:ceq false false) : Lemma (true == false) =
  let Refl = h0 in
  let Refl = h1 in
  ()
