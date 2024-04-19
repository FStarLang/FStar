module BugBoxInjectivity
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


// #restart-solver
// #push-options "--log_queries --query_stats --debug BugBoxInjectivity --debug_level SMTEncoding"
// module CC = FStar.Cardinality.Universes
// noeq
// type test (a:Type u#0 -> Type u#1) : Type u#1 =
//   | Mk : test a

// let const (f:Type u#1) : Type u#0 -> Type u#1 = fun _ -> f
// let itest (f:Type u#1) : Type u#1 = test (const f)
// let itest_inhabited (f:Type u#1) : itest f = Mk 
// let const_inversion (f0 f1:Type u#1)
// : Lemma 
//   (requires const f0 == const f1)
//   (ensures f0 == f1)
// = let _f0 = const f0 int in
//   let _f1 = const f1 int in
//   assert (_f0 == _f1);
//   ()
// let itest_injective (f0 f1:Type u#1) 
// : Lemma
//   (ensures itest f0 == itest f1 ==> const f0 == const f1)
// = let x : test (const f0) = itest_inhabited f0 in
//   let Mk #_ = x in
//   ()
// open FStar.Functions
// let itest_injective' : squash (is_inj itest) = 
//   introduce forall f0 f1.
//       itest f0 == itest f1 ==> f0 == f1
//   with introduce _ ==> _
//   with _ . (
//     itest_injective f0 f1;
//     const_inversion f0 f1
//   )
// [@@expect_failure [189]] //itest is not in the right universe to use this lemma
// let fals : squash False =
//   CC.no_inj_universes_suc itest


// #push-options "--ext 'compat:injectivity'"
// noeq
// type test2 (a:Type u#2) : Type u#1 =
//   | Mk2 : test2 a
// #pop-options

// let test2_inhabited (f:Type u#2) : test2 f = Mk2
// let test2_injective (f0 f1:Type u#2) 
// : Lemma
//   (ensures test2 f0 == test2 f1 ==> f0 == f1)
// = let x : test2 f0 = test2_inhabited f0 in
//   let Mk2 #_ = x in
//   ()
// open FStar.Functions
// let itest2_injective' : squash (is_inj test2) = 
//   introduce forall f0 f1.
//       test2 f0 == test2 f1 ==> f0 == f1
//   with introduce _ ==> _
//   with _ . (
//     test2_injective f0 f1
//   )
// let fals () : squash False =
//   CC.no_inj_universes_suc test2