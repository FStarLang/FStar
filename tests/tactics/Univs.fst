module Univs

(* Basic tests on universes *)

open FStar.Tactics

#set-options "--print_universes --print_implicits"

let refl0 (a:Type u#0) (x:a) : Lemma (x == x) = ()
let refl1 (a:Type u#1) (x:a) : Lemma (x == x) = ()
let refl2 (a:Type u#2) (x:a) : Lemma (x == x) = ()
let refl (a:Type u#aa) (x:a) : Lemma (x == x) = ()

let test00 (x:int) = assert (x == x) by (apply_lemma (`refl0))

[@expect_failure]
let test01 (x:int) = assert (x == x) by (apply_lemma (`refl1))

[@expect_failure]
let test02 (x:int) = assert (x == x) by (apply_lemma (`refl2))

let test0u (x:int) = assert (x == x) by (apply_lemma (`refl))

[@expect_failure]
let test10 (x:Type0) = assert (x == x) by (apply_lemma (`refl0))

let test11 (x:Type0) = assert (x == x) by (apply_lemma (`refl1))

[@expect_failure]
let test12 (x:Type0) = assert (x == x) by (apply_lemma (`refl2))

let test1u (x:Type0) = assert (x == x) by (apply_lemma (`refl))

[@expect_failure]
let test20 (x:Type u#1) = assert (x == x) by (apply_lemma (`refl0))

[@expect_failure]
let test21 (x:Type u#1) = assert (x == x) by (apply_lemma (`refl1))

let test22 (x:Type u#1) = assert (x == x) by (apply_lemma (`refl2))

let test2u (x:Type u#1) = assert (x == x) by (apply_lemma (`refl))


[@expect_failure]
let testu0 (x:Type u#aa) = assert (x == x) by (apply_lemma (`refl0))

[@expect_failure]
let testu1 (x:Type u#aa) = assert (x == x) by (apply_lemma (`refl1))

[@expect_failure]
let testu2 (x:Type u#aa) = assert (x == x) by (apply_lemma (`refl2))

let testuu (x:Type u#aa) = assert (x == x) by (apply_lemma (`refl))
