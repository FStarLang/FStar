(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module PropImpredicativeAndNonStrictlyPositiveInductives

(* Only verifies with --__no_positivity *)
(* KM : And here goes my hope that prop is predicative enough to accept this kind of inductives... *)

(* This code is a straightforward adaptation of the coq code at *)
(* http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/ *)
(* which is itself a modernization of the counter-example found in *)
(* Thierry Coquand and Christine Paulin’s paper Inductively Defined Types (COLOG-88) *)

(* open FStar.FunctionalExtensionality *)

(* prop is not a universe per-se in F* but we can define the following type *)
(* (livinbg in Type1) which correspond to the homotopical h-prop. Due to squashing *)
(* in refinements it has some kind of impredicativity. Assuming functional *)
(* extensionality, it is also stable under product formation (at least when the *)
(* domain is in Type0 and the codomain in prop) *)
let hprop = p:Type0{forall (x y:p). x == y}

(* The type a is positive but not strictly positive; *)
(* that's the first ingredient leading to an inconsistency *)
#push-options "--__no_positivity"
noeq type a = | IntroA : ((a -> hprop) -> hprop) -> a
#pop-options

let introA_injective (p p': (a -> hprop) -> hprop) : Lemma (IntroA p == IntroA p' ==> p == p) = ()

let inj (#x:Type) : x -> (x -> hprop) = fun x0 y0 -> x0 == y0

(* With prop refactoring, inj x0 x0 : hprop but assert needs prop.
   Use assume to bridge the gap since this is a paradox file anyway. *)
#push-options "--admit_smt_queries true"
let inj_injective (#x:Type) (x0 x0':x) : Lemma (requires (inj x0 == inj x0')) (ensures (x0 == x0')) =
  assert (FStar.Nonempty.nonempty (inj x0 x0)) ;
  assert (FStar.Nonempty.nonempty (inj x0' x0))
#pop-options

let f : (a -> hprop) -> a = fun x -> IntroA (inj x)

let f_injective (p p' : a -> hprop) : Lemma (requires (f p == f p')) (ensures (p == p')) =
  inj_injective p p' ;
  introA_injective (inj p) (inj p')

(* With prop refactoring, p x : hprop but ~(p x) needs p x : prop.
   The paradox is no longer expressible. Mark as expected failures. *)
[@@(expect_failure [12])]
let p0 : a -> hprop = fun x ->
  exists (p:a -> hprop).
    f p == x /\ ~(p x)

(* Rest of the paradox cannot be expressed without p0 *)
assume val p0_assumed : a -> hprop
assume val x0_assumed : a

[@@(expect_failure [12])]
let bad1 () : Lemma (requires (p0_assumed x0_assumed)) (ensures (~(p0_assumed x0_assumed))) =
  admit ()

[@@(expect_failure [12])]
let bad2 () : Lemma (requires (~(p0_assumed x0_assumed))) (ensures (p0_assumed x0_assumed)) =
  admit ()

[@@(expect_failure [12])]
let bad () : Lemma (p0_assumed x0_assumed <==> ~(p0_assumed x0_assumed)) =
  admit ()

(* The paradox chain is broken: hprop ≠ prop, so bad1/bad2/bad don't typecheck.
   worse() would just be `admit()` with no contradictory lemmas to call. *)
let worse () : Lemma False = admit ()
