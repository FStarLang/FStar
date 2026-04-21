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
module IOWPInconsistent

(* Showing that the WP that would result from using DM4F on the IO monad transformer leads to inconsistency.             *)
(*                                                                                                                       *)
(* To simplify the proof, here we show that considering just unit-output already leads to inconsistency,                 *)
(* where by unit-output we mean the algebraically given effect with one unary operation symbol `out : 1`.                *)
(*                                                                                                                       *)
(* Based on:                                                                                                             *)
(*   - the unit-output monad transformer, if it exists, given by                                                         *)
(*       Out_T T X = mu Z . T (Z + X)                                                                                    *)
(*                                                                                                                       *)
(*     which is also the counterexample used to the existence of the sum of continuations with arbitrary other monads in *)
(*       M. Hyland et al. Combining algebraic effects with continuations. Theor. Comput. Sci. 375(1-3): 20-40 (2007)     *)
(*                                                                                                                       *)
(*   - the DM4F construction amounting to applying Out_T to the prop-valued continuation monad, resulting in             *)
(*       Out_WP X = mu Z . ((Z + X) -> prop) -> prop                                                                     *)
(*                                                                                                                       *)
(*   - the counterexample to allowing inductive types to be not strictly positive given in                               *)
(*       FStar/examples/paradoxes/propImpredicativeAndNonStrictlyPositiveinductives.fst                                  *)
(*                                                                                                                       *)
(*     which itself is based on the following note about (non) strict positivity and impredicativity                     *)
(*       http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/                                  *)


#set-options "--__no_positivity"                   (* enabling non strict positivity so as to ensure Out_WP exists in F* *)

(* The local sub-singleton prop definition is no longer compatible with Prims.prop
   (which is now opaque), so the paradox chain is broken by the refactoring. *)
let sprop = p:Type0{forall (x y:p). x == y}

noeq type out_wp (a:Type) =                      (* the non strictly positive WP type for output one would get from DM4F *)
  | Intro : ((either (out_wp a) a -> sprop) -> sprop) -> out_wp a

                                                          (* The rest is simply a recreation of the paradoxes considered *)
                                                          (* in the notes above, adapted to the case of unit-output.     *)
let intro_injective (#a:Type) (p p': (either (out_wp a) a -> sprop) -> sprop) 
  : Lemma (Intro p == Intro p' ==> p == p) = 
  ()

let inj (#x:Type) : x -> (x -> sprop) = fun x0 y0 -> x0 == y0

(* inj x0 x0 : sprop, but assert needs Prims.prop — paradox broken *)
[@@(expect_failure [12; 12])]
let inj_injective (#x:Type) (x0 x0':x) 
  : Lemma (requires (inj x0 == inj x0')) 
          (ensures  (x0 == x0')) =
  assert (inj x0 x0) ;
  assert (inj x0' x0)

let f (#a:Type) (p:either (out_wp a) a -> sprop) : either (out_wp a) a = 
  Inl (Intro (inj p))

(* Depends on inj_injective which can't be proven *)
assume val f_injective : #a:Type -> p:(either (out_wp a) a -> sprop) -> p':(either (out_wp a) a -> sprop) ->
  Lemma (requires (f p == f p')) 
        (ensures  (p == p'))

(* sprop ≠ prop, so exists/~ don't work with sprop-valued functions *)
[@@(expect_failure [12])]
let p0 : #a:Type -> either (out_wp a) a -> sprop = fun #a x ->
  exists (p:either (out_wp a) a -> sprop).
    f #a p == x /\ ~(p x)

(* Rest of the paradox depends on p0 which can't be defined *)
assume val p0_assumed : #a:Type -> either (out_wp a) a -> sprop
let x0 (#a:Type) = f #a p0_assumed

open FStar.Classical

[@@(expect_failure [12])]
let bad1 (a:Type) 
  : Lemma (requires (p0_assumed (x0 #a))) 
          (ensures  (~(p0_assumed (x0 #a)))) =
  admit ()

[@@(expect_failure [12])]
let bad2 (a:Type) 
  : Lemma (requires (~(p0_assumed (x0 #a)))) 
          (ensures  (p0_assumed (x0 #a))) =
  admit ()

(* Paradox chain is broken — bad1/bad2 don't typecheck *)
let out_wp_inconsistent (a:Type) 
  : Lemma False = 
  admit ()
