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
module FStar.Tactics.BV.Lemmas

open FStar.BV
open FStar.UInt

// using uint_t' instead of uint_t breaks the tactic (goes to inl).

(* Congruence lemmas *)
let cong_bvand #n #w #x #y #z pf1 pf2 = ()
let cong_bvxor #n #w #x #y #z pf1 pf2 = ()
let cong_bvor #n #w #x #y #z pf1 pf2 = ()
let cong_bvshl #n #w #x #y pf = ()
let cong_bvshr #n #w #x #y pf = ()
let cong_bvdiv #n #w #x #y pf = ()
let cong_bvmod #n #w #x #y pf = ()
let cong_bvmul #n #w #x #y pf = ()
let cong_bvadd #n #w #x #y #z pf1 pf2 = ()
let cong_bvsub #n #w #x #y #z pf1 pf2 = ()
let eq_to_bv #n #x #y pf = int2bv_lemma_2 #n x y
let lt_to_bv #n #x #y pf = int2bv_lemma_ult_2 #n x y
let trans #n #x #y #z #w pf1 pf2 pf3 = ()
let trans_lt #n #x #y #z #w pf1 pf2 pf3 = ()
let trans_lt2 #n #x #y #z #w pf1 pf2 pf3 = int2bv_lemma_ult_2 x y