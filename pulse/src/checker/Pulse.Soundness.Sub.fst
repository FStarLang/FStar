(*
   Copyright 2023 Microsoft Research

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

module Pulse.Soundness.Sub
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

(* For simple_arr and elab_st_sub *)
open Pulse.Elaborate.Core

(* should be trivial *)
let app_typing (g:R.env) (ty1 ty2 f tm : R.term)
       (df : RT.tot_typing g f (simple_arr ty1 ty2))
       (dt : RT.tot_typing g tm ty1)
  : GTot (RT.tot_typing g (R.pack_ln (R.Tv_App f (tm, R.Q_Explicit))) ty2)
  = RU.magic()

let sub_soundness #g #t #c d (cb : soundness_t d) =
  let T_Sub _ e c1 c2 d_t d_sub = d in
  let (| coercion, c_typ |) : (t:R.term & RT.tot_typing (elab_env g) t (simple_arr (elab_comp c1) (elab_comp c2))) =
    elab_st_sub d_sub
  in
  let e_typing = cb g _ _ d_t in
  app_typing _ _ _ coercion (elab_st_typing d_t) c_typ e_typing
