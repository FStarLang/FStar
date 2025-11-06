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

module Pulse.Checker.Par

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.Checker.Comp

module T = FStar.Tactics.V2
module MT = Pulse.Typing.Metatheory

#push-options "--z3rlimit_factor 4 --split_queries no"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_Par? t.term})
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= let g = push_context "check_par" t.range g in
  let Tm_Par {pre1=preL; body1=eL; post1=postL;
              pre2=preR; body2=eR; post2=postR} = t.term in
  let (| preL, preL_typing |) = check_tot_term g preL tm_slprop in
  let (| preR, preR_typing |) = check_tot_term g preR tm_slprop in

  let postL_hint = intro_post_hint g EffectAnnotSTT None postL in
  let (| eL, cL, eL_typing |) =
    let ppname = mk_ppname_no_range "_par_l" in
    let r = check g preL preL_typing (PostHint postL_hint) ppname eL in
    apply_checker_result_k r ppname
  in
  let cL_typing = MT.st_typing_correctness eL_typing in

  let postR_hint = intro_post_hint g EffectAnnotSTT None postR in
  let (| eR, cR, eR_typing |) =
    let ppname = mk_ppname_no_range "_par_r" in
    let r = check g preR preR_typing (PostHint postR_hint) ppname eR in
    apply_checker_result_k r ppname
  in
  let cR_typing = MT.st_typing_correctness eR_typing in
  
  let x = fresh g in
  assume (comp_u cL == comp_u cR);
  let d = T_Par _ _ _ _ _ x cL_typing cR_typing eL_typing eR_typing in
  let (|_,d|) = match_comp_res_with_post_hint d post_hint in
  prove_post_hint (try_frame_pre false pre_typing (|_,_,d|) res_ppname) post_hint t.range
#pop-options
