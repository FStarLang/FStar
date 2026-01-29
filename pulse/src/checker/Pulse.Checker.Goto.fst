(*
   Copyright 2026 Microsoft Research

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

module Pulse.Checker.Goto

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

let check'
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g { PostHint? post_hint })
  (res_ppname:ppname)
  (t:st_term { Tm_Goto? t.term })
: T.Tac (checker_result_t g pre post_hint)
= let rng = t.range in
  let Tm_Goto { lbl; arg } = t.term in
  let PostHint ph = post_hint in
  match ph.effect_annot with
  | EffectAnnotSTT ->
    (match R.inspect_ln lbl with
    | R.Tv_Var v ->
      let v = (R.inspect_namedv v).uniq in
      (match lookup_goto g v with
      | Some (lbln, lbl_c) ->
        let (| arg, arg_typ |) = check_tot_term g arg (comp_res lbl_c) in
        let c' = C_ST {
          u = ph.u;
          res = ph.ret_ty;
          pre = open_term' (comp_pre lbl_c) arg 0;
          post = ph.post
        } in
        let t = wtag (Some STT) (Tm_Goto { lbl = term_of_nvar (lbln, v); arg }) in
        let typing: st_typing g t c' =
          let x' = fresh g in assume fresh_wrt x' g (freevars ph.post);
          let pht = post_hint_typing g ph x' in
          T_Goto _ (lbln, v) arg lbl_c arg_typ ph.u ph.ret_ty pht.ty_typing ph.post x' pht.post_typing in
        let (| c'', typing'' |) = match_comp_res_with_post_hint typing post_hint in
        prove_post_hint #g
          (try_frame_pre false #g pre_typing (|_,c'',typing''|) res_ppname)
          post_hint
          rng
      | None ->
        fail g (Some t.range) "Unknown goto label")
    | _ ->
      fail g (Some t.range) "Unknown goto label")
  | _ ->
    fail g (Some t.range) "goto requires stt"

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Goto? t.term })
: T.Tac (checker_result_t g pre post_hint)
= match post_hint with
  | NoHint ->
    let post_hint' = intro_post_hint g EffectAnnotSTT None (tm_pure tm_l_false) in
    let res = check' g pre pre_typing (PostHint post_hint') res_ppname t in
    retype_checker_result _ res
  | TypeHint ty ->
    let post_hint' = intro_post_hint g EffectAnnotSTT (Some ty) (tm_pure tm_l_false) in
    let res = check' g pre pre_typing (PostHint post_hint') res_ppname t in
    retype_checker_result _ res
  | PostHint post ->
    check' g pre pre_typing post_hint res_ppname t
