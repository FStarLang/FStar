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

module Pulse.Checker.ForwardJumpLabel

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.Checker.ImpureSpec
module RU = Pulse.RuntimeUtils

let starts_with (a b: string) : bool =
  if String.length b > String.length a then false
  else String.sub a 0 (String.length b) = b

#push-options "--z3rlimit 10 --split_queries always"
let check
    (g:env)
    (pre:term)
    (pre_typing:tot_typing g pre tm_slprop)
    (post_hint0:post_hint_opt g)
    (res_ppname:ppname)
    (t:st_term { Tm_ForwardJumpLabel? t.term })
    (check:check_t)
    : T.Tac (checker_result_t g pre post_hint0) =
  let rng = t.range in
  let Tm_ForwardJumpLabel { lbl; body; post = c } = t.term in
  let has_explicit_post = not (T.term_eq (comp_post c) tm_emp) in
  let post : post_hint_t =
    if has_explicit_post then
      let post_slprop = purify_spec g { ctxt_now = pre; ctxt_old = None } (comp_post c) in
      intro_post_hint g EffectAnnotSTT None post_slprop
    else
      match post_hint0 with
      | NoHint | TypeHint .. ->
        fail g (Some rng) "Labels require a postcondition"
      | PostHint ph ->
        ph
  in
  if not (EffectAnnotSTT? post.effect_annot) then
    if T.unseal lbl.name `starts_with` "_" then
      // TODO: just ignore early return/continue labels in atomic/ghost contexts for now
      let lbl_x = fresh g in
      let body = open_st_term_nv body (lbl, lbl_x) in
      check _ _ pre_typing _ res_ppname body
    else
      fail g (Some rng) "Labels require stt"
  else
    let lbl_c = C_ST {
      u = post.u;
      res = post.ret_ty;
      pre = post.post;
      post = tm_is_unreachable;
    } in
    let lbl_x = fresh g in
    let g' = push_goto g lbl_x lbl lbl_c in
    let pre_typing': tot_typing g' pre tm_slprop = RU.magic () in
    let post_hint' : post_hint_opt g' =
      assume post_hint_for_env_p g' post;
      PostHint post in
    let body = open_st_term_nv body (lbl, lbl_x) in
    let body' = check g' pre pre_typing' post_hint' res_ppname body in
    let (| body', body'_c, body'_typing |) = apply_checker_result_k #g' #pre #post body' res_ppname in
    assert comp_u body'_c == comp_u lbl_c;
    assert comp_res body'_c == comp_res lbl_c;
    assert comp_pre body'_c == pre;
    assert comp_post body'_c == post.post;
    assert C_ST? body'_c;
    assert lbl_c == goto_comp_of_block_comp body'_c;
    let body = close_st_term body' lbl_x in
    let t = wtag (Some STT) (Tm_ForwardJumpLabel {
      lbl = lbl;
      body = close_st_term body' lbl_x;
      post = body'_c;
    }) in
    assume open_st_term' body (term_of_nvar (lbl, lbl_x)) 0 == body';
    let typing: st_typing g t body'_c =
      T_ForwardJumpLabel g (lbl, lbl_x) body body'_c body'_typing in
    if not has_explicit_post then (
      assert post_hint0 == PostHint post;
      checker_result_for_st_typing (| _, _, typing |) res_ppname
    ) else (
      let (| c'', typing'' |) = match_comp_res_with_post_hint typing post_hint0 in
      prove_post_hint #g
        (try_frame_pre false #g pre_typing (|_,c'',typing''|) res_ppname)
        post_hint0
        rng
    )
#pop-options