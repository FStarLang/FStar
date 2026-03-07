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

module Pulse.Checker.Defer

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module RU = Pulse.RuntimeUtils

#push-options "--z3rlimit_factor 10 --fuel 0 --ifuel 0"
let check
  (g:env)
  (pre:term)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Defer? t.term })
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= allow_invert post_hint;
  match post_hint with
  | NoHint | TypeHint _ ->
    fail g (Some t.range)
      "defer requires an annotated post-condition"

  | PostHint post ->
    let g = push_context "check_defer" t.range g in
    let Tm_Defer { handler_pre=cpre; handler; body } = t.term in
    // Check handler_pre is a valid slprop
    let cpre = check_slprop g cpre in
    // Extend env: push BindingPost so goto labels see cpre
    let g' = push_post g cpre in
    // Extend post_hint: body's postcondition must include cpre
    let body_post : post_hint_for_env g' =
      { post with post = tm_star post.post cpre } in
    // Check body with extended env and post_hint
    let (| body', c_body |) = apply_checker_result_k (check g' pre (PostHint body_post) res_ppname body) res_ppname in
    // The body's postcondition should be (post ** cpre)
    // Now check the handler with cpre as (part of) precondition
    let post_hint_for_handler: post_hint_for_env g = {
      g;
      effect_annot = body_post.effect_annot;
      ret_ty = tm_unit;
      u = u0;
      post = tm_emp;
    } in
    let (| handler, c_handler |) = apply_checker_result_k (check g cpre (PostHint post_hint_for_handler) ppname_default handler) ppname_default in
    // After body, context is (post ** cpre); handler consumes cpre
    // Overall defer comp has the original post (without cpre)
    let t = wtag (Some (ctag_of_comp_st c_body)) (Tm_Defer { handler_pre = cpre; handler; body=body' }) in
    let c = C_ST { u=comp_u c_body; res=comp_res c_body; pre; post=post.post } in
    let c'' = match_comp_res_with_post_hint t c post_hint in
    prove_post_hint
      (try_frame_pre false #g (|t, c''|) res_ppname)
      post_hint
      t.range
#pop-options