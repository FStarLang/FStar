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

module Pulse.Checker.Unreachable

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module P = Pulse.Syntax.Printer

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Unreachable? t.term })
: T.Tac (checker_result_t g pre post_hint)
= let rng = t.range in
  match post_hint with
  | None ->
    fail g (Some t.range)
        "Expected a postcondition to be annotated when unreachable is used"
  | Some post ->
    let x = fresh g in
    let px = v_as_nv x in
    let post : post_hint_t = post in
    if x `Set.mem` freevars post.post
    then fail g None "Impossible: unexpected freevar clash in Tm_Unreachable, please file a bug-report"
    else
        let ctag = ctag_of_effect_annot post.effect_annot in
        let post_typing_rec = post_hint_typing g post x in
        let post_opened = open_term_nv post.post px in              
        assume (close_term post_opened x == post.post);
        let t : term = post.ret_ty in
        let u = post.u in
        let t_typing : universe_of g t u = post_typing_rec.ty_typing in
        let post_typing = post_typing_rec.post_typing in
        assume (close_term post_opened x == post.post);
        let s : st_comp = {u; res=t; pre; post=post.post} in
        let stc : st_comp_typing g s = (STC _ s x t_typing pre_typing post_typing) in
        let ff = (tm_fstar (`False) rng) in
        let (|eff, ff_typing |) = Pulse.Checker.Pure.core_check_term_at_type g ff tm_prop in
        if eff <> T.E_Total then T.fail "Impossible: False has effect Ghost"
        else
            let ff_validity = Pulse.Checker.Pure.check_prop_validity g ff ff_typing in
            let dt = T_Unreachable g s ctag stc ff_validity in
            prove_post_hint (try_frame_pre pre_typing (match_comp_res_with_post_hint dt post_hint) res_ppname)
                            post_hint
                            (Pulse.RuntimeUtils.range_of_term t)
    

  
