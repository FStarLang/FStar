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

module Pulse.Checker.Admit

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module P = Pulse.Syntax.Printer
module RU = Pulse.Reflection.Util

let check_core
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Admit? t.term })

  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_admit" t.range in

  let Tm_Admit { ctag = c; typ=t; post } = t.term in

  let x = fresh g in
  let px = v_as_nv x in
  let res
    : (t:term &
       u:universe &
       universe_of g t u &
       post:vprop &
       tot_typing (push_binding g x (fst px) t) post tm_vprop)
    = match post, post_hint with
      | None, None ->
        fail g None "could not find a post annotation on admit, please add one"
      
        //
        // If there is a post annoatation on admit, pick that
        //   plus make the return type as unit
        //
      | Some post, _ ->
        let t : term = { t = Tm_FStar RU.unit_tm; range = t.range } in
        let (| u, t_typing |) = check_universe g t in    
        let post_opened = open_term_nv post px in      
        let (| post, post_typing |) = 
            check_tot_term (push_binding g x (fst px) t) post_opened tm_vprop
        in
        (| t, u, t_typing, post, post_typing |)

      | _, Some post ->
        let post : post_hint_t = post in
        if x `Set.mem` freevars post.post
        then fail g None "Impossible: unexpected freevar clash in Tm_Admit, please file a bug-report"
        else (
          let post_typing_rec = post_hint_typing g post x in
          let post_opened = open_term_nv post.post px in              
          assume (close_term post_opened x == post.post);
          (| post.ret_ty, post.u, post_typing_rec.ty_typing, post_opened, post_typing_rec.post_typing |)
        )
  in
  let (| t, u, t_typing, post_opened, post_typing |) = res in
  let post = close_term post_opened x in
  let s : st_comp = {u;res=t;pre;post} in

  assume (open_term (close_term post_opened x) x == post_opened);
  let d = T_Admit _ _ c (STC _ s x t_typing pre_typing post_typing) in
  prove_post_hint (try_frame_pre pre_typing (match_comp_res_with_post_hint d post_hint) res_ppname) post_hint t.range

let check
    (g:env)
    (pre:term)
    (pre_typing:tot_typing g pre tm_vprop)
    (post_hint:post_hint_opt g)
    (res_ppname:ppname)
    (t:st_term { Tm_Admit? t.term })

  : T.Tac (checker_result_t g pre post_hint) 
  = let Tm_Admit r = t.term in
    match post_hint with
    | Some { ctag_hint=Some ct } ->
      check_core g pre pre_typing post_hint res_ppname ({ t with term=Tm_Admit {r with ctag=ct}})
    | _ ->
      check_core g pre pre_typing post_hint res_ppname t
