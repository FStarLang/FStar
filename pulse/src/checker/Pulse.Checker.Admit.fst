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

let check
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
    : (c:comp_st { comp_post_matches_hint c post_hint } &
       comp_typing g c (universe_of_comp c))
    = match post, post_hint with
      | None, None ->
        fail g None "could not find a post annotation on admit, please add one"

      | Some post1, Some post2 ->
        fail g None
          (Printf.sprintf "found two post annotations on admit: %s and %s, please remove one"
             (P.term_to_string post1)
             (P.term_to_string post2.post))
      
      | Some post, _ ->
        let (| u, t_typing |) = check_universe g t in    
        let post_opened = open_term_nv post px in      
        let (| post_opened, post_typing |) = 
          check_tot_term (push_binding g x (fst px) t) post_opened tm_vprop
        in
        let post = close_term post_opened x in
        let s : st_comp = {u;res=t;pre;post} in
        assume (open_term (close_term post_opened x) x == post_opened);
        let d_s : st_comp_typing _ s = STC _ s x t_typing pre_typing post_typing in
        (match c with
         | STT -> (| _,  CT_ST _ _ d_s |)
         | STT_Ghost -> (| _, CT_STGhost _ tm_emp_inames _ (magic ()) d_s |)
         | STT_Atomic -> (| _, CT_STAtomic _ tm_emp_inames Neutral _ (magic ()) d_s |))

      | _, Some post ->
        let post : post_hint_t = post in
        if x `Set.mem` freevars post.post
        then fail g None "Impossible: unexpected freevar clash in Tm_Admit, please file a bug-report"
        else (
          let post_typing_rec = post_hint_typing g post x in
          let post_opened = open_term_nv post.post px in              
          assume (close_term post_opened x == post.post);
          let s : st_comp = {u=post.u;res=post.ret_ty;pre;post=post.post} in
          let d_s : st_comp_typing _ s =
            STC _ s x post_typing_rec.ty_typing pre_typing post_typing_rec.post_typing in
          
          match post.effect_annot with
          | EffectAnnotSTT -> (| _,  CT_ST _ _ d_s |)
          | EffectAnnotGhost { opens } ->
            let d_opens : tot_typing post.g opens tm_inames = post.effect_annot_typing in
            assert (g `env_extends` post.g);
            let d_opens : tot_typing g opens tm_inames = magic () in  // weakening
            (| _, CT_STGhost _ opens _ d_opens d_s |)
          | EffectAnnotAtomic { opens }
          | EffectAnnotAtomicOrGhost { opens } ->
            let d_opens : tot_typing post.g opens tm_inames = post.effect_annot_typing in
            assert (g `env_extends` post.g);
            let d_opens : tot_typing g opens tm_inames = magic () in  // weakening
            (| _, CT_STAtomic _ opens Neutral _ d_opens d_s |)
        )
  in
  let (| c, d_c |) = res in
  let d = T_Admit _ _ d_c in
  checker_result_for_st_typing (| _, _, d |) res_ppname
