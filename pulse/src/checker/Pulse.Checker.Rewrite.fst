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

module Pulse.Checker.Rewrite

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.PP
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer

let check_vprop_equiv_ext r (g:env) (p q:vprop)
: T.Tac (vprop_equiv g p q)
= let elab_p = elab_term p in
  let elab_q = elab_term q in
  let res, issues = T.check_equiv (elab_env g) elab_p elab_q in
  T.log_issues issues;
  match res with
  | None -> 
    fail_doc g (Some r)
           [text "rewrite: could not prove equality of";
            pp p;
            pp q]
  | Some token ->
    VE_Ext g p q token

let rec check_vprop_equiv r (g:env) (p q:vprop)
: T.Tac (vprop_equiv g p q)
= if eq_tm p q
  then VE_Refl g p
  else (
    match inspect_term p, inspect_term q with
    | Some (Tm_ForallSL u1 b1 t1), Some (Tm_ForallSL u2 b2 t2) ->
      if eq_univ u1 u2
      && eq_tm b1.binder_ty b2.binder_ty
      then (
        let x = fresh g in
        assume (~(x `Set.mem` freevars t1));
        assume (~(x `Set.mem` freevars t2));
        let g' = push_binding g x b1.binder_ppname b1.binder_ty in
        let nx = b1.binder_ppname, x in
        let ext = check_vprop_equiv r g' (open_term_nv t1 nx) (open_term_nv t2 nx) in
        VE_Fa g x u1 b1 t1 t2 ext
      )
      else check_vprop_equiv_ext r g p q
    | Some (Tm_Star p1 p2), Some (Tm_Star q1 q2) ->
      let ext1 = check_vprop_equiv r g p1 q1 in
      let ext2 = check_vprop_equiv r g p2 q2 in
      VE_Ctxt g p1 p2 q1 q2 ext1 ext2
    | _ -> 
      check_vprop_equiv_ext r g p q
  )
  
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_Rewrite? t.term})

  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "check_rewrite" t.range g in
  let Tm_Rewrite {t1=p; t2=q} = t.term in
  let (| p, p_typing |) = check_vprop g p in
  let (| q, q_typing |) = check_vprop g q in
  let equiv_p_q = check_vprop_equiv t.range g p q in
	let d = T_Rewrite _ p q p_typing equiv_p_q in
	prove_post_hint (try_frame_pre pre_typing (match_comp_res_with_post_hint d post_hint) res_ppname) post_hint t.range
