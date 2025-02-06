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
module R = FStar.Reflection.V2

let check_slprop_equiv_ext r (g:env) (p q:slprop)
: T.Tac (slprop_equiv g p q)
= let res, issues = Pulse.Typing.Util.check_equiv_now (elab_env g) p q in
  match res with
  | None -> 
    fail_doc_with_subissues g (Some r) issues [
      text "rewrite: could not prove equality of";
      pp p;
      pp q;
    ]
  | Some token ->
    VE_Ext g p q token

let check_slprop_equiv_tac r (g:env) (p q:slprop) (tac_tm : term)
: T.Tac (slprop_equiv g p q)
= let open FStar.Reflection.Typing in
  let open FStar.Stubs.TypeChecker.Core in
  begin match T.inspect tac_tm with
  | _ -> ()
  | T.Tv_FVar _ -> ()
  | _ ->
    fail_doc g (Some <| T.range_of_term tac_tm) [
      text "Currently, tactics used in rewrite..by must be \
            top-level names. Please hoist this tactic into a top-level
            definition."
    ]
  end;
  let u0 : R.universe = R.pack_universe R.Uv_Zero in
  let goal = Pulse.Reflection.Util.stt_slprop_equiv p q in
  let r_env = elab_env g in
  let goal_typing :
    my_erased (T.typing_token r_env goal (E_Total, R.pack_ln (R.Tv_Type u0)))
    = magic()
  in
  let goal_typing_tok : squash (T.typing_token r_env goal (E_Total, R.pack_ln (R.Tv_Type u0))) =
    match goal_typing with | E x -> ()
  in
  let res, issues = T.call_subtac_tm r_env tac_tm u0 goal in
  match res with
  | None -> 
    fail_doc_with_subissues g (Some r) issues [
      text "rewrite: could not prove equality of";
      pp p;
      pp q;
      text "Using tactic:" ^/^ pp tac_tm
    ]
  | Some token ->
    // Need a VE_ rule to turn an arbitrary proof into a slprop_equiv.
    // Or use enough core lemmas to show that slprop_equiv implies equality here,
    // and then use VE_Ext.
    VE_Ext g p q (magic ())

let rec check_slprop_equiv r (g:env) (p q:slprop)
: T.Tac (slprop_equiv g p q)
= if eq_tm p q
  then VE_Refl g p
  else (
    match inspect_term p, inspect_term q with
    | Tm_ForallSL u1 b1 t1, Tm_ForallSL u2 b2 t2 ->
      if eq_univ u1 u2
      && eq_tm b1.binder_ty b2.binder_ty
      then (
        let x = fresh g in
        assume (~(x `Set.mem` freevars t1));
        assume (~(x `Set.mem` freevars t2));
        let g' = push_binding g x b1.binder_ppname b1.binder_ty in
        let nx = b1.binder_ppname, x in
        let ext = check_slprop_equiv r g' (open_term_nv t1 nx) (open_term_nv t2 nx) in
        VE_Fa g x u1 b1 t1 t2 ext
      )
      else check_slprop_equiv_ext r g p q
    | Tm_Star p1 p2, Tm_Star q1 q2 ->
      let ext1 = check_slprop_equiv r g p1 q1 in
      let ext2 = check_slprop_equiv r g p2 q2 in
      VE_Ctxt g p1 p2 q1 q2 ext1 ext2
    | _ -> 
      check_slprop_equiv_ext r g p q
  )
  
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_Rewrite? t.term})

  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "check_rewrite" t.range g in
  let Tm_Rewrite {t1=p; t2=q; tac_opt} = t.term in
  let (| p, p_typing |) = check_slprop g p in
  let (| q, q_typing |) = check_slprop g q in

  let equiv_p_q =
    (* If we don't have a tactic, we just call the check_slprop_equiv
    function which mostly goes to SMT. Otherwise, we just ask the tactic
    and construct a slprop_equiv with it. *)
    match tac_opt with
    | None ->
      check_slprop_equiv t.range g p q
    | Some tac ->
      check_slprop_equiv_tac t.range g p q tac
  in
	let d = T_Rewrite _ p q p_typing equiv_p_q in
	prove_post_hint (try_frame_pre false pre_typing (match_comp_res_with_post_hint d post_hint) res_ppname) post_hint t.range
