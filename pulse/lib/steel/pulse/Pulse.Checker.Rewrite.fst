module Pulse.Checker.Rewrite

module T = FStar.Tactics
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

module FV = Pulse.Typing.FV

let check_rewrite
  (g:env)
  (t:st_term{Tm_Rewrite? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint) =
  let g = push_context "check_rewrite" t.range g in
  let Tm_Rewrite {t1=p; t2=q} = t.term in
  let (| p, p_typing |) = check_vprop g p in
  let (| q, q_typing |) = check_vprop g q in
  let equiv_p_q =
      if eq_tm p q
      then VE_Refl g p
      else match T.check_equiv (elab_env g) (elab_term p) (elab_term q) with
           | None, issues -> 
             T.fail (Printf.sprintf "rewrite: p and q elabs are not equiv\n%s" 
                          (Pulse.Checker.Pure.print_issues g issues))
           | Some token, _ -> VE_Ext g p q token in
	     let d = T_Rewrite _ p q p_typing equiv_p_q in
	     repack (Pulse.Checker.Common.try_frame_pre pre_typing d) post_hint
