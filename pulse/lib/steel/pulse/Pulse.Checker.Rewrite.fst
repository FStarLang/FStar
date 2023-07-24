module Pulse.Checker.Rewrite

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV

let check_rewrite
  (g:env)
  (t:st_term{Tm_Rewrite? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)

  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "check_rewrite" t.range g in
  let Tm_Rewrite {t1=p; t2=q} = t.term in
  let (| p, p_typing |) = check_vprop g p in
  let (| q, q_typing |) = check_vprop g q in
  let equiv_p_q =
      if eq_tm p q
      then VE_Refl g p
      else let elab_p = elab_term p in
           let elab_q = elab_term q in
           let res, issues = T.check_equiv (elab_env g) elab_p elab_q in
           T.log_issues issues;
           match res with
           | None -> 
             fail g (Some t.range)
                    (Printf.sprintf "rewrite: could not prove equality of %s and %s\nElaborations: %s and %s\n" 
                           (P.term_to_string p)
                           (P.term_to_string q)
                           (T.term_to_string elab_p)
                           (T.term_to_string elab_q))
           | Some token ->
            VE_Ext g p q token in
	let d = T_Rewrite _ p q p_typing equiv_p_q in
	repack (try_frame_pre pre_typing d) post_hint t.range
