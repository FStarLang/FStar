module Pulse.Checker.Par

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.Checker.Comp

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module RT = FStar.Reflection.Typing
module MT = Pulse.Typing.Metatheory

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_Par? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "check_par" t.range g in
  let Tm_Par {pre1=preL; body1=eL; post1=postL;
              pre2=preR; body2=eR; post2=postR} = t.term in
  let (| preL, preL_typing |) =
    check_term_with_expected_type g preL tm_vprop in
  let (| preR, preR_typing |) =
    check_term_with_expected_type g preR tm_vprop in

  let postL_hint = intro_post_hint g None None postL in

  let (| eL, cL, eL_typing |) =
    let ppname = mk_ppname_no_range "_par_l" in
    let r = 
      check g preL (E preL_typing) (Some postL_hint) ppname eL in
    apply_checker_result_k r ppname in

  if C_ST? cL
  then
    let cL_typing = MT.st_typing_correctness eL_typing in
    let postR_hint = intro_post_hint g None None postR in
    let (| eR, cR, eR_typing |) =
      let ppname = mk_ppname_no_range "_par_r" in
      let r =
        check g preR (E preR_typing) (Some postR_hint) ppname eR  in
      apply_checker_result_k r ppname in

    if C_ST? cR && eq_univ (comp_u cL) (comp_u cR)
    then
      let cR_typing = MT.st_typing_correctness eR_typing in
      let x = fresh g in
      let d = T_Par _ _ _ _ _ x cL_typing cR_typing eL_typing eR_typing in
      prove_post_hint (try_frame_pre pre_typing d res_ppname) post_hint t.range
    else fail g (Some eR.range)
           (Printf.sprintf "check_par: right computation is not stt (%s)" (P.comp_to_string cR))
  else fail g (Some eL.range)
           (Printf.sprintf "check_par: left computation is not stt (%s)" (P.comp_to_string cL))
