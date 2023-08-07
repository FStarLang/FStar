module Pulse.Checker.Bind

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Base
open Pulse.Checker.Pure
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory
module PS = Pulse.Checker.Prover.Substs

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let check_bind
  (g:env)
  (ctxt:vprop)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term {Tm_Bind? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g ctxt post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_bind" t.range in

  debug_prover g (fun _ ->
    Printf.sprintf "checking bind:\n%s\n" (P.st_term_to_string t));
 
  if None? post_hint
  then fail g (Some t.range) "check_bind: post hint is not set, please add an annotation";

  let Tm_Bind { binder; head=e1; body=e2} = t.term in

  let (| x, g1, _, (| ctxt', ctxt'_typing |), k1 |) =
    check g ctxt ctxt_typing None binder.binder_ppname e1 in
  let d : st_typing_in_ctxt g1 ctxt' post_hint =
    let ppname = mk_ppname_no_range "_bind_c" in
    let r =
      check g1 ctxt' ctxt'_typing post_hint ppname (open_st_term_nv e2 (binder.binder_ppname, x)) in
      apply_checker_result_k #_ #_ #(Some?.v post_hint) r ppname in
  let d : st_typing_in_ctxt g ctxt post_hint = k1 post_hint d in

  checker_result_for_st_typing d res_ppname

let check_tot_bind
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_TotBind? t.term })
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_bind" t.range in

  if None? post_hint
  then fail g (Some t.range) "check_tot_bind: post hint is not set, please add an annotation";

  let Tm_TotBind { head=e1; body=e2 } = t.term in
  let (| e1, u1, t1, _t1_typing, e1_typing |) = check_tot_term_and_type g e1 in
  let t1 =
    let b = {binder_ty=t1;binder_ppname=ppname_default} in
    let eq_tm = mk_eq2 u1 t1 (null_bvar 0) e1 in
    tm_refine b eq_tm in

  // THIS IS WASTEFUL, CHECKING e1 MULTIPLE TIMES
  let (| e1, e1_typing |) =
    check_tot_term_with_expected_type g e1 t1 in

  let x = fresh g in

  let k = continuation_elaborator_with_tot_bind pre_typing e1_typing (ppname_default, x) in

  let px = v_as_nv x in
  let g' = push_binding g x (fst px) t1 in
  let pre_typing' : tot_typing g' pre tm_vprop =
    Metatheory.tot_typing_weakening_single pre_typing x t1 in
  let d =
    let ppname = mk_ppname_no_range "_tbind_c" in
    let r = check g' pre pre_typing' post_hint ppname (open_st_term_nv e2 px) in
    apply_checker_result_k #_ #_ #(Some?.v post_hint) r ppname in
  let d = k post_hint d in
  checker_result_for_st_typing d res_ppname
