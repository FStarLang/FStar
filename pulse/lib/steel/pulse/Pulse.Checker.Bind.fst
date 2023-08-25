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

  let Tm_Bind { binder; head=e1; body=e2 } = t.term in

  let (| x, g1, _, (| ctxt', ctxt'_typing |), k1 |) =
    let r = check g ctxt ctxt_typing None binder.binder_ppname e1 in
    (* Check that the type matches the annotation, if any *)
    let ty = binder.binder_ty in
    begin match ty.t with
    | Tm_Unknown -> ()
    | _ ->
      let (| ty, _, _ |) = check_tot_term g ty in //elaborate it first
      let (| _, _, (| _, t, _ |), _, _ |) = r in
      // TODO: once we have the rename operation then we should
      // ditch this check and just elaborate the bind
      //   let x : ty = stapp in ...
      // to
      //   let x0 = stapp in
      //   let x : t = x0 in
      //   rename x0 x; ...
      // to leverage the pure case
      if not (eq_tm ty t) then
        fail g (Some e1.range)
          (Printf.sprintf "Type mismatch: expected %s, got %s" (P.term_to_string ty) (P.term_to_string t))
    end;
    r
  in
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

  let g = Pulse.Typing.Env.push_context g "check_tot_bind" t.range in

  if None? post_hint
  then fail g (Some t.range) "check_tot_bind: post hint is not set, please add an annotation";

  // let Tm_TotBind { head=e1; body=e2 } = t.term in
  // let (| e1, eff1, t1, (| u1, _t1_typing |), e1_typing |) =
  //   check_term_and_type g e1 in
  let Tm_TotBind { binder=b; head=e1; body=e2 } = t.term in
  let (| e1, eff1, t1, (| u1, _t1_typing |) , e1_typing |) =
    (* If there's an annotated type for e1 in the binder, we check it at
    that type. Otherwise we just call check_term_and_type and infer. *)
    let ty = b.binder_ty in
    match ty.t with
    | Tm_Unknown ->
      check_term_and_type g e1
    | _ ->
      let (| ty, _, _ |) = check_tot_term g ty in //elaborate it first
      let (| u1, ty_typing |) = check_universe g ty in
      let (| e1, eff1, e1_typing |) = check_term_with_expected_type g e1 ty in
      let ty_typing : universe_of g ty u1 = ty_typing in
      let e1_typing : typing g e1 eff1 ty = e1_typing in
      (| e1, eff1, ty, (| u1, ty_typing |), e1_typing |)
        <: (t:term & eff:T.tot_or_ghost & ty:term & (u:universe & universe_of g ty u) & typing g t eff ty)
        (* ^ Need this annotation *)
  in
  let t1 =
    let b = {binder_ty=t1;binder_ppname=ppname_default} in
    let eq_tm = mk_eq2 u1 t1 (null_bvar 0) e1 in
    tm_refine b eq_tm in

  // THIS IS WASTEFUL, CHECKING e1 MULTIPLE TIMES
  let (| e1, e1_typing |) =
    check_term_with_expected_type_and_effect g e1 eff1 t1 in

  let x = fresh g in

  let b = { b with binder_ty = t1 } in
  let k = continuation_elaborator_with_let pre_typing b e1_typing (ppname_default, x) in

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
