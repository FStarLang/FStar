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

module Pulse.Checker.While

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.Checker.ImpureSpec

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory
module RU = Pulse.RuntimeUtils

let while_cond_comp_typing (#g:env) (u:universe) (x:ppname) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (tm_exists_sl u (as_binder ty) inv_body) tm_slprop)
  : Dv (comp_typing_u g (comp_while_cond x inv_body))
  = Metatheory.admit_comp_typing g (comp_while_cond x inv_body)

let while_body_comp_typing (#g:env) (u:universe) (x:ppname) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (tm_exists_sl u (as_binder ty) inv_body) tm_slprop)
  : Dv (comp_typing_u g (comp_while_body x inv_body))
  = Metatheory.admit_comp_typing g (comp_while_body x inv_body)

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 8"
#restart-solver
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_While? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "while loop" t.range g in
  let Tm_While { invariant=inv; condition=cond; body; condition_var } = t.term in
  let (| ex_inv, inv_typing |) =
    purify_and_check_spec (push_context "invariant" (term_range inv) g) 
                { ctxt_now = pre; ctxt_old = Some pre }
                (tm_exists_sl u0 (mk_binder_ppname tm_bool condition_var) inv)
  in
  let ex_inv_v = inspect_term ex_inv in
  if not (Tm_ExistsSL? ex_inv_v)
  then fail g (Some t.range)
         (Printf.sprintf "check_while: typechecked invariant %s is not an existential"
            (P.term_to_string ex_inv));

  let Tm_ExistsSL u {binder_ppname=nm; binder_ty=ty} inv = ex_inv_v in

  if not (eq_tm ty tm_bool) ||
     not (eq_univ u u0)
  then fail g (Some nm.range)
         (Printf.sprintf "While loop invariant exists but its witness type is %s, expected bool"
            (P.term_to_string ty));

  let while_cond_comp_typing = while_cond_comp_typing u nm ty inv inv_typing in
  let (| res_typing, cond_pre_typing, x, post_typing |) =
    Metatheory.(st_comp_typing_inversion (fst <| comp_typing_inversion while_cond_comp_typing))
  in
  let while_cond_hint : post_hint_for_env g =
    post_hint_from_comp_typing while_cond_comp_typing
  in

  let (| cond, cond_comp, cond_typing |) =
    let ppname = mk_ppname_no_range "_while_c" in
    let r = check
      (push_context "check_while_condition" cond.range g)
      (comp_pre (comp_while_cond nm inv))
      (coerce_eq () cond_pre_typing) // why is coerce_eq needed !?
      (PostHint while_cond_hint)
      ppname
      cond in
    apply_checker_result_k r ppname
  in
  if eq_comp cond_comp (comp_while_cond nm inv)
  then begin
    let while_body_comp_typing = while_body_comp_typing u nm ty inv inv_typing in
    let (| res_typing, body_pre_typing, x, post_typing |) = 
      Metatheory.(st_comp_typing_inversion (fst <| comp_typing_inversion while_body_comp_typing))
    in
    let while_post_hint : post_hint_for_env g =
      post_hint_from_comp_typing while_body_comp_typing
    in
    debug g (fun _ -> 
      Printf.sprintf "while_body post_hint: %s\n"
        (Pulse.Syntax.Printer.term_to_string while_post_hint.post)
    );
    let (| body, body_comp, body_typing |) =
      let ppname = mk_ppname_no_range "_while_b" in
      let r = check
        (push_context "check_while_body" body.range g)
        (comp_pre (comp_while_body nm inv))
        (coerce_eq () body_pre_typing) // why is coerce_eq needed !?
        (PostHint while_post_hint)
        ppname
        body in
      apply_checker_result_k r ppname in
    if eq_comp body_comp (comp_while_body nm inv)
    then
      let d = T_While g inv cond body inv_typing cond_typing body_typing in
      let (| c,d |) = match_comp_res_with_post_hint d post_hint in
      prove_post_hint (try_frame_pre false pre_typing (|_,c,d|) res_ppname) post_hint t.range
    else fail g None
          (Printf.sprintf "Could not prove the inferred type of the while body matches the annotation\n\
                           Inferred type = %s\n\
                           Annotated type = %s\n"
                           (P.comp_to_string body_comp)
                           (P.comp_to_string (comp_while_body nm inv)))
  end
  else fail g None
         (Printf.sprintf "Could not prove that the inferred type of the while condition matches the annotation\n\
                          Inferred type = %s\n\
                          Annotated type = %s\n"
                          (P.comp_to_string cond_comp)
                          (P.comp_to_string (comp_while_cond nm inv)))
#pop-options

let empty_env g = mk_env (fstar_env g)
let push_empty_env_idem (g:env) : Lemma (push_env g (empty_env g) == g)[SMTPat (push_env g (empty_env g))] = admit()
let body_typing_subst_true #g #x #post (_:tot_typing (push_binding g x ppname_default tm_bool) (open_term post x) tm_slprop)
: tot_typing g (open_term' post tm_true 0) tm_slprop = admit()
let body_typing_ex #g #x #post (_:tot_typing (push_binding g x ppname_default tm_bool) (open_term post x) tm_slprop)
: tot_typing g (tm_exists_sl u0 (as_binder tm_bool) post) tm_slprop = admit()
let unit_typing g : universe_of g tm_unit u0 = admit()

let inv_typing_weakening (#g:env) (#inv:slprop) (inv_typing:tot_typing g inv tm_slprop) 
: (x:FStar.Ghost.erased var {fresh_wrt x g (freevars inv)} & tot_typing (push_binding g x ppname_default tm_unit) (open_term inv x) tm_slprop)
 = let x : (x:FStar.Ghost.erased var {fresh_wrt x g (freevars inv)}) = RU.magic () in
   let tt : tot_typing (push_binding g x ppname_default tm_unit) (open_term inv x) tm_slprop = RU.magic () in
   (|x, tt|)

let inv_as_post_hint (#g:env) (#inv:slprop) (inv_typing:tot_typing g inv tm_slprop) 
: T.Tac (ph:post_hint_for_env g { ph.post == inv /\ ph.ret_ty == tm_unit /\ ph.u == u0 /\ ph.effect_annot == EffectAnnotSTT })
= let (| x, post_typing_src |) = inv_typing_weakening inv_typing in
  { g; effect_annot=EffectAnnotSTT; effect_annot_typing=();
    ret_ty=tm_unit; u=u0; ty_typing=unit_typing g; post=inv;
    x; post_typing_src; post_typing=RU.magic() }

let tm_l_true : term = FStar.Reflection.V2.Formula.(formula_as_term True_)
let tm_l_or (a b: term) : term = FStar.Reflection.V2.Formula.(formula_as_term (Or a b))
let tm_l_and (a b: term) : term = FStar.Reflection.V2.Formula.(formula_as_term (And a b))

let loop_requires_marker_lid = Pulse.Reflection.Util.mk_pulse_lib_core_lid "loop_requires_marker"
let mk_loop_requires_marker p = R.pack_ln (R.Tv_App (R.pack_ln (R.Tv_FVar (R.pack_fv loop_requires_marker_lid))) (p, R.Q_Explicit))

let rec subst_loop_requires_marker (t: term) (v: term -> term) : Dv term =
  match R.inspect_ln t with
  | R.Tv_App hd arg -> (
    let default () : Dv term =
      R.pack_ln (R.Tv_App (subst_loop_requires_marker hd v) (subst_loop_requires_marker (fst arg) v, snd arg)) in
    match R.inspect_ln hd with
    | R.Tv_FVar fv ->
      if R.inspect_fv fv = loop_requires_marker_lid then
        v (fst arg)
      else
        default ()
    | _ -> default ()
  )
  | R.Tv_Abs b body ->
    R.pack_ln (R.Tv_Abs b (subst_loop_requires_marker body v))
  | _ -> t

let subst_loop_requires_marker_with_true t = subst_loop_requires_marker t fun _ -> tm_l_true
let reduce_loop_requires_marker t = subst_loop_requires_marker t id

(*
The desugaring of while loops into the unelaborated syntax is awful and hacky.

while (cond)
  invariant inv
  requires pre
  ensures post
{
  body
}

is represented as

Tm_ForwardJumpLabel {
  lbl = "_break";
  body = Tm_NuWhile {
    invariant = inv;
    loop_requires = pre;
    condition = cond;
    body = Tm_ForwardJumpLabel {
      lbl = "_continue";
      body = body; 
    };
  };
  post = C_ST {
    post = tm_pure post;
  };
}

The continue inside the body is nice and modular (and we don't need to anything special for it).
But when the Pulse.Checker module sees a while loop inside a forward jump label,
it directly calls this checker and pass the post as the loop_ensures argument here.

*)

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 72"
module RT = FStar.Reflection.Typing

#push-options "--fuel 1 --ifuel 1"
let rec compute_meas_infos (g:env) (pre:term) (ms: list term)
  : T.Tac (list (term & term & universe))
  = match ms with
    | [] -> []
    | m :: rest ->
      let m' = purify_term g { ctxt_now = pre; ctxt_old = Some pre } m in
      let (| _, _, ty, (| u, _ |), _ |) = compute_term_type_and_u g m' in
      (m, ty, u) :: compute_meas_infos g pre rest

let rec build_tuple_info (infos: list (term & term & universe))
  : T.Tac (term & term & universe & (term -> term -> term))
  = match infos with
    | [(m, ty, u)] -> (m, ty, u, mk_precedes u ty)
    | (m, ty, u) :: rest ->
      let (m_rest, ty_rest, u_rest, mk_dec_rest) = build_tuple_info rest in
      let ty_tup = mk_tuple2 u u_rest ty ty_rest in
      let m_tup = mk_mktuple2 u u_rest ty ty_rest m m_rest in
      let mk_dec_tup (new_m: term) (old_m: term) : term =
        let new_hd = mk_fst u u_rest ty ty_rest new_m in
        let old_hd = mk_fst u u_rest ty ty_rest old_m in
        let new_tl = mk_snd u u_rest ty ty_rest new_m in
        let old_tl = mk_snd u u_rest ty ty_rest old_m in
        let precedes_hd = mk_precedes u ty new_hd old_hd in
        let eq_hd = mk_eq2 u ty new_hd old_hd in
        let rest_dec = mk_dec_rest new_tl old_tl in
        tm_l_or precedes_hd (tm_l_and eq_hd rest_dec)
      in
      (m_tup, ty_tup, u, mk_dec_tup)
    | _ -> (unit_const, tm_unit, u0, mk_precedes u0 tm_unit)
#pop-options

let check_nuwhile
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g {~ (PostHint? post_hint) })
  (res_ppname:ppname)
  (t:st_term{Tm_NuWhile? t.term})
  (breaklblx: var { freshv g breaklblx })
  (loop_ensures: option term)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "nu while loop" t.range g in
  let Tm_NuWhile { invariant=inv; loop_requires; meas; condition=cond; body } = t.term in

  (*
  We need to compute three slprops here:
   - The invariant, which is true before the loop and at the end of the body.
   - The postcondition, which is true after the condition and immediately after
     the end of the loop (but before the label).
   - The break condition, which is true after the break label.
  
  The postcondition is computed from the invariant by inferring a postcondition
  for `cond` ensuring `pure (result == x)`.  The break condition is also
  computed from the invariant by inferring a postcondition for `cond` but
  ensuring `pure ((loop_requires /\ result == false) \/ loop_ensures)`.
  
  One problem is that loop_requires should be part of the invariant and
  postcondition, but not of the break condition (except for the part guarded by
  `result == false`).  Therefore we mark the loop_requires in the invariant with
  the `loop_requires_marker` identity function, and replace that subterm with
  `True` in the break condition.

  If a decreases clause is present, we tack `pure (x == meas)` onto the
  invariant, where x is a fresh erased variable. This allows the checker to
  track the termination measure across loop iterations.
  *)

  let inv =
    if loop_requires `eq_tm` tm_l_true then inv else
    (inv `tm_star` tm_pure (mk_loop_requires_marker loop_requires)) in
  let x_meas: nvar = mk_ppname_no_range "meas", fresh g in
  let u_meas, ty_meas, meas_val, is_tot, mk_dec =
    match meas with
    | [] -> u0, tm_unit, unit_const, false, mk_precedes u0 tm_unit
    | [meas] ->
      let meas' = purify_term g { ctxt_now = pre; ctxt_old = Some pre } meas in
      let (| _, _, ty, (| u, _ |), _ |) = compute_term_type_and_u g meas' in
      u, ty, meas, true, mk_precedes u ty
    | _ ->
      let meas_infos = compute_meas_infos g pre meas in
      let (meas_val, _ty_approx, _u_approx, mk_dec) = build_tuple_info meas_infos in
      let meas_val' = purify_term g { ctxt_now = pre; ctxt_old = Some pre } meas_val in
      let (| _, _, ty, (| u, _ |), _ |) = compute_term_type_and_u g meas_val' in
      u, ty, meas_val, true, mk_dec
  in
  let dec_formula = mk_dec (tm_bvar {bv_index=0;bv_ppname=fst x_meas}) (term_of_nvar x_meas) in
  let inv_range = term_range inv in
  let g_meas = push_binding g (snd x_meas) (fst x_meas) ty_meas in
  let inv = dfst <|
    purify_and_check_spec (push_context "invariant" inv_range g_meas)
      { ctxt_now = pre; ctxt_old = Some pre }
      (inv `tm_star` tm_pure (mk_eq2 u_meas ty_meas (term_of_nvar x_meas) meas_val))
  in
  let loop_pre0 = tm_exists_sl u_meas (as_binder ty_meas) (close_term inv (snd x_meas)) in
  let (| g0, remaining, k |) = Pulse.Checker.Prover.prove t.range g pre loop_pre0 false in
  assume freshv g0 (snd x_meas);
  let g1 = push_binding g0 (snd x_meas) (fst x_meas) ty_meas in
  let inv = tm_star (RU.deep_compress_safe inv) remaining in
  let inv_typing : tot_typing g1 inv tm_slprop = RU.magic () in
  let res_cond : checker_result_t g1 inv (TypeHint tm_bool) =
    check (push_context "check_while_condition" cond.range g1) inv inv_typing (TypeHint tm_bool) ppname_default cond in
  let (| post_cond, r_cond |) : (ph:post_hint_for_env g1 & Pulse.Typing.Combinators.st_typing_in_ctxt g1 inv (PostHint ph)) =
    let res_cond = retype_checker_result NoHint res_cond in
    let ph = Pulse.JoinComp.infer_post res_cond in
    let r_cond = Pulse.Checker.Prover.prove_post_hint res_cond (PostHint ph) cond.range in
    (| ph, apply_checker_result_k r_cond ppname_default |)
  in
  let (| cond, comp_cond, cond_typing |) = r_cond in
  if not (T.term_eq post_cond.ret_ty tm_bool)
  || not (T.univ_eq post_cond.u u0)
  then T.fail "Expected while condition to return a bool";

  assume freshv g1 breaklblx;
  let (| break_pred, break_typ |) : t:term & tot_typing g0 t tm_slprop =
    match loop_ensures with
    | Some loop_ensures ->
      let (| x_cond, g1', (| _, _, t_typ |), (| cond_post, _ |), k |) = res_cond in
      let loop_ensures = 
        (mk_eq2 u0 tm_bool (term_of_nvar (ppname_default, x_cond)) tm_false
            `tm_l_and` loop_requires)
          `tm_l_or` loop_ensures in
      let loop_ensures = purify_term g1' { ctxt_now = cond_post; ctxt_old = Some pre } loop_ensures in
      let loop_ensures = RU.beta_lax (elab_env g1') loop_ensures in
      let loop_ensures = RU.deep_compress_safe loop_ensures in
      let (| loop_ensures, loop_ensures_typ |) = check_tot_term g1' loop_ensures tm_prop in
      let loop_ensures = cond_post `tm_star` tm_pure loop_ensures in
      let y = fresh g1' in
      let g1'' = push_binding g1' y ppname_default tm_unit in
      assert g1 `env_extends` g0;
      assert g1' `env_extends` g1;
      assert g1'' `env_extends` g1';
      let loop_ensures_typ: tot_typing g1'' loop_ensures tm_slprop = RU.magic () in
      let unit_typ: universe_of g1'' tm_unit u0 = RU.magic () in
      let loop_ensures = Pulse.JoinComp.infer_post' g0 g1'' y unit_typ loop_ensures_typ in
      let loop_ensures = subst_loop_requires_marker_with_true loop_ensures.post in
      let loop_ensures = open_term' loop_ensures unit_const 0 in
      let loop_ensures_typ: tot_typing g0 loop_ensures tm_slprop = RU.magic () in
      (| loop_ensures, loop_ensures_typ |)
    | None ->
      let t: term = tm_exists_sl u_meas (as_binder ty_meas) (close_term (open_term' post_cond.post tm_false 0) (snd x_meas)) in
      let typ: tot_typing g0 t tm_slprop = RU.magic () in
      (| t, typ |)
  in
  let break_lbl_c = C_ST {
    u = u0;
    res = tm_unit;
    pre = break_pred;
    post = tm_is_unreachable;
  } in
  let breaklbln = { name = T.seal "_break"; range = t.range } in

  assume freshv g0 breaklblx;
  let g1' = push_goto g0 breaklblx breaklbln break_lbl_c in
  assume freshv g1' (snd x_meas);
  let g2 = push_binding g1' (snd x_meas) (fst x_meas) ty_meas in
  
  // lift post_cond across "g2 `env_extends` g1"
  let post_cond : post_hint_for_env g2 = assume post_hint_for_env_p g2 post_cond; post_cond in
  let r_cond : Pulse.Typing.Combinators.st_typing_in_ctxt g2 inv (PostHint post_cond) =
    let (| t, c, typ |) = r_cond in
    let typ : st_typing g2 t c = RU.magic () in
    (| t, c, typ |) in

  let body_pre_open = post_cond.post in
  let body_post_typing : tot_typing g2 (comp_post (comp_nuwhile_body u_meas ty_meas is_tot dec_formula x_meas inv body_pre_open)) tm_slprop = RU.magic () in
  let body_ph : post_hint_for_env g2 = inv_as_post_hint body_post_typing in
  assert body_ph.ret_ty == tm_unit;
  let x = fresh g2 in
  assume (x == Ghost.reveal post_cond.x);
  let body_open_pre_typing : tot_typing (push_binding g2 x ppname_default tm_bool) (open_term body_pre_open x) tm_slprop =
    RU.magic () in // post_cond.post_typing_src
  let body_pre_typing = body_typing_subst_true body_open_pre_typing in
  let r_body = 
    check 
      (push_context "check_while_body" body.range g2) 
      _ body_pre_typing (PostHint body_ph) ppname_default body
  in
  let (| cond, comp_cond, cond_typing |) = r_cond in
  let (| body, comp_body, body_typing |) = apply_checker_result_k r_body ppname_default in
  assert (comp_cond == (comp_nuwhile_cond inv body_pre_open));
  assert (comp_post comp_body == comp_post (comp_nuwhile_body u_meas ty_meas is_tot dec_formula x_meas inv body_pre_open));
  assert (comp_pre comp_body == comp_pre (comp_nuwhile_body u_meas ty_meas is_tot dec_formula x_meas inv body_pre_open));
  assert (comp_u comp_body == comp_u (comp_nuwhile_body u_meas ty_meas is_tot dec_formula x_meas inv body_pre_open));
  assert (comp_res comp_body == comp_res (comp_nuwhile_body u_meas ty_meas is_tot dec_formula x_meas inv body_pre_open));
  assert (comp_body == comp_nuwhile_body u_meas ty_meas is_tot dec_formula x_meas inv body_pre_open);
  let inv_typing2 : tot_typing g2 inv tm_slprop = RU.magic () in

  let while = wtag (Some STT) (Tm_NuWhile { invariant = inv; loop_requires = tm_unknown; meas = []; condition = cond; body }) in
  let typ_meas: universe_of g1' ty_meas u_meas = RU.magic () in
  assume ~(snd x_meas `Set.mem` freevars_st cond);
  assume ~(snd x_meas `Set.mem` freevars_st body);
  let d: st_typing g1' while (comp_nuwhile u_meas ty_meas x_meas inv body_pre_open) =
    let h = RU.magic () in
    T_NuWhile g1' inv body_pre_open cond body
      u_meas ty_meas typ_meas is_tot dec_formula
      x_meas g2
      inv_typing2 h cond_typing body_typing
    in
  let C_ST cst = comp_nuwhile u_meas ty_meas x_meas inv body_pre_open in
  let loop_pre = tm_exists_sl u_meas (as_binder ty_meas) (close_term inv (snd x_meas)) in
  assert comp_pre (comp_nuwhile u_meas ty_meas x_meas inv body_pre_open) == loop_pre;
  let d_st : Pulse.Typing.Combinators.st_typing_in_ctxt g1' loop_pre NoHint = (| _, _, d |) in
  let res = checker_result_for_st_typing d_st ppname_default in
  assume (fresh_wrt x g0 (freevars break_pred));
  let post_hint_for_while : post_hint_for_env g0 = {
      g=g0;
      effect_annot=EffectAnnotSTT;
      effect_annot_typing=();
      ret_ty=RT.unit_ty;
      u=u_zero;
      ty_typing=RU.magic(); //unit typing
      post=break_pred;
      x;
      post_typing_src=RU.magic(); //from inv typing and body_open_pre_typing
      post_typing=RU.magic()
    }
  in
  let res = prove_post_hint res (PostHint post_hint_for_while) t.range in
  let (| while, while_comp, while_d |) = apply_checker_result_k res ppname_default in
  assert post_hint_for_while.post == break_pred;
  assert post_hint_for_while.u == u0;
  assert post_hint_for_while.ret_ty == tm_unit;
  assert comp_pre while_comp == loop_pre;
  assert comp_post while_comp == break_pred;
  assert comp_u while_comp == u0;
  assert comp_res while_comp == tm_unit;

  assume open_st_term_nv (close_st_term while breaklblx) (breaklbln, breaklblx) == while;
  let fjl = wtag (Some (ctag_of_comp_st while_comp))
    (Tm_ForwardJumpLabel { lbl = breaklbln; body = close_st_term while breaklblx; post = while_comp }) in
  admit ();
  assert break_lbl_c == goto_comp_of_block_comp while_comp;
  let fjl_d: st_typing g0 fjl while_comp =
    T_ForwardJumpLabel g0 (breaklbln, breaklblx) (close_st_term while breaklblx) while_comp while_d in

  let d_st: Pulse.Typing.Combinators.st_typing_in_ctxt g0 loop_pre (TypeHint tm_unit) = (| _, _, fjl_d |) in
  let d_st: Pulse.Typing.Combinators.st_typing_in_ctxt g0 loop_pre0 (TypeHint tm_unit) =
    let (| t, c, _ |) = d_st in
    let c = with_st_comp c { st_comp_of_comp c with pre = loop_pre0 } in
    let typ : st_typing g0 t c = RU.magic () in
    (| t, c, typ |) in

  let d_st : Pulse.Typing.Combinators.st_typing_in_ctxt g pre NoHint = k NoHint d_st in
  let res = checker_result_for_st_typing d_st ppname_default in
  let res = retype_checker_result #_ #_ #NoHint post_hint res in
  res

#pop-options