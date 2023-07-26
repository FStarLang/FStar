module Pulse.Checker.While

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory

let while_cond_comp_typing (#g:env) (u:universe) (x:ppname) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (tm_exists_sl u (as_binder ty) inv_body) tm_vprop)
  : Metatheory.comp_typing_u g (comp_while_cond x inv_body)
  = Metatheory.admit_comp_typing g (comp_while_cond x inv_body)

let while_body_comp_typing (#g:env) (u:universe) (x:ppname) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (tm_exists_sl u (as_binder ty) inv_body) tm_vprop)
  : Metatheory.comp_typing_u g (comp_while_body x inv_body)
  = Metatheory.admit_comp_typing g (comp_while_body x inv_body)

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 4"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_While? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "while loop" t.range g in
  let Tm_While { invariant=inv; condition=cond; body; condition_var } = t.term in
  let (| ex_inv, inv_typing |) =
    check_vprop (push_context "invariant" (term_range inv) g) 
                (tm_exists_sl u0 { binder_ppname=condition_var; binder_ty=tm_bool } inv)
  in

  if not (Tm_ExistsSL? ex_inv.t)
  then fail g (Some t.range)
         (Printf.sprintf "check_while: typechecked invariant %s is not an existential"
            (P.term_to_string ex_inv));

  let Tm_ExistsSL u {binder_ppname=nm; binder_ty=ty} inv = ex_inv.t in

  if not (eq_tm ty tm_bool) ||
     not (eq_univ u u0)
  then fail g (Some nm.range)
         (Printf.sprintf "While loop invariant exists but its witness type is %s, expected bool"
            (P.term_to_string ty));

  let while_cond_comp_typing = while_cond_comp_typing u nm ty inv inv_typing in
  let (| res_typing, cond_pre_typing, x, post_typing |) =
    Metatheory.(st_comp_typing_inversion (comp_typing_inversion while_cond_comp_typing))
  in
  let while_cond_hint : post_hint_for_env g =
    post_hint_from_comp_typing while_cond_comp_typing
  in

  let (| cond, cond_comp, cond_typing |) =
    let r = check
      (push_context "while condition" cond.range g)
      (comp_pre (comp_while_cond nm inv))
      cond_pre_typing
      (Some while_cond_hint)
      (mk_ppname_no_range "_while_c")
      cond in
    apply_checker_result_k r
  in
  if eq_comp cond_comp (comp_while_cond nm inv)
  then begin
    let while_body_comp_typing = while_body_comp_typing u nm ty inv inv_typing in
    let (| res_typing, body_pre_typing, x, post_typing |) = 
      Metatheory.(st_comp_typing_inversion (comp_typing_inversion while_body_comp_typing))
    in
    let while_post_hint : post_hint_for_env g =
      post_hint_from_comp_typing while_body_comp_typing
    in
    let (| body, body_comp, body_typing |) =
      let r = check
        (push_context "while body" body.range g)
        (comp_pre (comp_while_body nm inv))
        body_pre_typing
        (Some while_post_hint)
        (mk_ppname_no_range "_while_b")
        body in
      apply_checker_result_k r in
    if eq_comp body_comp (comp_while_body nm inv)
    then
      let d = T_While g inv cond body inv_typing cond_typing body_typing in
      prove_post_hint (try_frame_pre pre_typing d res_ppname) post_hint t.range
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
