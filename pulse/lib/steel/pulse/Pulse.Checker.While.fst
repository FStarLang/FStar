module Pulse.Checker.While

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Prover

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV
module Metatheory = Pulse.Typing.Metatheory
module RU = Pulse.RuntimeUtils

let while_cond_comp_typing (#g:env) (u:universe) (x:ppname) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (tm_exists_sl u (as_binder ty) inv_body) tm_vprop)
  : Metatheory.comp_typing_u g (comp_while_cond x inv_body)
  = Metatheory.admit_comp_typing g (comp_while_cond x inv_body)

let while_body_comp_typing (#g:env) (u:universe) (x:ppname) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (tm_exists_sl u (as_binder ty) inv_body) tm_vprop)
  : Metatheory.comp_typing_u g (comp_while_body x inv_body)
  = Metatheory.admit_comp_typing g (comp_while_body x inv_body)

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 4"
let check_while
  (g:env)
  (t:st_term{Tm_While? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "while loop" t.range g in
  let Tm_While { invariant=inv; condition=cond; body; condition_var } = t.term in
  let (| ex_inv, inv_typing |) =
    check_vprop (push_context "invariant" (term_range inv) g) 
                (tm_exists_sl u0 { binder_ppname=condition_var; binder_ty=tm_bool } inv)
  in

  if not (Tm_ExistsSL? ex_inv.t)
  then fail g None "Typechecked invariant is not an exists";

  let Tm_ExistsSL u {binder_ppname=nm; binder_ty=ty} inv = ex_inv.t in

  if not (eq_tm ty tm_bool) ||
     not (eq_univ u u0)
  then fail g (Some nm.range) "While loop invariant exists but its witness type is not bool";

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
        body in
      apply_checker_result_k r in
    if eq_comp body_comp (comp_while_body nm inv)
    then
      let d = T_While g inv cond body inv_typing cond_typing body_typing in
      repack (try_frame_pre pre_typing d) post_hint t.range
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
