module Pulse.Checker.While

module T = FStar.Tactics
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV
module Framing = Pulse.Checker.Framing
module Metatheory = Pulse.Typing.Metatheory

let while_cond_comp_typing (#g:env) (u:universe) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (Tm_ExistsSL u ty inv_body should_elim_false) Tm_VProp)
  : Metatheory.comp_typing_u g (comp_while_cond inv_body)
  = Metatheory.admit_comp_typing g (comp_while_cond inv_body)

let while_body_comp_typing (#g:env) (u:universe) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (Tm_ExistsSL u ty inv_body should_elim_false) Tm_VProp)
  : Metatheory.comp_typing_u g (comp_while_body inv_body)
  = Metatheory.admit_comp_typing g (comp_while_body inv_body)

#push-options "--ifuel 2 --z3rlimit_factor 4"
let check_while
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_While? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  let g = push_context "while loop" g in
  let Tm_While { invariant=inv; condition=cond; body } = t.term in
  let (| ex_inv, inv_typing |) =
    check_vprop (push_context "invariant" g)
                (Tm_ExistsSL u0 tm_bool inv should_elim_true)
  in
  match Framing.check_frameable pre_typing ex_inv with
  | Inr f -> T.raise (Framing_failure f)
  | Inl framing_token ->
    match ex_inv with
    | Tm_ExistsSL u ty inv _ ->
      if not (eq_tm ty tm_bool) ||
        not (eq_univ u u0)
      then T.fail "While loop invariant is exists but its witness type is not bool"
      else begin
        let while_cond_comp_typing = while_cond_comp_typing u ty inv inv_typing in
        let (| res_typing, cond_pre_typing, x, post_typing |) =
            Metatheory.(st_comp_typing_inversion (comp_typing_inversion while_cond_comp_typing))
        in
        let while_cond_hint
          : post_hint_for_env g
          = post_hint_from_comp_typing while_cond_comp_typing
        in
        let (| cond, cond_comp, cond_typing |) =
          check' allow_inst
                 (push_context "while condition" g)
                 cond
                 (comp_pre (comp_while_cond inv))
                 cond_pre_typing
                 (Some while_cond_hint)
        in
        if eq_comp cond_comp (comp_while_cond inv)
        then begin
          let while_body_comp_typing = while_body_comp_typing u ty inv inv_typing in
          let (| res_typing, body_pre_typing, x, post_typing |) = 
              Metatheory.(st_comp_typing_inversion (comp_typing_inversion while_body_comp_typing))
          in
          let while_post_hint
            : post_hint_for_env g
            = post_hint_from_comp_typing while_body_comp_typing
          in
          let (| body, body_comp, body_typing |) =
              check' allow_inst
                     (push_context "while body" g)
                     body
                     (comp_pre (comp_while_body inv))
                     body_pre_typing
                     (Some while_post_hint)
          in
          if eq_comp body_comp (comp_while_body inv)
          then let d = T_While g inv cond body inv_typing cond_typing body_typing in
               let (| c, st_d |) = Framing.apply_frame pre_typing d framing_token in
               repack (| c, st_d |) post_hint
          else 
            T.fail
              (Printf.sprintf "Could not prove the inferred type of the while body matches the annotation\n\
                                     Inferred type = %s\n\
                                     Annotated type = %s\n"
                                     (P.comp_to_string body_comp)
                                     (P.comp_to_string (comp_while_body inv)))
      end
      else T.fail 
(Printf.sprintf "Could not prove that the inferred type of the while condition matches the annotation\n\
                                 Inferred type = %s\n\
                                 Annotated type = %s\n"
                                 (P.comp_to_string cond_comp)
                                 (P.comp_to_string (comp_while_cond inv)))
                end
     | _ -> T.fail "Typechecked invariant is not an exists"
