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

module T = FStar.Tactics.V2
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

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 8"
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
    check_slprop (push_context "invariant" (term_range inv) g) 
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
      cond_pre_typing
      (Some while_cond_hint)
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
        body_pre_typing
        (Some while_post_hint)
        ppname
        body in
      apply_checker_result_k r ppname in
    if eq_comp body_comp (comp_while_body nm inv)
    then
      let d = T_While g inv cond body inv_typing cond_typing body_typing in
      prove_post_hint (try_frame_pre false pre_typing (match_comp_res_with_post_hint d post_hint) res_ppname) post_hint t.range
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


#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 8"

let check_nuwhile
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_NuWhile? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "nu while loop" t.range g in
  let Tm_NuWhile { invariant=inv; condition=cond; body } = t.term in
  let (| inv, inv_typing |) =
    check_slprop (push_context "invariant" (term_range inv) g) inv
  in
  let (| g1, nts, labs, remaining, k |) = Pulse.Checker.Prover.prove false pre_typing (empty_env g) inv_typing in
  let inv = tm_star (Pulse.Checker.Prover.Substs.nt_subst_term inv nts) remaining in
  let inv_typing : tot_typing g1 inv tm_slprop = RU.magic () in
  let (| post_cond, r_cond |) : (ph:post_hint_for_env g1 & checker_result_t g1 inv (Some ph)) =
    let r_cond = check (push_context "check_while_condition" cond.range g1) inv inv_typing None ppname_default cond in
    let ph = Pulse.Checker.Base.infer_post r_cond in
    (| ph, Pulse.Checker.Prover.prove_post_hint r_cond (Some ph) cond.range |)
  in
  if not (T.term_eq post_cond.ret_ty tm_bool)
  || not (T.univ_eq post_cond.u u0)
  then T.fail "Expected while condition to return a bool";
  let inv_ph : post_hint_for_env g1 = inv_as_post_hint inv_typing in
  let body_pre_open = post_cond.post in
  let x = fresh g1 in
  assume (x == Ghost.reveal post_cond.x);
  let body_open_pre_typing : tot_typing (push_binding g1 x ppname_default tm_bool) (open_term body_pre_open x) tm_slprop =
    post_cond.post_typing_src
  in
  let body_pre_typing = body_typing_subst_true body_open_pre_typing in
  let r_body = 
    check 
      (push_context "check_while_body" body.range g1) 
      _ body_pre_typing (Some inv_ph) ppname_default body
  in
  let (| cond, comp_cond, cond_typing |) = apply_checker_result_k r_cond ppname_default in
  let (| body, comp_body, body_typing |) = apply_checker_result_k r_body ppname_default in
  assert (comp_cond == (comp_nuwhile_cond inv body_pre_open));
  assert (comp_body == comp_nuwhile_body inv body_pre_open);
  let d = T_NuWhile g1 inv body_pre_open cond body inv_typing (body_typing_ex body_open_pre_typing) cond_typing body_typing in
  let d_st : Pulse.Typing.Combinators.st_typing_in_ctxt g1 inv None =  (| _, _, d |) in
  let d_st : Pulse.Typing.Combinators.st_typing_in_ctxt g pre None = k None d_st in
  prove_post_hint (checker_result_for_st_typing d_st ppname_default) post_hint t.range
#pop-options