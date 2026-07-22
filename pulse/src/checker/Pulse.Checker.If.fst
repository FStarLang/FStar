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

module Pulse.Checker.If

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module J = Pulse.JoinComp
module RU = Pulse.RuntimeUtils
#set-options "--z3rlimit 40"


let retype_checker_result_post_hint #g #pre (ph:post_hint_for_env g)
    (ph':post_hint_opt g {PostHint? ph' ==> PostHint?.v ph' == ph})
    (r:checker_result_t g pre (PostHint ph))
: T.Tac (checker_result_t g pre ph')
= let (| x, g1, t, ctxt', k |) = r in
  (| x, g1, t, ctxt', k |)

let retype_checker_result (#g:env) (#ctxt:slprop) (#ph:post_hint_opt g) (ph':post_hint_opt g { not (PostHint? ph')})
  (r:checker_result_t g ctxt ph)
: checker_result_t g ctxt ph'
= let (| x, g1, t, ctxt, k |) = r in
  (| x, g1, t, ctxt, k |)

let set_effect_annot (#g:env) (ph:post_hint_for_env g) (ea:effect_annot)
: (ph':post_hint_for_env g { ph'.ret_ty == ph.ret_ty /\ ph'.post == ph.post /\
                             ph'.u == ph.u /\ ph'.effect_annot == ea })
= { ph with effect_annot = ea }

// Relabel a stt/stt_div computation with the given (stt or stt_div) effect,
// preserving its state components. Used to lift the branches of an inferred
// conditional to a common effect once a divergent branch is detected.
let lift_branch_comp (c:comp_st)
                     (eff:effect_annot { EffectAnnotSTT? eff \/ EffectAnnotSTTDiv? eff })
: (c':comp_st { comp_pre c' == comp_pre c /\ comp_res c' == comp_res c /\
                comp_u c' == comp_u c /\ comp_post c' == comp_post c /\
                effect_annot_matches c' eff })
= match eff with
  | EffectAnnotSTTDiv -> C_STDiv (st_comp_of_comp c)
  | _ -> C_ST (st_comp_of_comp c)

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 2"
#restart-solver
let check
  (g:env)
  (pre:term)
  (post_hint:post_hint_opt g)
  (annot_post:option (post_hint_for_env g))
  (res_ppname:ppname)
  (b:st_term)
  (e1 e2:st_term)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  
  let g = Pulse.Typing.Env.push_context g "check_if" e1.range in

  let b : term =
    match b.term with
    | Tm_Return { term=bt } -> check_tot_term g bt tm_bool
    | _ -> fail g (Some b.range) "check_if: expected a pure condition (Tm_Return); stateful conditions should have been elaborated away"
  in

  let hyp = fresh g in

  //
  // The hint the branches are checked against. When the surrounding context
  // fixes the postcondition (and effect), use it directly. Otherwise, if the
  // conditional carries an `ensures` annotation, check the branches against that
  // postcondition slprop but leave the effect to be inferred from the branches
  // (issue #4368); with no annotation, infer the postcondition too (issue #4366).
  //
  let branch_hint : post_hint_opt g =
    match post_hint with
    | PostHint _ -> post_hint
    | _ -> (match annot_post with | Some ap -> PostHint ap | None -> NoHint)
  in

  let g_with_eq = g_with_eq g hyp b in  
  let check_branch (eq_v:term) (br:st_term) (is_then:bool)
  : T.Tac (checker_result_t (g_with_eq eq_v) pre branch_hint)
  =
    let branch_range = br.range in
    let br =
      let t =
        mk_term (Tm_ProofHintWithBinders {
          binders = [];
          hint_type = RENAME { pairs = [(b, eq_v)]; goal=None; tac_opt = Some Pulse.Reflection.Util.match_rename_tac_tm; elaborated=true };
          t = br;
        }) br.range
      in
      { t with effect_tag = br.effect_tag }
    in

    let ppname = mk_ppname_no_range "_if_br" in
    let r = RU.with_error_bound branch_range (fun () ->
      check (g_with_eq eq_v) pre branch_hint ppname br) in
    r
  in

  let infer_post_branch (#eq_v:term) (r: checker_result_t (g_with_eq eq_v) pre NoHint) :
    T.Tac (p:post_hint_for_env g {p.g == g /\ p.effect_annot==EffectAnnotSTT}) =
    let (| x, g', (u, t), post, k |) = r in
    J.infer_post' g g' u t x post
  in

  let then_ = check_branch tm_true e1 true in
  let else_ = check_branch tm_false e2 false in
  let joinable : (
    ph:post_hint_for_env g & 
    checker_result_t (g_with_eq tm_true) pre (PostHint ph) &
    checker_result_t (g_with_eq tm_false) pre (PostHint ph)
  ) = match branch_hint with
      | PostHint ph -> 
        (| ph, then_, else_ |)
      | _ ->
        let then_ : checker_result_t _ _ NoHint = retype_checker_result _ then_ in
        let else_ : checker_result_t _ _ NoHint = retype_checker_result _ else_ in
        let post_then = infer_post_branch then_ in
        let post_else = infer_post_branch else_ in
        let post = Pulse.JoinComp.join_post #g #hyp #b post_then post_else in
        let then_ = Pulse.Checker.Prover.prove_post_hint then_ (PostHint post) e1.range in
        let else_ = Pulse.Checker.Prover.prove_post_hint else_ (PostHint post) e2.range in
        (| post, then_, else_ |)
  in
  let (| post_hint', then_, else_ |) = joinable in

  let assemble (post_final:post_hint_for_env g {
                  PostHint? post_hint ==> PostHint?.v post_hint == post_final })
               (e1:st_term { ~(hyp `Set.mem` freevars_st e1) })
               (c1:comp_st { comp_pre c1 == pre /\ comp_post_matches_hint c1 (PostHint post_final) })
               (e2:st_term { ~(hyp `Set.mem` freevars_st e2) })
               (c2:comp_st { comp_pre c2 == pre /\ comp_post_matches_hint c2 (PostHint post_final) })
  : T.Tac (checker_result_t g pre post_hint)
  = let c =
      J.join_comps (g_with_eq tm_true) e1 c1 (g_with_eq tm_false) e2 c2 post_final in
    let c_typing = comp_typing_from_post_hint c post_final in
    let b_st = mk_term (Tm_Return { expected_type = tm_bool; insert_eq = false; term = b }) e1.range in
    let if_st = wrst c (Tm_If { b=b_st; then_=e1; else_=e2; post=None }) in
    let d : st_typing_in_ctxt g pre (PostHint post_final) =
      (| if_st, c |) in
    let res : checker_result_t g pre (PostHint post_final) = checker_result_for_st_typing d res_ppname in
    retype_checker_result_post_hint post_final post_hint res
  in

  match post_hint with
  | PostHint _ ->
    //
    // The postcondition (hence the effect) was supplied by the user: check each
    // branch against it directly and compose.
    //
    let extract #g #pre (#ph:post_hint_for_env g) (r:checker_result_t g pre (PostHint ph)) (is_then:bool)
    : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
             c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (PostHint ph)})
    = let (| br, c |) =
        let ppname = mk_ppname_no_range "_if_br" in
        apply_checker_result_k r ppname
      in
      assume not (hyp `Set.mem` freevars_st br);
      (| br, c |)
    in
    let (| e1, c1 |) = extract then_ true in
    let (| e2, c2 |) = extract else_ false in
    assemble post_hint' e1 c1 e2 c2

  | _ ->
    //
    // The postcondition was inferred (tentatively as stt). Read back the natural
    // effect of each branch with a single check: if either branch is divergent,
    // the whole conditional is divergent (issue #4366). This avoids re-checking
    // any branch.
    //
    let extract_nat #g #pre (#ph:post_hint_for_env g) (r:checker_result_t g pre (PostHint ph)) (is_then:bool)
    : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
             c:comp_st { comp_pre c == pre /\ comp_res c == ph.ret_ty /\
                         comp_u c == ph.u /\ comp_post c == ph.post })
    = let (| br, c |) =
        let ppname = mk_ppname_no_range "_if_br" in
        apply_checker_result_k_nohint r ppname
      in
      assume not (hyp `Set.mem` freevars_st br);
      (| br, c |)
    in
    let (| e1, c1 |) = extract_nat then_ true in
    let (| e2, c2 |) = extract_nat else_ false in
    //
    // Inferred branches produce only stt or stt_div; join by letting stt_div
    // dominate.
    //
    let joined_eff : (ea:effect_annot { EffectAnnotSTT? ea \/ EffectAnnotSTTDiv? ea }) =
      if EffectAnnotSTTDiv? (effect_annot_of_comp c1) || EffectAnnotSTTDiv? (effect_annot_of_comp c2)
      then EffectAnnotSTTDiv
      else EffectAnnotSTT
    in
    let post_final = set_effect_annot post_hint' joined_eff in
    let c1 = lift_branch_comp c1 joined_eff in
    let c2 = lift_branch_comp c2 joined_eff in
    assemble post_final e1 c1 e2 c2
  #pop-options
