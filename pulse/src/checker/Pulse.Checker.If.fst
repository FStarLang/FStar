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
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module Metatheory = Pulse.Typing.Metatheory
module J = Pulse.JoinComp
module RW = Pulse.Checker.Prover.RewritesTo
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

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 2"
#restart-solver
let check
  (g:env)
  (pre:term)
  (pre_typing: tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (b:term)
  (e1 e2:st_term)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  
  let g = Pulse.Typing.Env.push_context g "check_if" e1.range in

  let (| b, b_typing |) =
    check_tot_term g b tm_bool in

  let hyp = fresh g in

  let g_with_eq = g_with_eq g hyp b in  
  let check_branch (eq_v:term) (br:st_term) (is_then:bool)
  : T.Tac (checker_result_t (g_with_eq eq_v) pre post_hint)
  = let pre_typing = 
      Metatheory.tot_typing_weakening_single
        pre_typing
        hyp 
        (mk_sq_rewrites_to_p u0 tm_bool b eq_v)
    in

    let br =
      let t =
        mk_term (Tm_ProofHintWithBinders {
          binders = [];
          hint_type = RENAME { pairs = [(b, eq_v)]; goal=None; tac_opt=None; elaborated=true };
          t = br;
        }) br.range
      in
      { t with effect_tag = br.effect_tag }
    in

    let ppname = mk_ppname_no_range "_if_br" in
    let r = check (g_with_eq eq_v) pre pre_typing post_hint ppname br in
    r
  in

  let then_ = check_branch tm_true e1 true in
  let else_ = check_branch tm_false e2 false in
  let joinable : (
    ph:post_hint_for_env g & 
    checker_result_t (g_with_eq tm_true) pre (PostHint ph) &
    checker_result_t (g_with_eq tm_false) pre (PostHint ph)
  ) = match post_hint with
      | PostHint ph -> 
        (| ph, then_, else_ |)
      | _ ->
        let then_ : checker_result_t _ _ NoHint = retype_checker_result _ then_ in
        let else_ : checker_result_t _ _ NoHint = retype_checker_result _ else_ in
        let post_then = Pulse.Checker.Base.infer_post then_ in
        let post_else = Pulse.Checker.Base.infer_post else_ in
        let post = Pulse.JoinComp.join_post #g #hyp #b post_then post_else in
        let then_ = Pulse.Checker.Prover.prove_post_hint then_ (PostHint post) e1.range in
        let else_ = Pulse.Checker.Prover.prove_post_hint else_ (PostHint post) e2.range in
        (| post, then_, else_ |)
  in
  let (| post_hint', then_, else_ |) = joinable in

  let extract #g #pre (#ph:post_hint_for_env g) (r:checker_result_t g pre (PostHint ph)) (is_then:bool)
  : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
           c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (PostHint ph)} &
           st_typing g br c)
  = let (| br, c, d |) =
      let ppname = mk_ppname_no_range "_if_br" in
      apply_checker_result_k r ppname
    in
    let br_name = if is_then then "then" else "else" in
    if hyp `Set.mem` freevars_st br
    then fail g (Some br.range)
           (Printf.sprintf "check_if: branch hypothesis is in freevars of checked %s branch" br_name)
    else (| br, c, d |)
  in
  let (| e1, c1, e1_typing |) = extract then_ true in
  let (| e2, c2, e2_typing |) = extract else_ false in
  let (| c, e1_typing, e2_typing |) =
    J.join_comps _ _ _ e1_typing _ _ _ e2_typing post_hint' in

  let c_typing = comp_typing_from_post_hint c pre_typing post_hint' in

  let d : st_typing_in_ctxt g pre (PostHint post_hint') =
    (| _, c, T_If g b e1 e2 c hyp b_typing e1_typing e2_typing (E c_typing) |) in

  let res : checker_result_t g pre (PostHint post_hint') = checker_result_for_st_typing d res_ppname in
  retype_checker_result_post_hint post_hint' post_hint res
  #pop-options