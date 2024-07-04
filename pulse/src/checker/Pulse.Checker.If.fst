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
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory
module RU = Pulse.RuntimeUtils
module J = Pulse.JoinComp

#set-options "--z3rlimit 40"

let check
  (g:env)
  (pre:term)
  (pre_typing: tot_typing g pre tm_slprop)
  (post_hint:post_hint_for_env g)
  (res_ppname:ppname)
  (b:term)
  (e1 e2:st_term)
  (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint)) =
  
  let g = Pulse.Typing.Env.push_context g "check_if" e1.range in

  let (| b, b_typing |) =
    check_tot_term g b tm_bool in

  let post = post_hint.post in
  let hyp = fresh g in
  let g_with_eq (eq_v:term) =
    push_binding g hyp (mk_ppname_no_range "_if_hyp") (mk_eq2 u0 tm_bool b eq_v)
  in

  let check_branch (eq_v:term) (br:st_term) (is_then:bool)
    : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
             c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (Some post_hint)} &
             st_typing (g_with_eq eq_v) br c) =
    let g_with_eq = g_with_eq eq_v in
    let pre_typing = 
      Metatheory.tot_typing_weakening_single
        pre_typing
        hyp 
        (mk_eq2 u0 tm_bool b eq_v)
    in
    
    let (| br, c, d |) =
      let ppname = mk_ppname_no_range "_if_br" in
      let r =
        check g_with_eq pre pre_typing (Some post_hint) ppname br in
      apply_checker_result_k r ppname in

    let br_name = if is_then then "then" else "else" in

    if hyp `Set.mem` freevars_st br
    then fail g (Some br.range)
           (Printf.sprintf "check_if: branch hypothesis is in freevars of checked %s branch" br_name)
    else (| br, c, d |)
  in

  let (| e1, c1, e1_typing |) = check_branch tm_true e1 true in
  let (| e2, c2, e2_typing |) = check_branch tm_false e2 false in    
  let (| c, e1_typing, e2_typing |) =
    J.join_comps _ _ _ e1_typing _ _ _ e2_typing post_hint in

  let c_typing = comp_typing_from_post_hint c pre_typing post_hint in

  let d : st_typing_in_ctxt g pre (Some post_hint) =
    (| _, c, T_If g b e1 e2 c hyp b_typing e1_typing e2_typing (E c_typing) |) in

  checker_result_for_st_typing d res_ppname
