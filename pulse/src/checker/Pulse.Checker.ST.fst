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

module Pulse.Checker.ST
open FStar.Tactics.V2
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Reflection.Util

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
open Pulse.Checker.Prover
open Pulse.Show

let should_allow_ambiguous (t:term) : T.Tac bool =
  Pulse.Reflection.Util.head_has_attr_string "Pulse.Lib.Core.allow_ambiguous" t

open Pulse.PP
#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 2"
let check
  (g:env)
  (ctxt:slprop)
  (ctxt_typing:tot_typing g ctxt tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_ST? t.term })
  : T.Tac (checker_result_t g ctxt post_hint) =

  let g = push_context "st" t.range g in
  let post_hint: post_hint_opt g = post_hint in
  let range = t.range in
  let Tm_ST { t=e; args } = t.term in
  if Cons? args then
    fail_doc g (Some t.range) [
      text "Internal error: trailing combinator arguments not lifted in Tm_ST";
      pp t
    ];
  let e, ty, eff = tc_term_phase1 g e in
  match Pulse.Readback.readback_comp ty with
  | None -> fail g (Some range) (Printf.sprintf "readback of %s failed" (show ty))
  | Some (C_Tot _) ->
    let h, a = T.collect_app_ln e in
    let (| _, _, th, _ |) = Pulse.Checker.Pure.compute_term_type g h in
    let open Pulse.PP in
    fail_doc g 
      (Some range)
      [text "Expected an application of a function returning a computation type { stt, stt_ghost, stt_atomic }";
       text "But the application:";
       pp e;
       text "is a total term";
       text "Maybe it is not fully applied?"]

  | Some c0 -> (
    let allow_ambiguous = should_allow_ambiguous e in
    let (| g', ctxt', k |) = prove (RU.range_of_term e) g ctxt (comp_pre c0) allow_ambiguous in

    // remove spurious beta-redexes
    let e = e |> RU.beta_lax (elab_env g) |> RU.deep_compress in
    let ty = ty |> RU.beta_lax (elab_env g) |> RU.deep_compress in
    assume elab_comp c0 == ty;
    let Some c = Pulse.Readback.readback_comp ty in

    let (| eff, typing |) = core_check_term_at_type g' e ty in
    let t = { t with term = Tm_ST { t=e; args=[] }; effect_tag = T.seal (Some (ctag_of_comp_st c)) } in
    let d : st_typing g' t c =
      if eff = T.E_Total
      then T_ST g' e c typing
      else (
        match c with
        | C_ST _ | C_STAtomic .. ->
          let open Pulse.PP in
          fail_doc g (Some range)
            [text "Application of a stateful or atomic computation cannot have a ghost effect";
            pp t;
            text "has computation type";
            pp c]
        | C_STGhost .. ->
          let d_non_info : non_informative g' c =
            let token = is_non_informative g' c in
            match token with
            | None ->
              fail g' (Some range)
                (Printf.sprintf "Unexpected informative result for %s" (P.comp_to_string c))
            | Some token ->
                E <| RT.Non_informative_token _ _ (FStar.Squash.return_squash token) 
          in
          T_STGhost g' e c typing d_non_info
      )
      in
      let h: tot_typing g' ctxt' tm_slprop = RU.magic () in // TODO: thread through prover
      if comp_post c `eq_tm` tm_is_unreachable then
        let framed = checker_result_for_st_typing (k _ (| t, add_frame c ctxt', T_Frame _ _ _ ctxt' h d |)) res_ppname in
        RU.record_stats "prove_post_hint" fun _ -> prove_post_hint framed post_hint range
      else
        // TODO: not sure why we need the type equality check below..
        let (| c, d |) = match_comp_res_with_post_hint d post_hint in
        let framed = checker_result_for_st_typing (k _ (| t, add_frame c ctxt', T_Frame _ _ _ ctxt' h d |)) res_ppname in
        RU.record_stats "prove_post_hint" fun _ -> prove_post_hint framed post_hint range
  )
#pop-options