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

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
module Prover = Pulse.Checker.Prover
open Pulse.Show

let should_allow_ambiguous (t:term) : T.Tac bool =
  Pulse.Reflection.Util.head_has_attr_string "Pulse.Lib.Core.allow_ambiguous" t

let check
  (g0:env)
  (ctxt:slprop)
  (ctxt_typing:tot_typing g0 ctxt tm_slprop)
  (post_hint:post_hint_opt g0)
  (res_ppname:ppname)
  (t:st_term { Tm_ST? t.term })
  : T.Tac (checker_result_t g0 ctxt post_hint) =

  let g = push_context "st" t.range g0 in
  let post_hint: post_hint_opt g = post_hint in
  let range = t.range in
  let Tm_ST { t=e } = t.term in
  let (| uvs, e, _ |) = Pulse.Checker.Pure.instantiate_term_implicits_uvs g e true in
  let g' : env = push_env g uvs in
  assert (g' `env_extends` g);
  let post_hint: post_hint_opt g' = post_hint in
  let (| e, eff, ty, typing |) = Pulse.Checker.Pure.compute_term_type g' e in
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

  | Some c -> (
    let allow_ambiguous = should_allow_ambiguous e in
    let t = { t with term = Tm_ST { t=e }  } in
    let d : ( st_typing g' t c ) =
    if eff = T.E_Total
    then T_ST g' e c typing
    else (
      match c with
      | C_ST _ | C_STAtomic .. ->
        let open Pulse.PP in
        fail_doc g0 (Some range)
          [text "Application of a stateful or atomic computation cannot have a ghost effect";
           pp t;
           text "has computation type";
           pp c]
      | C_STGhost .. ->
        let d_non_info : non_informative g' c =
          let token = is_non_informative g' c in
          match token with
          | None ->
            fail g (Some range)
              (Printf.sprintf "Unexpected informative result for %s" (P.comp_to_string c))
          | Some token ->
              E <| RT.Non_informative_token _ _ (FStar.Squash.return_squash token) 
        in
        T_STGhost g' e c typing d_non_info
    )
    in
    let (| st', c', st_typing' |) = match_comp_res_with_post_hint d post_hint in
    let framed = 
      RU.record_stats "try_frame_pre_uvs" fun _ -> Prover.try_frame_pre_uvs allow_ambiguous ctxt_typing uvs (| st', c', st_typing' |) res_ppname in
    RU.record_stats "prove_post_hint" fun _ -> Prover.prove_post_hint framed post_hint range
  )