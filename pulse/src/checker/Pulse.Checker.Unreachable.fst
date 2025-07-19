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

module Pulse.Checker.Unreachable

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover


let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Unreachable? t.term })
: T.Tac (checker_result_t g pre post_hint)
= let rng = t.range in
  match post_hint with
  | NoHint | TypeHint _ ->
    fail g (Some t.range)
      "Expected a postcondition to be annotated when unreachable is used"
  | PostHint post ->
    let ff = (wr (`False) rng) in
    let (|eff, ff_typing |) = Pulse.Checker.Pure.core_check_term_at_type g ff tm_prop in
    if eff <> T.E_Total then T.fail "Impossible: False has effect Ghost"
    else let ff_validity = Pulse.Checker.Pure.check_prop_validity g ff ff_typing in
         let x = fresh g in
         let (| c, c_typing |) = Pulse.Typing.Combinators.comp_for_post_hint pre_typing post x in
         let d = T_Unreachable _ _ c_typing ff_validity in
         checker_result_for_st_typing (| _, _, d |) res_ppname
