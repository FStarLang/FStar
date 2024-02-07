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

module Pulse.Checker.AssertWithBinders

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

let head_wild (st:st_term) =
  match st.term with
  | Tm_ProofHintWithBinders { hint_type = WILD } -> true
  | _ -> false

let head_show_proof_state (st:st_term) =
  match st.term with
  | Tm_ProofHintWithBinders { hint_type = SHOW_PROOF_STATE _ } -> true
  | _ -> false

let handle_head_immediately st = head_wild st || head_show_proof_state st

val check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_ProofHintWithBinders? st.term })
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)

