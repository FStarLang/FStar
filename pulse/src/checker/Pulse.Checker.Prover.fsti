(*
   Copyright 2025 Microsoft Research

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

module Pulse.Checker.Prover
open Pulse.Checker.Base
open Pulse.Typing
open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Syntax.Naming
module T = FStar.Tactics.V2

val elim_exists (g: env) (frame: slprop) u b body (x: nvar { ~(Set.mem (snd x) (dom g)) })
    (g': env { g' == push_binding g (snd x) (fst x) (mk_erased u b.binder_ty) }) :
  continuation_elaborator g (frame `tm_star` tm_exists_sl u b body)
    g' (frame `tm_star` open_term' body (mk_reveal u b.binder_ty (term_of_nvar x)) 0)

val prove (rng: range) (g: env) (ctxt goals: slprop) (allow_amb: bool) :
  T.Tac (g':env { env_extends g' g } & ctxt': slprop &
    continuation_elaborator g ctxt g' (goals `tm_star` ctxt'))

val prove_post_hint (#g:env) (#ctxt:slprop) (r:checker_result_t g ctxt NoHint) (post_hint:post_hint_opt g) (rng:range) :
  T.Tac (checker_result_t g ctxt post_hint)

val try_frame_pre (allow_ambiguous : bool) (#g:env)
    (#ctxt:slprop) (ctxt_typing:tot_typing g ctxt tm_slprop)
    (d:(t:st_term & c:comp_st & st_typing g t c))
    (res_ppname:ppname) :
  T.Tac (checker_result_t g ctxt NoHint)

val elim_exists_and_pure (#g:env) (#ctxt:slprop)
    (ctxt_typing:tot_typing g ctxt tm_slprop)
    : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_slprop &
            continuation_elaborator g ctxt g' ctxt')