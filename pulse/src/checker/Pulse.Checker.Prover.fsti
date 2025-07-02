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

module Pulse.Checker.Prover

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

module PS = Pulse.Checker.Prover.Substs

include Pulse.Checker.Prover.Base
include Pulse.Checker.Prover.Util

val normalize_slprop
  (g:env)
  (v:slprop)
  : T.Tac (v':slprop & slprop_equiv g v v')

val normalize_slprop_welltyped
  (g:env)
  (v:slprop)
  (v_typing:tot_typing g v tm_slprop)
  : T.Tac (v':slprop & slprop_equiv g v v' & tot_typing g v' tm_slprop)

val prove
  (allow_ambiguous : bool)
  (#g:env) (#ctxt:slprop) (ctxt_typing:tot_typing g ctxt tm_slprop)
  (uvs:env { disjoint g uvs })
  (#goals:slprop) (goals_typing:tot_typing (push_env g uvs) goals tm_slprop)

  : T.Tac (g1 : env { g1 `env_extends` g /\ disjoint g1 uvs } &
           nts : PS.nt_substs &
           effect_labels:list T.tot_or_ghost { PS.well_typed_nt_substs g1 uvs nts effect_labels } &
           remaining_ctxt : slprop &
           continuation_elaborator g ctxt g1 ((PS.nt_subst_term goals nts) * remaining_ctxt))

val try_frame_pre_uvs
  (allow_ambiguous : bool)
  (#g:env) (#ctxt:slprop) (ctxt_typing:tot_typing g ctxt tm_slprop)
  (uvs:env { disjoint g uvs })
  (d:(t:st_term & c:comp_st & st_typing (push_env g uvs) t c))
  (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None)

val try_frame_pre
  (allow_ambiguous : bool)
  (#g:env) (#ctxt:slprop) (ctxt_typing:tot_typing g ctxt tm_slprop)
  (d:(t:st_term & c:comp_st & st_typing g t c))
  (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None)

val prove_post_hint (#g:env) (#ctxt:slprop)
  (r:checker_result_t g ctxt None)
  (post_hint:post_hint_opt g)
  (rng:range)
  
  : T.Tac (checker_result_t g ctxt post_hint)

val elim_exists_and_pure (#g:env) (#ctxt:slprop)
  (ctxt_typing:tot_typing g ctxt tm_slprop)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' tm_slprop &
           continuation_elaborator g ctxt g' ctxt')
