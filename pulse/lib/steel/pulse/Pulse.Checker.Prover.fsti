module Pulse.Checker.Prover

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

module PS = Pulse.Checker.Prover.Substs

include Pulse.Checker.Prover.Base
include Pulse.Checker.Prover.Util

val prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:tot_typing (push_env g uvs) goals tm_vprop)

  : T.Tac (g1 : env { g1 `env_extends` g /\ disjoint g1 uvs } &
           nts : PS.nt_substs { PS.well_typed_nt_substs g1 uvs nts } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 ((PS.nt_subst_term goals nts) * remaining_ctxt))

val try_frame_pre_uvs (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (uvs:env { disjoint g uvs })
  (#t:st_term) (#c:comp_st) (d:st_typing (push_env g uvs) t c)
  (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None)

val try_frame_pre (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None)

val prove_post_hint (#g:env) (#ctxt:vprop)
  (r:checker_result_t g ctxt None)
  (post_hint:post_hint_opt g)
  (rng:range)
  
  : T.Tac (checker_result_t g ctxt post_hint)
