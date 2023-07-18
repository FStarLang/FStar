module Pulse.Prover

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Prover.Common

module PS = Pulse.Prover.Substs

val prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:tot_typing (push_env g uvs) goals tm_vprop)

  : T.Tac (g1 : env { g1 `env_extends` g } &
           nts : PS.nt_substs { PS.well_typed_nt_substs g1 uvs nts } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 ((PS.nt_subst_term goals nts) * remaining_ctxt))

val try_frame_pre (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (#t:st_term) (#c:comp_st) (d:st_typing g t c)

  : T.Tac (checker_result_t g ctxt None)

val repack (#g:env) (#ctxt:vprop)
  (r:checker_result_t g ctxt None)
  (post_hint:post_hint_opt g)
  (rng:range)
  
  : T.Tac (checker_result_t g ctxt post_hint)
