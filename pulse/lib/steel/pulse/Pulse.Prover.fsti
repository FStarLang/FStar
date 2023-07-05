module Pulse.Prover

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Prover.Common

module PS = Pulse.Prover.Substs

val prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:vprop_typing g ctxt)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:vprop_typing (push_env g uvs) goals)

  : T.Tac (g1 : env { g1 `env_extends` g } &
           uvs1 : env { uvs1 `env_extends` uvs /\ disjoint uvs1 g1 } &
           nts1 : PS.nt_substs { PS.well_typed_nt_substs g1 uvs1 nts1 } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 ((PS.nt_subst_term goals nts1) * remaining_ctxt))
