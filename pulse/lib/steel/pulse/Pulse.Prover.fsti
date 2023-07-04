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
           ss1 : PS.ss_t { well_typed_ss ss1 uvs1 g1 } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 (ss1.(goals) * remaining_ctxt))
