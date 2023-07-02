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

  : T.Tac (g1 : env { g1 `env_extends` g /\ disjoint g1 uvs } &
           ss : PS.t { well_typed_ss ss uvs g1 } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 (ss.(goals) * remaining_ctxt))
