module Pulse.Prover.Common

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Util

module T = FStar.Tactics

module Psubst = Pulse.Prover.Substs

let vprop_typing (g:env) (t:term) = tot_typing g t tm_vprop

noeq
type preamble = {
  g0 : env;

  ctxt : vprop;
  ctxt_typing : vprop_typing g0 ctxt;

  t : st_term;
  c : comp_st;

  uvs : uvs:env { disjoint uvs g0 }
}

let pst_env (#g0:env) (uvs:env { disjoint uvs g0 }) (ss:Psubst.t g0) =
  push_env g0 (psubst_env (filter_ss uvs ss) ss)

noeq
type prover_state (preamble:preamble) = {
  ss : ss:Psubst.t preamble.g0 {
    well_typed_ss preamble.uvs ss
  };

  solved_goals : term;

  unsolved_goals : list term;

  remaining_ctxt : list term;

  steps : st_term;

  t_typing
    : st_typing (pst_env preamble.uvs ss)
                (Psubst.subst_st_term ss preamble.t)
                (Psubst.subst_comp ss preamble.c);

  unsolved_goals_typing
    : vprop_typing (pst_env preamble.uvs ss)
                   (list_as_vprop unsolved_goals);

  remaining_ctxt_typing
    : vprop_typing preamble.g0 (list_as_vprop remaining_ctxt);
  
  steps_typing
    : st_typing (pst_env preamble.uvs ss)
                steps
                (ghost_comp
                   preamble.ctxt
                   (tm_star (list_as_vprop remaining_ctxt) solved_goals));

  c_pre_inv
    : vprop_equiv (pst_env preamble.uvs ss)
                  (Psubst.subst_term ss (comp_pre preamble.c))
                  (tm_star (list_as_vprop unsolved_goals) solved_goals);

  solved_goals_closed : squash (freevars solved_goals `Set.subset`
                                dom preamble.g0);
}

let pst_extends (#preamble:_) (p1 p2:prover_state preamble) =
  p1.ss `Psubst.subst_extends` p2.ss

type prover_t =
  #preamble:_ ->
  p:prover_state preamble ->
  T.Tac (option (p':prover_state preamble { p' `pst_extends` p /\
                                            p'.unsolved_goals == [] }))

type prover_step_t =
  #preamble:_ ->
  p:prover_state preamble ->
  prover:prover_t ->
  T.Tac (option (p':prover_state preamble { p' `pst_extends` p }))

