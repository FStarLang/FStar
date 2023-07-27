module Pulse.Checker.Prover.Base

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators

open Pulse.Checker.Base

module T = FStar.Tactics.V2
module PS = Pulse.Checker.Prover.Substs

let vprop_typing (g:env) (t:term) = tot_typing g t tm_vprop

//
// Scaffolding for adding elims
//
// Given a function f : vprop -> T.Tac bool that decides whether a vprop
//   should be elim-ed,
//   and an mk function to create the elim term, comp, and typing,
//   add_elims will create a continuation_elaborator
//

type mk_t =
  #g:env ->
  #v:vprop ->
  tot_typing g v tm_vprop ->
  T.Tac (option (x:ppname &
                 t:st_term &
                 c:comp { stateful_comp c /\ comp_pre c == v } &
                 st_typing g t c))

val add_elims (#g:env) (#ctxt:term) (#frame:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g (tm_star ctxt frame) tm_vprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_vprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame))

//
// Prover state
//

noeq type preamble = {
  g0 : env;
  
  ctxt : vprop;
  frame : vprop;
  ctxt_frame_typing : vprop_typing g0 (tm_star ctxt frame);

  goals : vprop;
}

let op_Array_Access (ss:PS.ss_t) (t:term) =
  PS.ss_term t ss

let op_Star = tm_star

noeq type prover_state (preamble:preamble) = {
  pg : g:env { g `env_extends` preamble.g0 };

  remaining_ctxt : list vprop;
  remaining_ctxt_frame_typing : vprop_typing pg (list_as_vprop remaining_ctxt * preamble.frame);

  uvs : uvs:env { disjoint uvs pg };
  ss : PS.ss_t;

  solved : vprop;
  unsolved : list vprop;

  k : continuation_elaborator preamble.g0 (preamble.ctxt * preamble.frame)
                              pg ((list_as_vprop remaining_ctxt * preamble.frame) * ss.(solved));

  goals_inv : vprop_equiv (push_env pg uvs) preamble.goals (list_as_vprop unsolved * solved);
  solved_inv : squash (freevars ss.(solved) `Set.subset` dom pg);
}

let is_terminal (#preamble:_) (st:prover_state preamble) =
  st.unsolved == []

irreducible
let extend_post_hint_opt_g (g:env) (post_hint:post_hint_opt g) (g1:env { g1 `env_extends` g })
  : p:post_hint_opt g1 { p == post_hint } =
  match post_hint with
  | None -> None
  | Some post_hint ->
    assert (g `env_extends` post_hint.g);
    assert (g1 `env_extends` g);
    assert (g1 `env_extends` post_hint.g);
    Some post_hint

let ss_extends (ss1 ss2:PS.ss_t) =
  Set.subset (PS.dom ss2) (PS.dom ss1) /\
  (forall (x:var). PS.contains ss2 x ==> PS.sel ss1 x == PS.sel ss2 x)

let pst_extends (#preamble:_) (pst1 pst2:prover_state preamble) =
  pst1.pg `env_extends` pst2.pg /\
  pst1.uvs `env_extends` pst2.uvs /\
  pst1.ss `ss_extends` pst2.ss

type prover_t =
  #preamble:_ ->
  pst1:prover_state preamble ->
  T.Tac (pst2:prover_state preamble { pst2 `pst_extends` pst1 /\
                                      is_terminal pst2 })
