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

module Pulse.Checker.Prover.Base

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators

open Pulse.Checker.Base

module T = FStar.Tactics.V2
module PS = Pulse.Checker.Prover.Substs

let slprop_typing (g:env) (t:term) = tot_typing g t tm_slprop

//
// Scaffolding for adding elims
//
// Given a function f : slprop -> T.Tac bool that decides whether a slprop
//   should be elim-ed,
//   and an mk function to create the elim term, comp, and typing,
//   add_elims will create a continuation_elaborator
//

type mk_t =
  #g:env ->
  #v:slprop ->
  tot_typing g v tm_slprop ->
  T.Tac (option (x:ppname &
                 t:st_term &
                 c:comp { stateful_comp c /\ comp_pre c == v } &
                 st_typing g t c))

val add_elims (#g:env) (#ctxt:term) (#frame:term)
  (f:slprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g (tm_star ctxt frame) tm_slprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_slprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame))

//
// Prover state
//

noeq type preamble = {
  g0 : env;
  
  ctxt : slprop;
  frame : slprop;
  ctxt_frame_typing : slprop_typing g0 (tm_star ctxt frame);

  goals : slprop;
}

let op_Array_Access (ss:PS.ss_t) (t:term) =
  PS.ss_term t ss

let op_Star = tm_star

noeq
type prover_state (preamble:preamble) = {
  pg : g:env { g `env_extends` preamble.g0 };

  remaining_ctxt : list slprop;
  remaining_ctxt_frame_typing : slprop_typing pg (list_as_slprop remaining_ctxt * preamble.frame);

  uvs : uvs:env { disjoint uvs pg };
  ss : PS.ss_t;

  //
  // these are the typed ss
  // sometimes a step in the prover (e.g., intro exists) may compute these
  // in such cases, the prover doesn't need to compute again
  // so we cache them here
  //
  nts : option (nts:PS.nt_substs & effect_labels:list T.tot_or_ghost {
    PS.well_typed_nt_substs pg uvs nts effect_labels /\
    PS.is_permutation nts ss
  });

  solved : slprop;
  unsolved : list slprop;

  (* Note: we substitute solved, as it can contain some of the uvars in
     uvs, but not remaining_ctxt or preamble.frame which do not mention
     them (see their typing hypotheses above, in pg, which is disjoint
     from uvs. Substituting would not be wrong, just useless. *)
  k : continuation_elaborator preamble.g0 (preamble.ctxt * preamble.frame)
                              pg ((list_as_slprop remaining_ctxt * preamble.frame) * ss.(solved));

  // GM: Why isn't the rhs substituted here?
  goals_inv : slprop_equiv (push_env pg uvs)
                preamble.goals
                (list_as_slprop unsolved * solved);
  solved_inv : squash (freevars ss.(solved) `Set.subset` dom pg);
  
  progress : bool; (* used by prover and rules to check for progress and restart if so *)
  allow_ambiguous : bool;
  (* ^ true if we can skip the ambiguity check, used for functions like gather which
  are inherently ambiguous, but safely so. *)
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

let pst_extends (#preamble1 #preamble2:_)
  (pst1 : prover_state preamble1)
  (pst2 : prover_state preamble2)
=
  pst1.pg `env_extends` pst2.pg /\
  pst1.uvs `env_extends` pst2.uvs /\
  pst1.ss `ss_extends` pst2.ss

type prover_t =
  #preamble:_ ->
  pst1:prover_state preamble ->
  T.Tac (pst2:prover_state preamble { pst2 `pst_extends` pst1 /\
                                      is_terminal pst2 })
