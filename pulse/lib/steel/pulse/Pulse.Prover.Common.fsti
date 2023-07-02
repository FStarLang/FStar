module Pulse.Prover.Common

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv

module T = FStar.Tactics.V2

module PS = Pulse.Prover.Substs

let vprop_typing (g:env) (t:term) = tot_typing g t tm_vprop

type continuation_elaborator
  (g:env) (ctxt:term)
  (g':env) (ctxt':term) =
  post_hint:post_hint_opt g ->
  checker_result_t g' ctxt' post_hint ->
  T.Tac (checker_result_t g ctxt post_hint)

val k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt

val k_elab_trans (#g0 #g1 #g2:env) (#ctxt0 #ctxt1 #ctxt2:term)
                 (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
                 (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2

val k_elab_equiv (#g1 #g2:env) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)
                 (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
                 (d1:vprop_equiv g1 ctxt1 ctxt1')
                 (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2'

//
// A canonical continuation elaborator for Bind
//
val continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_vprop)
  (x:var { None? (lookup g x) })
  : T.Tac (continuation_elaborator
             g                                (tm_star ctxt (comp_pre c1))
             (push_binding g x ppname_default (comp_res c1)) (tm_star (open_term (comp_post c1) x) ctxt))



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

noeq type preamble = {
  g0 : env;
  
  ctxt : vprop;
  frame : vprop;
  ctxt_frame_typing : vprop_typing g0 (tm_star ctxt frame);

  goals : vprop;
}

let op_Array_Access (ss:PS.t) (t:term) =
  PS.subst_term t ss

let op_Star = tm_star

let well_typed_ss (ss:PS.t) (uvs g:env) =
  forall (x:var).
  PS.contains ss x ==> (Set.mem x (dom uvs) /\
                        tot_typing g (PS.sel ss x) (ss.(Some?.v (lookup uvs x))))

noeq type prover_state (preamble:preamble) = {
  pg : g:env { g `env_extends` preamble.g0 };

  remaining_ctxt : list vprop;
  remaining_ctxt_frame_typing : vprop_typing pg (list_as_vprop remaining_ctxt * preamble.frame);

  uvs : uvs:env { disjoint uvs pg };
  ss : ss:PS.t { well_typed_ss ss uvs pg};

  solved : vprop;
  unsolved : list vprop;

  solved_typing : vprop_typing pg ss.(solved);

  k : continuation_elaborator preamble.g0 (preamble.ctxt * preamble.frame)
                              pg ((list_as_vprop remaining_ctxt * preamble.frame) * ss.(solved));

  goals_inv : vprop_equiv (push_env pg uvs) preamble.goals (list_as_vprop unsolved * solved);
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

let st_typing_subst (g:env) (uvs:env { disjoint uvs g }) (t:st_term) (c:comp_st)
  (d:st_typing (push_env g uvs) t c)
  (ss:PS.t { well_typed_ss ss uvs g })

  : T.Tac (option (st_typing g (PS.subst_st_term t ss) (PS.subst_comp c ss))) =

  let b = PS.check_well_typedness g uvs ss in
  if not b then None
  else let g' = mk_env (fstar_env g) in
       assert (equal (push_env uvs g') uvs);
       let d = PS.st_typing_nt_substs g uvs g' d (PS.as_nt_substs ss) in
       assume (equal (push_env g (PS.nt_subst_env g' (PS.as_nt_substs ss))) g);
       Some d

let st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp_st) (d:st_typing (push_env g g') t c)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : st_typing (push_env g1 g') t c =

  let g2 = diff g1 g in
  let d = st_typing_weakening g g' t c d g2 in
  assert (equal (push_env (push_env g g2) g') (push_env g1 g'));
  d

let veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (d:vprop_equiv (push_env g g') v1 v2)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : vprop_equiv (push_env g1 g') v1 v2 =

  let g2 = diff g1 g in
  let d = veq_weakening g g' d g2 in
  assert (equal (push_env (push_env g g2) g') (push_env g1 g'));
  d


let ss_extends (ss1 ss2:PS.t) =
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

// noeq
// type preamble = {
//   g0 : env;

//   ctxt : vprop;
//   ctxt_typing : vprop_typing g0 ctxt;

//   t : st_term;
//   c : comp_st;

//   uvs : uvs:env { disjoint uvs g0 }
// }

// let pst_env (#g0:env) (uvs:env { disjoint uvs g0 }) (ss:Psubst.t g0) =
//   push_env g0 (psubst_env (filter_ss uvs ss) ss)

// noeq
// type prover_state (preamble:preamble) = {
//   ss : ss:Psubst.t preamble.g0 {
//     well_typed_ss preamble.uvs ss
//   };

//   solved_goals : term;

//   unsolved_goals : list term;

//   remaining_ctxt : list term;

//   steps : st_term;

//   t_typing
//     : st_typing (pst_env preamble.uvs ss)
//                 (Psubst.subst_st_term ss preamble.t)
//                 (Psubst.subst_comp ss preamble.c);

//   unsolved_goals_typing
//     : vprop_typing (pst_env preamble.uvs ss)
//                    (list_as_vprop unsolved_goals);

//   remaining_ctxt_typing
//     : vprop_typing preamble.g0 (list_as_vprop remaining_ctxt);
  
//   steps_typing
//     : st_typing (pst_env preamble.uvs ss)
//                 steps
//                 (ghost_comp
//                    preamble.ctxt
//                    (tm_star (list_as_vprop remaining_ctxt) solved_goals));

//   c_pre_inv
//     : vprop_equiv (pst_env preamble.uvs ss)
//                   (Psubst.subst_term ss (comp_pre preamble.c))
//                   (tm_star (list_as_vprop unsolved_goals) solved_goals);

//   solved_goals_closed : squash (freevars solved_goals `Set.subset`
//                                 dom preamble.g0);
// }

// let pst_extends (#preamble:_) (p1 p2:prover_state preamble) =
//   p1.ss `Psubst.subst_extends` p2.ss

// type prover_t =
//   #preamble:_ ->
//   p:prover_state preamble ->
//   T.Tac (option (p':prover_state preamble { p' `pst_extends` p /\
//                                             p'.unsolved_goals == [] }))

// type prover_step_t =
//   #preamble:_ ->
//   p:prover_state preamble ->
//   prover:prover_t ->
//   T.Tac (option (p':prover_state preamble { p' `pst_extends` p }))

