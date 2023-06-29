module Pulse.Prover.Common

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv

module T = FStar.Tactics

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
  : T.Tac (x:var { None? (lookup g x) } &
           continuation_elaborator
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

val add_elims (#g:env) (#ctxt:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_vprop &
            continuation_elaborator g ctxt g' ctxt')

noeq type preamble = {
  g0 : env;
  
  ctxt : vprop;
  ctxt_typing : vprop_typing g0 ctxt;

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

  uvs : uvs:env { disjoint uvs pg };
  ss : ss:PS.t { well_typed_ss ss uvs pg};

  solved : vprop;
  unsolved : list vprop;

  k : continuation_elaborator preamble.g0 preamble.ctxt
                              pg (list_as_vprop remaining_ctxt * ss.(solved));

  goals_inv : vprop_equiv (push_env pg uvs) preamble.goals (list_as_vprop unsolved * solved);

  solved_inv : squash (freevars ss.(solved) `Set.subset` dom pg);
}

let is_terminal (#preamble:_) (st:prover_state preamble) =
  st.unsolved == []

val prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:vprop_typing g ctxt)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:vprop_typing (push_env g uvs) goals)

  : T.Tac (g1 : env { g1 `env_extends` g /\ disjoint g1 uvs } &
           ss : PS.t { well_typed_ss ss uvs g1 } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 (ss.(goals) * remaining_ctxt))

open Pulse.Checker.Common

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

let add_frame (#g:env) (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
  (frame:vprop)
  : T.Tac (t':st_term &
           c':comp_st { c' == add_frame c frame } &
           st_typing g t' c') = magic ()

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
  (t:st_term) (c:comp_st) (_:st_typing (push_env g g') t c)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : T.Tac (st_typing (push_env g1 g') t c) = magic ()


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

// there will be some side conditions related to the typings
let k_intro_exists (g:env) (u:universe) (b:binder) (p:vprop) (e:term)
  (frame:vprop)
  : T.Tac (continuation_elaborator g (frame * subst_term p [ DT 0 e ])
                                   g (frame * tm_exists_sl u b p)) = magic ()

let intro_exists (#preamble:_) (pst:prover_state preamble)
  (u:universe) (b:binder) (body:vprop)
  (unsolved':list vprop)
  (_:squash (pst.unsolved == (tm_exists_sl u b body)::unsolved'))
  (prover:prover_t)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        is_terminal pst' }) =

  let x = fresh pst.pg in
  let px = b.binder_ppname, x in
  let preamble_sub = {
    g0 = pst.pg;
    ctxt = (list_as_vprop pst.remaining_ctxt) * pst.ss.(pst.solved);
    ctxt_typing = magic ();
    goals = pst.solved * open_term_nv body px * (list_as_vprop unsolved'); 
  } in
  assume (pst.ss.(tm_emp) == tm_emp);
  let pst_sub : prover_state preamble_sub = {
    pg = pst.pg;
    remaining_ctxt = vprop_as_list preamble_sub.ctxt;
    uvs = pst.uvs;
    ss = pst.ss;
    solved = tm_emp;
    unsolved = (vprop_as_list (pst.ss.(pst.solved))) @ [open_term_nv body px] @ unsolved';
    k = magic ();
    goals_inv = magic ();
    solved_inv = ();
  } in

  let pst_sub_terminal = prover pst_sub in
  let pst_sub_terminal_goals_inv
    : vprop_equiv (push_env pst_sub_terminal.pg pst_sub_terminal.uvs)
                  preamble_sub.goals
                  (list_as_vprop [] * pst_sub_terminal.solved) = pst_sub_terminal.goals_inv in
  assert (well_typed_ss pst_sub_terminal.ss pst_sub_terminal.uvs pst_sub_terminal.pg);
  // substitution lemma on pst_sub_terminal_goals_inv
  let pst_sub_terminal_goals_inv
    : vprop_equiv pst_sub_terminal.pg
                  pst_sub_terminal.ss.(preamble_sub.goals)
                  pst_sub_terminal.ss.(pst_sub_terminal.solved) = magic () in
  let k_sub_terminal
    : continuation_elaborator preamble_sub.g0 preamble_sub.ctxt
                              pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt * pst_sub_terminal.ss.(pst_sub_terminal.solved)) =
    pst_sub_terminal.k in
  // replacing pst_sub_terminal.ss.(pst_sub_terminal.solved) with
  // pst_sub_terminal.ss.(preamble_sub.goals) using the equiv relation
  let k_sub_terminal
    : continuation_elaborator preamble_sub.g0 preamble_sub.ctxt
                              pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt * pst_sub_terminal.ss.(preamble_sub.goals)) =
    magic () in
  // substitute preamble_sub.goals
  let k_sub_terminal
    : continuation_elaborator
        preamble_sub.g0 preamble_sub.ctxt
        pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt *
                             pst_sub_terminal.ss.(pst.solved * open_term_nv body px * (list_as_vprop unsolved'))) =
    k_sub_terminal in
  // huh why is this not provable?
  assume (pst_sub_terminal.ss.(pst.solved * open_term_nv body px * (list_as_vprop unsolved')) ==
          pst_sub_terminal.ss.(pst.solved) * pst_sub_terminal.ss.(open_term_nv body px) * pst_sub_terminal.ss.(list_as_vprop unsolved'));
  let witness = pst_sub_terminal.ss.(null_var x) in
  // assume (pst_sub_terminal.ss.(open_term_nv body px) == subst_term (pst_sub_terminal.ss.(body)) [DT 0 witness]);
  // rejig some of the *s in k_sub_terminal
  let k_sub_terminal
    : continuation_elaborator
        preamble_sub.g0 preamble_sub.ctxt
        pst_sub_terminal.pg ((list_as_vprop pst_sub_terminal.remaining_ctxt *
                              pst_sub_terminal.ss.(pst.solved) *
                              pst_sub_terminal.ss.(list_as_vprop unsolved')) *
                             (subst_term (pst_sub_terminal.ss.(body)) [DT 0 witness])) = magic () in
  let k_intro_exists
    : continuation_elaborator
        pst_sub_terminal.pg ((list_as_vprop pst_sub_terminal.remaining_ctxt *
                              pst_sub_terminal.ss.(pst.solved) *
                              pst_sub_terminal.ss.(list_as_vprop unsolved')) *
                             (subst_term (pst_sub_terminal.ss.(body)) [DT 0 witness]))
        pst_sub_terminal.pg ((list_as_vprop pst_sub_terminal.remaining_ctxt *
                              pst_sub_terminal.ss.(pst.solved) *
                              pst_sub_terminal.ss.(list_as_vprop unsolved')) *
                             (tm_exists_sl u (PS.nt_subst_binder b (PS.as_nt_substs pst_sub_terminal.ss)) pst_sub_terminal.ss.(body))) =
    k_intro_exists pst_sub_terminal.pg u (PS.nt_subst_binder b (PS.as_nt_substs pst_sub_terminal.ss)) pst_sub_terminal.ss.(body) witness
      (list_as_vprop pst_sub_terminal.remaining_ctxt *
       pst_sub_terminal.ss.(pst.solved) *
       pst_sub_terminal.ss.(list_as_vprop unsolved')) in
  // // these are all NT substitutions
  // assume (shift_subst (as_subst pst_sub_terminal.ss) == as_subst pst_sub_terminal.ss);
  assume (tm_exists_sl u (PS.nt_subst_binder b (PS.as_nt_substs pst_sub_terminal.ss)) pst_sub_terminal.ss.(body) ==
          pst_sub_terminal.ss.(tm_exists_sl u b body));
  let k_intro_exists
    : continuation_elaborator
        pst_sub_terminal.pg ((list_as_vprop pst_sub_terminal.remaining_ctxt *
                              pst_sub_terminal.ss.(pst.solved) *
                              pst_sub_terminal.ss.(list_as_vprop unsolved')) *
                             (subst_term (pst_sub_terminal.ss.(body)) [DT 0 witness]))
        pst_sub_terminal.pg ((list_as_vprop pst_sub_terminal.remaining_ctxt *
                              pst_sub_terminal.ss.(pst.solved) *
                              pst_sub_terminal.ss.(list_as_vprop unsolved')) *
                             (pst_sub_terminal.ss.(tm_exists_sl u b body))) = k_intro_exists in
  // rejig some stars
  let k_intro_exists
    : continuation_elaborator
        pst_sub_terminal.pg ((list_as_vprop pst_sub_terminal.remaining_ctxt *
                              pst_sub_terminal.ss.(pst.solved) *
                              pst_sub_terminal.ss.(list_as_vprop unsolved')) *
                             (subst_term (pst_sub_terminal.ss.(body)) [DT 0 witness]))
        pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt *
                             pst_sub_terminal.ss.(pst.solved * tm_exists_sl u b body * list_as_vprop unsolved')) = magic () in

  let k_sub_terminal
    : continuation_elaborator
        preamble_sub.g0 preamble_sub.ctxt
        pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt *
                             pst_sub_terminal.ss.(pst.solved * tm_exists_sl u b body * list_as_vprop unsolved')) =
    k_elab_trans k_sub_terminal k_intro_exists in
  // pst.unsolved == tm_exists_sl u b body * list_as_vprop unsolved'
  let k_sub_terminal
    : continuation_elaborator
        preamble_sub.g0 preamble_sub.ctxt
        pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt *
                             pst_sub_terminal.ss.(pst.solved * list_as_vprop pst.unsolved)) = magic () in

  let k_pst
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop pst.remaining_ctxt * pst.ss.(pst.solved)) = pst.k in

  let k_pst
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        preamble_sub.g0 preamble_sub.ctxt = k_pst in

  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt *
                             pst_sub_terminal.ss.(pst.solved * list_as_vprop pst.unsolved)) =
    k_elab_trans k_pst k_sub_terminal in

  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs) preamble.goals (list_as_vprop pst.unsolved * pst.solved) =
    pst.goals_inv in

  assert (pst_sub_terminal.pg `env_extends` pst.pg);
  assert (pst_sub_terminal.uvs `env_extends` pst.uvs);

  // weakening of goals_inv
  let goals_inv
    : vprop_equiv (push_env pst_sub_terminal.pg pst_sub_terminal.uvs)
                  preamble.goals
                  (pst.solved * list_as_vprop pst.unsolved) = magic () in

  // substitution lemma
  let goals_inv
    : vprop_equiv pst_sub_terminal.pg
                  (pst_sub_terminal.ss.(preamble.goals))
                  (pst_sub_terminal.ss.(pst.solved * list_as_vprop pst.unsolved)) = magic () in

  // replace in k
  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt *
                             pst_sub_terminal.ss.(preamble.goals)) =
    magic () in

  let pst' : prover_state preamble = {
    pg = pst_sub_terminal.pg;
    remaining_ctxt = pst_sub_terminal.remaining_ctxt;
    uvs = pst_sub_terminal.uvs;
    ss = pst_sub_terminal.ss;
    solved = preamble.goals;
    unsolved = [];
    k;
    goals_inv = magic ();
    solved_inv = magic (); // what is this? is this a dynamic check?
  } in

  pst'

let try_match_pq (g:env) (uvs:env { disjoint uvs g})
  (#p:vprop) (p_typing:vprop_typing g p)
  (#q:vprop) (q_typing:vprop_typing (push_env g uvs) q)
  : T.Tac (option (ss:PS.t { well_typed_ss ss uvs g /\
                             PS.dom ss `Set.subset` freevars q } &
                   vprop_equiv g p ss.(q))) = magic ()

let compose_ss (ss1 ss2:PS.t) : PS.t = magic ()

let match_step (#preamble:preamble) (pst:prover_state preamble)
  (p:vprop) (remaining_ctxt':list vprop)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.remaining_ctxt == p::remaining_ctxt' /\
             pst.unsolved == q::unsolved'))
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

let q_ss = pst.ss.(q) in
assume (freevars q_ss `Set.disjoint` PS.dom pst.ss);

let ropt = try_match_pq pst.pg pst.uvs #p (magic ()) #q_ss (magic ()) in
match ropt with
| None -> None
| Some (| ss_q, veq |) ->
  assert (PS.dom ss_q `Set.disjoint` PS.dom pst.ss);
  assert (well_typed_ss ss_q pst.uvs pst.pg);

  let ss_new = compose_ss ss_q pst.ss in
  assume (well_typed_ss ss_new pst.uvs pst.pg);

  let veq
    : vprop_equiv pst.pg p (ss_q.(pst.ss.(q))) = veq in
  assume (ss_q.(pst.ss.(q)) == ss_new.(q));
  let veq : vprop_equiv pst.pg p ss_new.(q) = veq in
  
  let remaining_ctxt_new = remaining_ctxt' in
  let solved_new = q * pst.solved in
  let unsolved_new = unsolved' in

  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop pst.remaining_ctxt * pst.ss.(pst.solved)) = pst.k in

  assume (pst.ss.(pst.solved) == ss_new.(pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop (p::remaining_ctxt') * ss_new.(pst.solved)) = pst.k in
  
  // some *s
  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop remaining_ctxt' * (p * ss_new.(pst.solved))) = magic () in
  
  // using veq of p and ss_new.(q)
  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop remaining_ctxt' * (ss_new.(q) * ss_new.(pst.solved))) = magic () in

  assume (ss_new.(q) * ss_new.(pst.solved) == ss_new.(q * pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop remaining_ctxt_new * (ss_new.(solved_new))) = k in

  let pst' : prover_state preamble =
    { pst with remaining_ctxt=remaining_ctxt_new;
               ss=ss_new;
               solved=solved_new;
               unsolved=unsolved_new;
               k;
               goals_inv=magic ();
               solved_inv=magic () } in  // this solved_inv ... runtime check or inversion?
  
  assume (ss_new `ss_extends` pst.ss);
  Some pst'





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

