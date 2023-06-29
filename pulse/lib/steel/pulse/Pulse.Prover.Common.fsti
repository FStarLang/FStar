module Pulse.Prover.Common

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Util

open Pulse.Checker.Auto.Elims

module T = FStar.Tactics

module Psubst = Pulse.Prover.Substs

let vprop_typing (g:env) (t:term) = tot_typing g t tm_vprop

noeq type preamble = {
  g0 : env;
  
  ctxt : vprop;
  ctxt_typing : vprop_typing g0 ctxt;

  goals : vprop;
}

type ss_t = Map.t var term

let as_subst (ss:ss_t) : subst = magic ()

let shift (ss:ss_t) = shift_subst (as_subst ss)

let op_Array_Access (ss:ss_t) (t:term) =
  subst_term t (as_subst ss)

let op_String_Access = Map.sel

let op_Star = tm_star

let well_typed_ss (ss:ss_t) (uvs g:env) =
  forall (x:var).
  Map.contains ss x ==> (Set.mem x (dom uvs) /\
                         tot_typing g ss.[x] (ss.(Some?.v (lookup uvs x))))

noeq type prover_state (preamble:preamble) = {
  pg : g:env { g `env_extends` preamble.g0 };

  remaining_ctxt : list vprop;

  uvs : uvs:env { disjoint uvs pg };
  ss : ss:ss_t { well_typed_ss ss uvs pg};

  solved : vprop;
  unsolved : list vprop;

  k : continuation_elaborator preamble.g0 preamble.ctxt
                              pg (list_as_vprop remaining_ctxt * ss.(solved));

  goals_inv : vprop_equiv (push_env pg uvs) preamble.goals (list_as_vprop unsolved * solved);

  solved_inv : squash (freevars ss.(solved) `Set.subset` dom pg);
}

let covers (ss:ss_t) (uvs:env) =
  Set.equal (Map.domain ss) (dom uvs)

let is_terminal (#preamble:_) (st:prover_state preamble) =
  st.unsolved == [] /\ covers st.ss st.uvs


let prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:vprop_typing g ctxt)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:vprop_typing (push_env g uvs) goals)

  : T.Tac (g1 : env { g1 `env_extends` g /\ disjoint g1 uvs } &
           ss : ss_t { well_typed_ss ss uvs g1 } &
           remaining_ctxt : vprop &
           k : continuation_elaborator g ctxt g1 (ss.(goals) * remaining_ctxt)) = magic ()

open Pulse.Checker.Common

let check_stapp_no_ctxt (g:env) (t:st_term { Tm_STApp? t.term })
  : T.Tac (uvs : env { disjoint uvs g } &
           t:st_term &
           c:comp_st &
           st_typing (push_env g uvs) t c) = magic ()

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
  (_:st_typing (push_env g uvs) t c)
  (ss:ss_t { well_typed_ss ss uvs g })
  : T.Tac (st_typing g (subst_st_term t (as_subst ss)) (subst_comp c (as_subst ss))) = magic ()

let st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp_st) (_:st_typing (push_env g g') t c)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : T.Tac (st_typing (push_env g1 g') t c) = magic ()

// This is implemented in Pulse.Checker.Bind
let  mk_bind' (g:env)
              (pre:term)
              (e1:st_term)
              (e2:st_term)
              (c1:comp_st)
              (c2:comp_st)
              (px:nvar { ~ (Set.mem (snd px) (dom g)) })
              (d_e1:st_typing g e1 c1)
              (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1)))
              (d_e2:st_typing (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2)
              (post_hint:post_hint_opt g { comp_post_matches_hint c2 post_hint })
              (_:squash (
                 let _, x = px in
                 comp_pre c1 == pre /\
                 None? (lookup g x) /\
                 (~(x `Set.mem` freevars_st e2)) /\
                 open_term (comp_post c1) x == comp_pre c2))
  : T.Tac (checker_result_t g pre post_hint) = magic ()

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"
let check_bind
  (g:env)
  (t:st_term {Tm_Bind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let Tm_Bind { binder=b; head=e1; body=e2 } = t.term in

  match e1.term with
  | Tm_STApp _ ->
    let (| uvs1, e1, c1, d1 |) = check_stapp_no_ctxt g e1 in
    let c10 = c1 in
    // magic is comp_pre c1 typing, get from inversion of d1 
    let (| g1, ss1, remaining_pre, k |) =
      prove pre_typing uvs1 #(comp_pre c1) (magic ()) in
    let x = fresh g1 in
    let px = b.binder_ppname, x in
    // TODO: if the binder is annotated, check subtyping
    let g2 = push_binding g1 x b.binder_ppname ss1.(comp_res c1) in
    let pre_e2 = open_term_nv (subst_term (comp_post c1) (shift ss1)) px * remaining_pre in
    assert (g2 `env_extends` g1);
    // magic is the typing of pre_e2 in g2
    // remaining_pre is well-typed, may be prove function can return it?
    // well-typedness of open_term?
    let (| e2, c2, d2 |) =
      check g2 (open_st_term_nv e2 px) pre_e2 (magic ()) (extend_post_hint_opt_g g post_hint g2) in

    if not (stateful_comp c2)
    then fail g None "Bind: c2 is not st"
    else
      let d1 = st_typing_weakening g uvs1 e1 c1 d1 g1 in 
      // g1 |- ss1 e1 : ss1 c1
      let d1 = st_typing_subst g1 uvs1 e1 c1 d1 ss1 in
      let (| e1, c1, d1 |) = add_frame d1 remaining_pre in

      assert (comp_pre c1 == ss1.(comp_pre c10) * remaining_pre);
      assert (comp_res c1 == ss1.(comp_res c10));
      assert (None? (lookup g1 x));
      assert (comp_post c1 == (subst_term (comp_post c10) (shift ss1)) * remaining_pre);
      assume (open_term remaining_pre x == remaining_pre);
      assert (open_term (comp_post c1) x == comp_pre c2);
   
      let e2_closed = close_st_term e2 x in
      assume (open_st_term e2_closed x == e2);

      let r = mk_bind' g1 (comp_pre c1) e1 e2_closed c1 c2 px d1 (magic ()) d2 post_hint () in

      k post_hint r

  | _ -> fail g None "Bind: e1 is not an stapp"

let ss_extends (ss1 ss2:ss_t) =
  Set.subset (Map.domain ss2) (Map.domain ss1) /\
  (forall (x:var). Map.contains ss2 x ==> ss1.[x] == ss2.[x])

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
  assert (pst_sub_terminal.ss `covers` pst_sub_terminal.uvs);
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
                             (tm_exists_sl u (subst_binder b (as_subst pst_sub_terminal.ss)) pst_sub_terminal.ss.(body))) =
    k_intro_exists pst_sub_terminal.pg u (subst_binder b (as_subst pst_sub_terminal.ss)) pst_sub_terminal.ss.(body) witness
      (list_as_vprop pst_sub_terminal.remaining_ctxt *
       pst_sub_terminal.ss.(pst.solved) *
       pst_sub_terminal.ss.(list_as_vprop unsolved')) in
  // these are all NT substitutions
  assume (shift_subst (as_subst pst_sub_terminal.ss) == as_subst pst_sub_terminal.ss);
  assert (tm_exists_sl u (subst_binder b (as_subst pst_sub_terminal.ss)) pst_sub_terminal.ss.(body) ==
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
  : T.Tac (option (ss:ss_t { well_typed_ss ss uvs g /\
                             Map.domain ss `Set.subset` freevars q } &
                   vprop_equiv g p ss.(q))) = magic ()

let compose_ss (ss1 ss2:ss_t) : ss_t = magic ()

let match_step (#preamble:preamble) (pst:prover_state preamble)
  (p:vprop) (remaining_ctxt':list vprop)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.remaining_ctxt == p::remaining_ctxt' /\
             pst.unsolved == q::unsolved'))
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

let q_ss = pst.ss.(q) in
assume (freevars q_ss `Set.disjoint` Map.domain pst.ss);

let ropt = try_match_pq pst.pg pst.uvs #p (magic ()) #q_ss (magic ()) in
match ropt with
| None -> None
| Some (| ss_q, veq |) ->
  assert (Map.domain ss_q `Set.disjoint` Map.domain pst.ss);
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

