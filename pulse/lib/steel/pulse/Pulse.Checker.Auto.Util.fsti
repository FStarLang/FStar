module Pulse.Checker.Auto.Util

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory

#push-options "--admit_smt_queries true"  // TODO: REMOVE THIS
let continuation_elaborator (g:env) (ctxt:term)
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
  (ctxt_pre1_typing:tot_typing g (Tm_Star ctxt (comp_pre c1)) Tm_VProp)
  : T.Tac (x:var { None? (lookup g x) } &
           continuation_elaborator
             g                                (Tm_Star ctxt (comp_pre c1))
             (push_binding g x (comp_res c1)) (Tm_Star (open_term (comp_post c1) x) ctxt))

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
  tot_typing g v Tm_VProp ->
  T.Tac (option (t:st_term &
                 c:comp { stateful_comp c /\ comp_pre c == v } &
                 st_typing g t c))

val add_elims (#g:env) (#ctxt:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')
#pop-options  // TODO: REMOVE THIS


open Pulse.Checker.VPropEquiv

module Psubst = Pulse.Prover.Substs

let vprop_typing (g:env) (t:term) = tot_typing g t Tm_VProp

noeq
type preamble = {
  g0 : env;

  ctxt : vprop;
  ctxt_typing : vprop_typing g0 ctxt;

  t : st_term;
  c : comp_st;

  uvs : uvs:env { disjoint uvs g0 }
}

let ghost_comp pre post = 
  C_STGhost Tm_EmpInames { u=u_zero; res=tm_unit; pre; post }

// let env_of (#g0:_) (uvs_pending:_) (ss:Psubst.t g0) =
//   push_env g0 (psubst_env uvs_pending ss)

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

  used_ctxt : term;

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
                   (Tm_Star (list_as_vprop remaining_ctxt) solved_goals));

  c_pre_inv
    : vprop_equiv (pst_env preamble.uvs ss)
                  (Psubst.subst_term ss (comp_pre preamble.c))
                  (Tm_Star (list_as_vprop unsolved_goals) solved_goals);

  solved_goals_closed : squash (freevars solved_goals `Set.subset`
                                dom preamble.g0);
}

let pst_extends (#preamble:_) (p1 p2:prover_state preamble) =
  p2.uvs_all == p1.uvs_all /\
  p2.ss `Psubst.subst_extends` p1.ss

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

let idem_steps (g:env) (ctxt:vprop)
  : t:st_term &
    st_typing g t (ghost_comp ctxt (Tm_Star (list_as_vprop (vprop_as_list ctxt))
                                            Tm_Emp)) = magic ()

val vprop_as_list_of_list_as_vprop (l:list vprop)
  : Lemma (vprop_as_list (list_as_vprop l) == l)
          [SMTPat (vprop_as_list (list_as_vprop l))]

val list_as_vprop_of_vprop_as_list (p:vprop)
  : Lemma (list_as_vprop (vprop_as_list p) == p)
          [SMTPat (list_as_vprop (vprop_as_list p))]

let check_ss_covers_g' (ss:nt_subst) (g':env)
  : b:bool { b ==> ss_covers_g' ss g' } = admit ()

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y === x} = x

#push-options "--z3rlimit_factor 2 --fuel 1 --ifuel 2"
// let prove_precondition (#g:env) (#ctxt:term)
//   (ctxt_typing:tot_typing g ctxt Tm_VProp)
//   (#t:st_term) (#c:comp_st)
//   (t_typing:st_typing g t c)
//   (prover:prover_t)
//   : T.Tac (option (t:st_term &
//                    c:comp_st { comp_pre c == ctxt } &
//                    st_typing g t c)) =

//   let preamble = {
//     initial_env = g;
//     initial_ctxt = ctxt;
//     initial_ctxt_typing = ctxt_typing;
//     t;
//     c
//   } in

//   let uvs = mk_env (fstar_env g) in
//   let ss : nt_subst = [] in
//   let solved_goals = Tm_Emp in
//   let remaining_goals = vprop_as_list (comp_pre c) in
//   let remaining_ctxt = vprop_as_list ctxt in

//   let (| proof_steps, proof_steps_typing |) = idem_steps g ctxt in

//   assert (equal (push_env preamble.initial_env uvs) g);

//   let t_typing : st_typing (push_env preamble.initial_env uvs) t c = t_typing in
  
//   // invert t_typing to get c typing to get c pre typing
//   let remaining_goals_typing
//     : vprop_typing (push_env preamble.initial_env uvs) (comp_pre c) =
//     magic () in
//   let remaining_goals_typing
//     : vprop_typing (push_env preamble.initial_env uvs) (list_as_vprop remaining_goals) =
//     remaining_goals_typing in

//   let remaining_ctxt_typing
//     : vprop_typing preamble.initial_env (list_as_vprop remaining_ctxt) =
//     ctxt_typing in

//   let proof_steps_typing : st_typing
//     (push_env preamble.initial_env uvs)
//     proof_steps
//     (ghost_comp
//        preamble.initial_ctxt
//        (Tm_Star (list_as_vprop remaining_ctxt) (subst_term solved_goals ss))) =
//     proof_steps_typing in

//   // matched is empty  
//   let c_pre_invariant
//     : vprop_equiv (push_env preamble.g0 uvs) (comp_pre preamble.c)
//                         (Tm_Star (list_as_vprop unmatched) matched) =
//     magic () in

//   let p = {uvs;ss;matched;unmatched;remaining;steps;
//            t_typing;unmatched_typing;remaining_typing;steps_typing;
//            veq;ss_closes_matched_uvs = ()} in

//   let p = prover p in
//   match p with
//   | None -> None
//   | Some p ->
//     assert (p.unmatched == []);

  //   let psteps_typing : st_typing (push_env preamble.g0 p.uvs) p.steps
  //     (ghost_comp preamble.ctxt
  //                 (Tm_Star (list_as_vprop p.remaining) (subst_term p.matched p.ss))) = p.steps_typing in
  //   assert (well_typed_ss preamble.g0 p.uvs p.ss);
  //   if check_ss_covers_g' p.ss p.uvs
  //   then begin
  //     assert (equal p.uvs (push_env p.uvs (mk_env (fstar_env preamble.g0))));
  //     let psteps_typing : st_typing
  //       (push_env preamble.g0 (push_env p.uvs (mk_env (fstar_env preamble.g0))))
  //       p.steps
  //       (ghost_comp preamble.ctxt
  //                   (Tm_Star (list_as_vprop p.remaining) (subst_term p.matched p.ss))) =
  //       coerce_eq psteps_typing () in
  //     // apply substitution lemma
  //     let psteps_typing : st_typing
  //       (push_env preamble.g0 (subst_env (mk_env (fstar_env preamble.g0)) p.ss))
  //       (subst_st_term p.steps p.ss)
  //       (subst_comp (ghost_comp preamble.ctxt
  //                               (Tm_Star (list_as_vprop p.remaining) (subst_term p.matched p.ss))) p.ss) =
  //       st_typing_subst preamble.g0 p.uvs (mk_env (fstar_env preamble.g0))
  //         psteps_typing
  //         p.ss in
  //     // substituting in an empty env returns an empty env
  //     assume (equal (subst_env (mk_env (fstar_env preamble.g0)) p.ss)
  //                   (mk_env (fstar_env preamble.g0)));
  //     assert (equal (push_env preamble.g0 (subst_env (mk_env (fstar_env preamble.g0)) p.ss))
  //             preamble.g0);
  //     // NT substitutions remain invariant under shifting
  //     assume (shift_subst p.ss == p.ss);

  //     // if no free uvs, substitution is an identity
  //     assert (freevars (subst_term p.matched p.ss) `Set.disjoint` dom uvs);
  //     assume (subst_term (subst_term p.matched p.ss) p.ss ==
  //             subst_term p.matched p.ss);

  //     // preamble.ctxt is well-typed in g0
  //     assume (freevars preamble.ctxt `Set.subset` (dom preamble.g0));
  //     assert (freevars preamble.ctxt `Set.disjoint` dom uvs);
  //     assume (subst_term preamble.ctxt p.ss == preamble.ctxt);

  //     let psteps_typing : st_typing
  //       preamble.g0
  //       (subst_st_term p.steps p.ss)
  //       (ghost_comp preamble.ctxt
  //                   (Tm_Star (subst_term (list_as_vprop p.remaining) p.ss)
  //                            (subst_term p.matched p.ss))) = psteps_typing in

  //     let veq : vprop_equiv (push_env preamble.g0 p.uvs)
  //                           (comp_pre preamble.c)
  //                           (Tm_Star (list_as_vprop []) p.matched) = p.veq in
  //     // simplify veq by normalizing list_as_vprop []
  //     let veq : vprop_equiv (push_env preamble.g0 p.uvs)
  //                           (comp_pre preamble.c)
  //                           p.matched = magic () in
  //     // apply substitution lemma to veq
  //     let veq : vprop_equiv preamble.g0 (subst_term (comp_pre preamble.c) p.ss)
  //                                       (subst_term p.matched p.ss) =
  //       veq_subst preamble.g0 p.uvs (mk_env (fstar_env preamble.g0)) veq p.ss in

  //     // in psteps typing, replace subst_term p.matched p.ss with subst_term (comp_pre preamble.c) p.ss
  //     let psteps_typing : st_typing
  //       preamble.g0
  //       (subst_st_term p.steps p.ss)
  //       (ghost_comp preamble.ctxt
  //                   (Tm_Star (subst_term (list_as_vprop p.remaining) p.ss)
  //                            (subst_term (comp_pre preamble.c) p.ss))) = magic () in

  //     let t_typing : st_typing (push_env preamble.g0 p.uvs) preamble.t preamble.c =
  //       p.t_typing in

  //     // apply substitution lemma
  //     let t_typing : st_typing preamble.g0
  //                              (subst_st_term preamble.t p.ss)
  //                              (subst_comp preamble.c p.ss) =
  //       st_typing_subst preamble.g0 p.uvs (mk_env (fstar_env preamble.g0))
  //         t_typing
  //         p.ss in

  //     assert (comp_pre (subst_comp preamble.c p.ss) == subst_term (comp_pre preamble.c) p.ss);
 
  //     // bind psteps and t

  //     admit ()
  //   end
  // else None
#pop-options

let intro_exists_sub_prover_state (#preamble:_) (p:prover_state preamble)
  (u:universe) (b:binder) (body:vprop)
  (exists_typing:tot_typing (push_env preamble.g0 p.uvs) (Tm_ExistsSL u b body) Tm_VProp)
  : v:var &
    p:prover_state_preamble &
    prover_state p =

  let x = fresh (push_env preamble.g0 p.uvs) in

  let preamble = {
    g0 = preamble.g0;
    ctxt = list_as_vprop p.remaining;
    ctxt_typing = p.remaining_typing;
    t = wr (Tm_IntroExists {
      erased=false;
      p=Tm_ExistsSL u b body;
      witnesses=[null_var x];
      should_check=should_check_false });
    c = comp_intro_exists u b body (null_var x);
  } in

  let uvs = push_binding p.uvs x b.binder_ty in
  let ss = p.ss in
  let matched = Tm_Emp in
  let unmatched = [open_term' body (null_var x) 0] in
  let remaining = p.remaining in
  let (| steps, steps_typing |) = idem_steps (push_env preamble.g0 uvs) (list_as_vprop p.remaining) in
  
  assert (equal (push_binding (push_env preamble.g0 p.uvs) x b.binder_ty)
                (push_env preamble.g0 uvs));
  let t_typing : st_typing (push_env preamble.g0 uvs) preamble.t preamble.c = T_IntroExists
    (push_env preamble.g0 uvs)
    u
    b
    body
    (null_var x)
    (magic ())
    (tot_typing_weakening x b.binder_ty exists_typing)
    (magic ()) in

  let unmatched_typing : tot_typing (push_env preamble.g0 uvs) (list_as_vprop unmatched) Tm_VProp =
    magic () in

  let remaining_typing : tot_typing preamble.g0 (list_as_vprop remaining) Tm_VProp = p.remaining_typing in

  assume (subst_term matched ss == Tm_Emp);
  let steps_typing : st_typing
    (push_env preamble.g0 uvs)
    steps
    (ghost_comp preamble.ctxt
                (Tm_Star (list_as_vprop remaining) (subst_term matched ss))) = steps_typing in

  let veq : vprop_equiv (push_env preamble.g0 uvs)
                        (open_term' body (null_var x) 0)
                        (Tm_Star (list_as_vprop unmatched) matched) = magic () in


  (| x,
     preamble, {
    uvs; ss;
    matched; unmatched; remaining; steps;
    t_typing; unmatched_typing; remaining_typing; steps_typing; veq; ss_closes_matched_uvs = ()
  } |)

#push-options "--z3rlimit_factor 10 --fuel 2 --ifuel 2"
let intro_exists_step (#preamble:_) (p:prover_state preamble)
  (u:universe) (b:binder) (body:vprop) (unmatched':list vprop)
  (_:squash (p.unmatched == (Tm_ExistsSL u b body) :: unmatched'))
  (prover:prover_t)
  : T.Tac (option (p':prover_state preamble { p'.uvs `env_extends` p.uvs })) =
  

  let (| x, sub_prover_preamble, sub_prover_state |) = intro_exists_sub_prover_state 
    p u b body (magic ()) in

  let sub_prover_state = prover sub_prover_state in

  match sub_prover_state with
  | None -> None
  | Some sub_prover_state ->
    let sub_steps_typing
      : st_typing (push_env preamble.g0 sub_prover_state.uvs)
                  sub_prover_state.steps
                  (ghost_comp (list_as_vprop p.remaining)
                              (Tm_Star (list_as_vprop sub_prover_state.remaining)
                                       (subst_term sub_prover_state.matched sub_prover_state.ss))) =
      sub_prover_state.steps_typing in
    
    let sub_veq : vprop_equiv (push_env preamble.g0 sub_prover_state.uvs)
                              (comp_pre sub_prover_preamble.c)
                              (Tm_Star (list_as_vprop []) sub_prover_state.matched) =
      sub_prover_state.veq in
    // normalize list_as_vprop []
    let sub_veq : vprop_equiv (push_env preamble.g0 sub_prover_state.uvs)
                              (comp_pre sub_prover_preamble.c)
                              sub_prover_state.matched = magic () in
    // PARTIAL SUBSTITUTION STEP, APPLY THE SUBSTITUTION BUT KEEP ENV SAME
    assume (push_env preamble.g0 sub_prover_state.uvs ==
            push_env preamble.g0 (push_env sub_prover_state.uvs (mk_env (fstar_env preamble.g0))));
    assume (subst_env (mk_env (fstar_env preamble.g0)) sub_prover_state.ss == mk_env (fstar_env preamble.g0));
    let sub_veq : vprop_equiv (push_env preamble.g0 (push_env sub_prover_state.uvs (mk_env (fstar_env preamble.g0))))
                              (comp_pre sub_prover_preamble.c)
                              sub_prover_state.matched = coerce_eq sub_veq () in
    let sub_veq : vprop_equiv (push_env preamble.g0 (push_env sub_prover_state.uvs (subst_env (mk_env (fstar_env preamble.g0)) sub_prover_state.ss)))
                              (subst_term (comp_pre sub_prover_preamble.c) sub_prover_state.ss)
                              (subst_term sub_prover_state.matched sub_prover_state.ss) =
      veq_subst_partial
        preamble.g0
        sub_prover_state.uvs
        (mk_env (fstar_env preamble.g0))
        sub_veq
        sub_prover_state.ss in
    let sub_veq : vprop_equiv (push_env preamble.g0 sub_prover_state.uvs)
                              (subst_term (comp_pre sub_prover_preamble.c) sub_prover_state.ss)
                              (subst_term sub_prover_state.matched sub_prover_state.ss) =
      coerce_eq sub_veq () in

    // use sub_veq with sub_steps_typing
    let sub_steps_typing
      : st_typing (push_env preamble.g0 sub_prover_state.uvs)
                  sub_prover_state.steps
                  (ghost_comp (list_as_vprop p.remaining)
                              (Tm_Star (list_as_vprop sub_prover_state.remaining)
                                       (subst_term (comp_pre sub_prover_preamble.c) sub_prover_state.ss))) =
      magic () in

    let t_typing
      : st_typing (push_env preamble.g0 sub_prover_state.uvs)
                  sub_prover_preamble.t
                  sub_prover_preamble.c = sub_prover_state.t_typing in

    // similar manipulations and PARTIAL SUBSTITUTIONS LEMMA ON st_typing, to get:
    let t_typing
      : st_typing (push_env preamble.g0 sub_prover_state.uvs)
                  (subst_st_term sub_prover_preamble.t sub_prover_state.ss)
                  (subst_comp sub_prover_preamble.c sub_prover_state.ss) = magic () in

    assert (sub_prover_preamble.c ==
            ghost_comp (comp_pre sub_prover_preamble.c)
                       (Tm_ExistsSL u b body));
    // NT substitutions are invariant under shifting
    assume (shift_subst sub_prover_state.ss == sub_prover_state.ss);
    assert (subst_comp sub_prover_preamble.c sub_prover_state.ss ==
            ghost_comp (subst_term (comp_pre sub_prover_preamble.c) sub_prover_state.ss)
                       (subst_term (Tm_ExistsSL u b body) sub_prover_state.ss));

    // we have:
    // g0, uvs |- { p.remaining } sub.steps { sub.remaining * ss (pre subpreamble.c)}
    // and
    // g0, uvs |- { ss (pre subpreamble.c) } ss sub.t { ss (Tm_ExistsSL u b body) }
    // we can bind these to get:
    //
    // g0, uvs |- { p.remaining } bind { sub.remaining * ss (Tm_ExistsSL u b body) }
    let sub_steps : st_term = magic () in
    let sub_steps_typing
      : st_typing (push_env preamble.g0 sub_prover_state.uvs)
                  sub_steps
                  (ghost_comp (list_as_vprop p.remaining)
                              (Tm_Star (list_as_vprop sub_prover_state.remaining)
                                       (subst_term (Tm_ExistsSL u b body) sub_prover_state.ss))) = magic () in

    // now stitch these steps in the original prover we got

    let psteps_typing
      : st_typing (push_env preamble.g0 p.uvs)
                  p.steps
                  (ghost_comp preamble.ctxt
                              (Tm_Star (list_as_vprop p.remaining) (subst_term p.matched p.ss))) = p.steps_typing in

    ss_extends_subst preamble.g0 p.uvs sub_prover_state.uvs p.ss sub_prover_state.ss p.matched;
    assert (subst_term p.matched p.ss == subst_term p.matched sub_prover_state.ss);
    
    let psteps_typing
      : st_typing (push_env preamble.g0 p.uvs)
                  p.steps
                  (ghost_comp preamble.ctxt
                              (Tm_Star (list_as_vprop p.remaining) (subst_term p.matched sub_prover_state.ss))) = p.steps_typing in

    assert (sub_prover_state.uvs `env_extends` p.uvs);
    // weakening of gamma
    let psteps_typing
      : st_typing (push_env preamble.g0 sub_prover_state.uvs)
                  p.steps
                  (ghost_comp preamble.ctxt
                              (Tm_Star (list_as_vprop p.remaining) (subst_term p.matched sub_prover_state.ss))) =
        magic () in

    // we have:
    // g0, uvs |- { preamble.ctxt } p.steps { p.remaining * sub_prover_state.ss p.matched }
    // and
    // g0, uvs |- { p.remaining } sub_steps { sub_prover_state.remaining * sub_prover_state.ss (Tm_ExistsSL u b body) }
    //
    // we can bind these to get:
    //
    // g0, uvs |- { preamble.ctxt } bind { sub_prover_state.remaining * sub_prover_state.ss (exists::p.matched) }
    let steps : st_term = magic () in
    let steps_typing
      : st_typing (push_env preamble.g0 sub_prover_state.uvs)
                  steps
                  (ghost_comp preamble.ctxt
                              (Tm_Star (list_as_vprop sub_prover_state.remaining)
                                       (subst_term (Tm_Star (Tm_ExistsSL u b body) p.matched) sub_prover_state.ss))) =
      magic () in

    let uvs = sub_prover_state.uvs in
    let ss = sub_prover_state.ss in
    let matched = Tm_Star (Tm_ExistsSL u b body) p.matched in
    let unmatched = unmatched' in
    let remaining = sub_prover_state.remaining in

    assume ((push_env preamble.g0 uvs) `env_extends` push_env preamble.g0 p.uvs);

    // weakening of gamma
    let t_typing : st_typing (push_env preamble.g0 uvs) preamble.t preamble.c = magic () in

    // derive from p.unmatched typing and weakening of gamma
    let unmatched_typing
      : tot_typing (push_env preamble.g0 uvs) (list_as_vprop unmatched) Tm_VProp = magic () in

    let remaining_typing
      : tot_typing preamble.g0 (list_as_vprop remaining) Tm_VProp = sub_prover_state.remaining_typing in

    let steps_typing
      : st_typing (push_env preamble.g0 uvs)
                  steps
                  (ghost_comp preamble.ctxt
                              (Tm_Star (list_as_vprop remaining)
                                       (subst_term matched ss))) = steps_typing in

    // move Tm_ExistsSL from unmatched to matched and weaken gamma
    let veq : vprop_equiv (push_env preamble.g0 uvs)
                          (comp_pre preamble.c)
                          (Tm_Star (list_as_vprop unmatched) matched) = magic () in

    // TODO: THIS NEEDS TO BE A RUNTIME CHECK THAT WE CLOSED EXISTS
    assume (freevars (subst_term (Tm_ExistsSL u b body) sub_prover_state.ss) `Set.subset` dom preamble.g0);

    Some ({
      uvs; ss;
      matched; unmatched; remaining; steps;
      t_typing; unmatched_typing; remaining_typing; steps_typing; veq; ss_closes_matched_uvs = ()
    })




// let vprop_typing g v = tot_typing g v Tm_VProp

// let ghost_comp pre post = 
//   C_STGhost Tm_EmpInames { u=u_zero; res=tm_unit; pre; post }

// open Pulse.Checker.VPropEquiv


// ///// Sketch of the new prover /////

// val dom_env (g:env) : Set.set var
// type typ = term

// // uvars with their types
// type uvs_t = Map.t var typ

// type substitution = Map.t var term

// val apply_ss (s:substitution) (t:term) : term
// val apply_ss_st (s:substitution) (t:st_term) : st_term
// val apply_c (s:substitution) (c:comp) : comp

// let uvars (t:term) (uvs:uvs_t) : Set.set var =
//   Set.intersect (freevars t) (Map.domain uvs)
// let uvars_st (t:st_term) (uvs:uvs_t) : Set.set var =
//   Set.intersect (freevars_st t) (Map.domain uvs)

// val env_contains (g:env) (x:var) (t:typ) : prop

// let set_difference (#a:eqtype) (s1 s2:Set.set a) =
//   Set.intersect s1 (Set.complement s2)


// //
// // In the prover state we maintain two environments,
// //   g0: the environment when we enter the prover, it doesn't have any uvars
// //    g: the current environment, may have names which are used as uvars
// //

// // TODO: we need to add a notion of well-typed env
// // and maintain that
// let uvs_invariant (g0 g:env) (uvs:uvs_t) : prop =
//   g `env_extends` g0 /\
//   Set.equal (set_difference (dom_env g) (dom_env g0)) (Map.domain uvs) /\
//   (forall (x:var). Map.contains uvs x ==>
//                    env_contains g x (Map.sel uvs x))

// //
// // The preamble remains fixed as prover state is transformed by steps
// //
// noeq
// type prover_state_preamble = {
//   // top-level entry env, no uvars
//   // when we enter the prover
//   // env into which we will elaborate the proof steps
//   // also the env in which the ctxt is well-typed
//   // initial_env
//   g0:env;
//   // current_env (g0 + uvars)
//   g:env;
//   // initial context
//   ctxt:vprop;
//   // ctxt is well-typed in g0
//   // we never introduce uvars in the ctxt
//   // initial_ctxt_typing
//   ctxt_typing:vprop_typing g0 ctxt;
//   // term whose precondition is the goal
//   t:st_term;
//   // comp for t
//   c:comp_st;
//   // t and c however may contain uvars
//   t_typing:st_typing g t c;

//   // set of uvars and their types that we have introduced so far
//   uvs:uvs_t;
//   // uvars are well-typed in g
//   uvs_props:squash (uvs_invariant g0 g uvs);
// }

// //
// // TODO:
// //   would like to have this: freevars t in g, and no uvars in t, then freevars t in g0
// //

// //
// // Solutions to uvars are closed in g0 --- no uvars in them
// //

// // TODO: this doesn't allow for dependent uvars,
// //   type of a uvar depending on another uvar
// // We need to close the telescope when stating this
// // Perhaps better to keep uvars and substs also as env,
// //   so that we get well-formedness for free
// let well_typed_substitution (g0:env) (uvs:uvs_t) (ss:substitution) : prop =
//   dom_env g0 `Set.disjoint` Map.domain uvs /\
//   (forall (x:var). Map.contains ss x ==>
//                    (Map.contains uvs x /\
//                     tot_typing g0 (Map.sel ss x) (Map.sel uvs x)))

// noeq
// type prover_state (preamble:prover_state_preamble) = {
//   // things in cpre that we have solved
//   // rename to solved_conjuncts
//   matched:term;
//   // remaining things in cpre
//   // goals
//   unmatched:list term;
//   // context remaining that we can match from
//   // remaining_ctxt
//   remaining:list term;
//   // the proof steps we have accumulated so far
//   // proof_steps
//   steps:st_term;

//   // uvars -> terms
//   ss:substitution;

//   // remaining is well-typed in g0
//   // remaining_ctxt_typing
//   remaining_typing:vprop_typing preamble.g0 (list_as_vprop remaining);

//   // goals_typing
//   unmatched_typing:vprop_typing preamble.g (list_as_vprop unmatched);

//   // steps are well-typed in g0
//   // proof_steps_typing
//   steps_typing:st_typing preamble.g0 steps
//     (ghost_comp
//        preamble.ctxt
//        (Tm_Star (list_as_vprop remaining) (apply_ss ss matched)));

//   // we haven't dropped any of the initial goals
//   // inductive invariant to relate solved goals and remaining goals
//   veq:vprop_equiv preamble.g (comp_pre preamble.c)
//                              (Tm_Star (list_as_vprop unmatched) matched);

//   props:squash (
//     well_typed_substitution preamble.g0 preamble.uvs ss /\
//     // whatever has been matched, must be closed w.r.t. uvars
//     uvars matched preamble.uvs `Set.subset` Map.domain ss
//   );
// }

// let ss_extends (ss1 ss2:substitution) : prop =
//   forall (x:var). (Map.contains ss2 x ==> (Map.contains ss1 x /\
//                                            Map.sel ss1 x == Map.sel ss2 x))

// val apply_ss_uvars (g0:env) (uvs:uvs_t) (ss:substitution) (t:term)
//   : Lemma
//       (requires well_typed_substitution g0 uvs ss)
//       (ensures uvars (apply_ss ss t) uvs ==
//                set_difference (uvars t uvs) (Map.domain ss))

// val apply_ss_st_uvars (g0:_) (uvs:_) (ss:substitution) (t:st_term)
//   : Lemma
//       (requires well_typed_substitution g0 uvs ss)
//       (ensures uvars_st (apply_ss_st ss t) uvs ==
//                set_difference (uvars_st t uvs) (Map.domain ss))

// val apply_ss_star (ss:substitution) (p1 p2:vprop)
//   : Lemma (apply_ss ss (Tm_Star p1 p2) == apply_ss ss p1 `Tm_Star` apply_ss ss p2)

// val extends_apply (g0:_) (uvs:_) (ss1 ss2:substitution) (t:term)
//   : Lemma
//       (requires
//          well_typed_substitution g0 uvs ss1 /\
//          well_typed_substitution g0 uvs ss2 /\
//          ss1 `ss_extends` ss2 /\
//          uvars t uvs `Set.subset` Map.domain ss2)
//       (ensures apply_ss ss1 t == apply_ss ss2 t)

// val extends_apply_st (g0:_) (uvs:_) (ss1 ss2:substitution) (t:st_term)
//   : Lemma
//       (requires
//          well_typed_substitution g0 uvs ss1 /\
//          well_typed_substitution g0 uvs ss2 /\
//          ss1 `ss_extends` ss2 /\
//          uvars_st t uvs `Set.subset` Map.domain ss2)
//       (ensures apply_ss_st ss1 t == apply_ss_st ss2 t)


// val typing_ss (g0:_) (uvs:_) (#g:env) (#t:st_term) (#c:comp) (t_typing:st_typing g t c) (ss:substitution)
//   : Pure (st_typing g (apply_ss_st ss t) (apply_c ss c))
//          (requires
//             uvs_invariant g0 g uvs /\
//             well_typed_substitution g0 uvs ss)
//          (ensures fun _ -> True)

// val veq_ss (g0:_) (uvs:_) (#g:env) (#p1 #p2:vprop) (veq:vprop_equiv g p1 p2) (ss:substitution)
//   : Pure (vprop_equiv g (apply_ss ss p1) (apply_ss ss p2))
//          (requires
//             uvs_invariant g0 g uvs /\
//             well_typed_substitution g0 uvs ss)
//          (ensures fun _ -> True)

// val veq_weakening (#g:_) (#p1 #p2:_) (veq:vprop_equiv g p1 p2) (g':env { env_extends g' g })
//   : vprop_equiv g' p1 p2

// val st_typing_strengthening (#g:_) (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
//   (g':env { env_extends g g' })
//   : Pure (st_typing g' t c)
//          (requires
//             freevars_st t `Set.subset` dom_env g' /\
//             freevars_comp c `Set.subset` dom_env g')
//          (ensures fun _ -> True)

// val tot_typing_strengthening (#g:_) (#t:term) (#ty:term) (t_typing:tot_typing g t ty)
//   (g':env { env_extends g g' })
//   : Pure (tot_typing g' t ty)
//          (requires
//             freevars t `Set.subset` dom_env g' /\
//             freevars ty `Set.subset` dom_env g')
//          (ensures fun _ -> True)

// val veq_strengthening (#g:_) (#p1 #p2:_) (veq:vprop_equiv g p1 p2)
//   (g':env { env_extends g g' })
//   : Pure (vprop_equiv g' p1 p2)
//          (requires
//             freevars p1 `Set.subset` dom_env g' /\
//             freevars p2 `Set.subset` dom_env g')
//          (ensures fun _ -> True)

// let with_pre_post (c:comp_st) (pre:vprop) (post:vprop) : comp_st =
//   match c with
//   | C_ST s
//   | C_STGhost _ s
//   | C_STAtomic _ s -> with_st_comp c { s with pre; post }

// val pre_post_equiv (#g:env) (#t:st_term) (#c:comp_st {ln (comp_post c)})
//   (d:st_typing g t c)
//   (#pre:vprop) (_:vprop_equiv g (comp_pre c) pre)
//   (#post:vprop) (_:vprop_equiv g (comp_post c) post)
//   : c':comp_st { c' == with_pre_post c pre post } &
//     st_typing g t c'

// type prover_t =
//   #(preamble:_) ->
//   p:prover_state preamble ->
//   T.Tac (option (p':prover_state preamble { p'.unmatched == [] /\
//                                             p'.ss `ss_extends` p.ss }))

// type prover_step =
//   #(preamble:_) ->
//   p:prover_state preamble ->
//   prover:prover_t ->
//   T.Tac (option (p':prover_state preamble { p'.ss `ss_extends` p.ss }))


// let idem_steps (g:env) (ctxt:vprop)
//   : t:st_term { freevars_st t == Set.empty } &
//     st_typing g t (ghost_comp ctxt (Tm_Star (list_as_vprop (vprop_as_list ctxt))
//                                             Tm_Emp)) = magic ()

// val empty_uvs : uvs:uvs_t { Map.domain uvs == Set.empty }
// val empty_ss : ss:substitution { Map.domain ss == Set.empty }


// let prove_precondition (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
//   (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
//   (prover:prover_t)
//   : T.Tac (option (t:st_term &
//                    c:comp_st { comp_pre c == ctxt } &
//                    st_typing g t c)) =
  
//   assume (g `env_extends` g);
//   let preamble = {
//     g0 = g;
//     g;
//     ctxt;
//     ctxt_typing;
//     t;
//     c;
//     t_typing;

//     uvs = empty_uvs;
//     uvs_props = ()
//   } in

//   let (| steps, steps_typing |) = idem_steps g ctxt in

//   let matched = Tm_Emp in
//   let unmatched = vprop_as_list (comp_pre c) in
//   let remaining = vprop_as_list ctxt in
//   let steps = steps in
//   let ss = empty_ss in

//   assume (apply_ss ss matched == Tm_Emp);
//   let steps_typing : st_typing preamble.g steps
//     (ghost_comp preamble.ctxt (Tm_Star (list_as_vprop remaining) (apply_ss ss matched))) = steps_typing in

//   let veq : vprop_equiv preamble.g (comp_pre preamble.c)
//                                    (Tm_Star (list_as_vprop unmatched) matched) = magic () in

//   let p = {
//     matched;
//     unmatched;
//     remaining;
//     steps;
//     ss;
//     remaining_typing = ctxt_typing;
//     unmatched_typing = magic ();  // get it from inversion of t_typing
//     steps_typing;
//     veq;
//     props = ();
//   } in

//   let popt = prover p in
//   match popt with
//   | Some p' ->
//     let steps_typing : st_typing g p'.steps
//       (ghost_comp ctxt (Tm_Star (list_as_vprop p'.remaining)
//                                 (apply_ss p'.ss p'.matched))) = p'.steps_typing in
//     assert (Set.equal (Map.domain p'.ss) Set.empty);
//     // since substitution is empty
//     assume (apply_ss p'.ss p'.matched == p'.matched);
//     let steps_typing : st_typing g p'.steps
//       (ghost_comp ctxt (Tm_Star (list_as_vprop p'.remaining) p'.matched)) = steps_typing in

//     let veq : vprop_equiv g (comp_pre c)
//                             (Tm_Star (list_as_vprop []) p'.matched) = p'.veq in
//     // replacing list_as_vprop [] with Tm_Emp and then normalizing star
//     let veq : vprop_equiv g (comp_pre c) p'.matched = magic () in

//     // use veq with steps_typing
//     let steps_typing : st_typing g p'.steps
//       (ghost_comp ctxt (Tm_Star (list_as_vprop p'.remaining) (comp_pre c))) = magic () in

//     // we can now bind p'.steps with c

//     admit ()
//   | None -> None

// val try_match (g0:_) (uvs:_)
//   (unm:vprop)
//   (rem:vprop)
//   (ss:substitution { well_typed_substitution g0 uvs ss })
//   : T.Tac (option (ss':substitution { well_typed_substitution g0 uvs ss' /\
//                                       ss' `ss_extends` ss /\
//                                       uvars unm uvs `Set.subset` Map.domain ss' } &
//                    vprop_equiv g0 (apply_ss ss' unm) rem))


// let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b { y === x } = x

// let match_step (#preamble:_) (p:prover_state preamble)
//   (unm:vprop)
//   (unmatched':list vprop)
//   (rem:vprop)
//   (remaining':list vprop)
//   (veq_unm:vprop_equiv preamble.g (list_as_vprop p.unmatched) (Tm_Star unm (list_as_vprop unmatched')))
//   (veq_rem:vprop_equiv preamble.g (list_as_vprop p.remaining) (Tm_Star rem (list_as_vprop remaining')))

//   : T.Tac (option (p':prover_state preamble { p'.ss `ss_extends` p.ss })) =

//   let ropt = try_match preamble.g0 preamble.uvs unm rem p.ss in
//   match ropt with
//   | Some (| ss', veq_unm_rem |) ->
//     let matched = Tm_Star unm p.matched in
//     let unmatched = unmatched' in
//     let remaining = remaining' in

//     let ss = ss' in

//     ///// restore p.steps_typing /////
//     extends_apply preamble.g0 preamble.uvs ss p.ss p.matched;
//     let steps_typing : st_typing preamble.g0 p.steps
//       (ghost_comp preamble.ctxt
//          (Tm_Star (list_as_vprop p.remaining) (apply_ss ss p.matched))) =
//       coerce_eq p.steps_typing () in
//     // some star rearrangement
//     let veq: vprop_equiv preamble.g0
//       (Tm_Star (list_as_vprop p.remaining) (apply_ss ss p.matched))
//       (Tm_Star (list_as_vprop remaining) (Tm_Star rem (apply_ss ss p.matched))) = magic () in
//     let veq_unm_rem : vprop_equiv preamble.g0 (apply_ss ss unm) rem =
//       veq_unm_rem in
//     let veq : vprop_equiv preamble.g0
//       (Tm_Star (list_as_vprop p.remaining) (apply_ss ss p.matched))
//       (Tm_Star (list_as_vprop remaining) (Tm_Star (apply_ss ss unm) (apply_ss ss p.matched))) =
//       magic () in
//     apply_ss_star ss unm p.matched;
//     let veq : vprop_equiv preamble.g0
//       (Tm_Star (list_as_vprop p.remaining) (apply_ss ss p.matched))
//       (Tm_Star (list_as_vprop remaining) (apply_ss ss (Tm_Star unm p.matched))) = veq in
//     let veq_pre : vprop_equiv preamble.g0 preamble.ctxt preamble.ctxt = magic () in
//     assume (ln (Tm_Star (list_as_vprop p.remaining) (apply_ss ss p.matched)));
//     let (| _, steps_typing |) : x:_ & st_typing preamble.g0 p.steps
//       (ghost_comp preamble.ctxt
//          (Tm_Star (list_as_vprop remaining) (apply_ss ss matched))) =
//       pre_post_equiv steps_typing veq_pre veq in
//     /////

//     ///// restore p.veq /////
//     let veq : vprop_equiv preamble.g
//       (comp_pre preamble.c)
//       (Tm_Star (list_as_vprop p.unmatched) p.matched) =
//       p.veq in
//     // use veq_unm
//     let veq : vprop_equiv preamble.g
//       (comp_pre preamble.c)
//       (Tm_Star (Tm_Star unm (list_as_vprop unmatched)) p.matched) = magic () in
//     // stars rearrangement
//     let veq : vprop_equiv preamble.g
//       (comp_pre preamble.c)
//       (Tm_Star (list_as_vprop unmatched) matched) = magic () in
//     /////

//     Some { p with
//            matched;
//            unmatched;
//            remaining;
//            steps = p.steps;
//            ss;
//            remaining_typing = magic ();  // remaining and matched are sub vprops of original ones,
//                                          // whose typing came in with the orignal prover state
//            unmatched_typing = magic ();
//            steps_typing;
//            veq;
//            props = (); }
  
//   | _ -> admit ()

// module RT = FStar.Reflection.Typing

// val subset_bool (#a:eqtype) (s1 s2:Set.set a)
//   : Tot (b:bool { b ==> Set.subset s1 s2 })

// #push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 1"
// let intro_exists_sub_prover_state (#preamble:_) (p:prover_state preamble)
//   (u:universe) (t:term) (body:vprop)
//   (unmatched':list vprop)
//   (_:squash (p.unmatched == (Tm_ExistsSL u (null_binder t) body)::unmatched'))
//   (y:var {y == fresh preamble.g})
//   : preamble_sub:prover_state_preamble &
//     prover_state preamble_sub =
  
//   let g' = push_binding preamble.g y t in
//   assume (g' `env_extends` preamble.g);

//   //// create a sub prover preamble ////
//   let g0_sub = preamble.g0 in
//   let g_sub = g' in
//   let ctxt_sub = list_as_vprop p.remaining in
//   let ctxt_typing_sub : vprop_typing g0_sub (list_as_vprop p.remaining) =
//     p.remaining_typing in
//   let witness_tm = tm_var {
//     nm_index = y;
//     nm_ppname = ppname_default;
//   } in
//   // what should erased be?
//   let t_sub = wr (Tm_IntroExists {
//     erased = false;
//     p = Tm_ExistsSL u (null_binder t) body;
//     witnesses = [witness_tm];
//     should_check = should_check_true
//   }) in
//   let c_sub = comp_intro_exists u (null_binder t) body witness_tm in
//   // the t and Tm_ExistsSL should come from typing of matched
//   // and some inversions
//   let t_typing_sub : st_typing g' t_sub c_sub =
//     T_IntroExists g' u (null_binder t) body witness_tm
//       (magic ())  // typing of t
//       (magic ())  // typing of Tm_ExistsSL
//       (magic ())  // typing of witness_tm
//   in

//   let uvs_sub = Map.upd preamble.uvs y t in
//   assume (~ (Map.contains preamble.uvs y));
//   assume (dom_env g_sub == Set.union (dom_env preamble.g) (Set.singleton y));
//   assume (~ (Set.mem y (dom_env preamble.g0)));
//   assume (forall (x:var). Map.contains uvs_sub x ==>
//                           env_contains g_sub x (Map.sel uvs_sub x));

//   let preamble_sub = {
//     g0 = g0_sub;
//     g = g_sub;
//     ctxt = ctxt_sub;
//     ctxt_typing = ctxt_typing_sub;
//     t = t_sub;
//     c = c_sub;
//     t_typing = t_typing_sub;

//     uvs = uvs_sub;
//     uvs_props = ()
//   } in
//   /////
  
//   // create a sub prover state /////
//   let matched_sub = Tm_Emp in
//   let unmatched_sub = vprop_as_list (comp_pre preamble_sub.c) in
//   let remaining_sub = p.remaining in

//   let remaining_typing:vprop_typing preamble_sub.g0 (list_as_vprop remaining_sub) =
//     p.remaining_typing in

//   // get from inversion of t_typing_sub
//   let unmatched_typing:vprop_typing preamble_sub.g (list_as_vprop unmatched_sub) =
//     magic () in
  
//   let (| steps_sub, steps_typing_sub |) = idem_steps preamble_sub.g0 preamble_sub.ctxt in
//   assume (apply_ss p.ss Tm_Emp == Tm_Emp);
//   assume (list_as_vprop (vprop_as_list preamble_sub.ctxt) == preamble_sub.ctxt);
//   let steps_typing_sub : st_typing preamble_sub.g0 steps_sub
//     (ghost_comp preamble_sub.ctxt
//        (Tm_Star (list_as_vprop remaining_sub) Tm_Emp)) = coerce_eq steps_typing_sub () in

//   // matched_sub is emp, and list_as_vprop and vprop_as_list should cancel
//   let veq_sub : vprop_equiv preamble_sub.g
//     (comp_pre preamble_sub.c)
//     (Tm_Star (list_as_vprop unmatched_sub) matched_sub) = magic () in

//   let ss_sub = p.ss in

//   assume (apply_ss ss_sub matched_sub == Tm_Emp);

//   let prover_state_sub : prover_state preamble_sub = {
//     matched = matched_sub;
//     unmatched = unmatched_sub;
//     remaining = remaining_sub;
//     steps = steps_sub;
//     ss = ss_sub;
//     remaining_typing;
//     unmatched_typing;
//     steps_typing = steps_typing_sub;
//     veq = veq_sub;
//     props = ();
//   } in

//   (| preamble_sub, prover_state_sub |)



// let intro_exists_step (#preamble:_) (p:prover_state preamble)
//   (u:universe) (t:term) (body:vprop)
//   (unmatched':list vprop)
//   (_:squash (p.unmatched == (Tm_ExistsSL u (null_binder t) body)::unmatched'))
//   (prover:(#(preamble:_) ->
//            p:prover_state preamble ->
//            T.Tac (option (p':prover_state preamble { p'.unmatched == [] /\
//                                                      p'.ss `ss_extends` p.ss }))))

//   : T.Tac (option (p':prover_state preamble { p'.ss `ss_extends` p.ss })) =
  
//   let y = fresh preamble.g in
//   let (| preamble_sub, prover_state_sub |) =
//     intro_exists_sub_prover_state p u t body unmatched' () y in
//   let t_sub = preamble_sub.t in
//   let c_sub = preamble_sub.c in
//   let t_typing_sub = preamble_sub.t_typing in

//   let popt = prover prover_state_sub in
//   match popt with
//   | None -> None
//   | Some psub ->
//     // make sure witness is solved, and exists is uvars free
//     if Set.mem y (Map.domain psub.ss) &&
//        subset_bool (uvars (Tm_ExistsSL u (null_binder t) body) preamble_sub.uvs) (Map.domain psub.ss)
//     then begin
//       let steps_typing_sub : st_typing preamble_sub.g0 psub.steps
//         (ghost_comp
//            (list_as_vprop p.remaining)
//            (Tm_Star (list_as_vprop psub.remaining) (apply_ss psub.ss psub.matched))) = psub.steps_typing in
      
//       let veq_sub : vprop_equiv preamble_sub.g
//         (comp_pre c_sub)
//         (Tm_Star (list_as_vprop []) psub.matched) = psub.veq in
//       // some manipulation of veq_sub
//       let veq_sub : vprop_equiv preamble_sub.g (comp_pre c_sub) psub.matched = magic () in
//       let veq_sub : vprop_equiv preamble_sub.g
//         (apply_ss psub.ss (comp_pre c_sub))
//         (apply_ss psub.ss psub.matched) =
//         veq_ss preamble_sub.g0 preamble_sub.uvs veq_sub psub.ss in

//       // THIS IS TODO, BUT WE SHOULD BE ABLE TO STRENGTHEN veq_sub to preamble_sub.g0
//       // Need a lemma that says, if freevars t in g, and no uvars in t, then freevars t in g0
//       //   Then we can use strengthening lemmas
//       let veq_sub : vprop_equiv preamble_sub.g0
//         (apply_ss psub.ss (comp_pre c_sub))
//         (apply_ss psub.ss psub.matched) = magic () in

//       // use veq_sub on steps_typing_sub
//       let steps_typing_sub : st_typing preamble_sub.g0 psub.steps
//         (ghost_comp
//            (list_as_vprop p.remaining)
//            (Tm_Star (list_as_vprop psub.remaining) (apply_ss psub.ss (comp_pre c_sub)))) = magic () in

//       let t_typing_sub : st_typing preamble_sub.g t_sub c_sub = t_typing_sub in
//       assert (comp_post c_sub == Tm_ExistsSL u (null_binder t) body);

//       let t_typing_sub : st_typing preamble_sub.g
//         (apply_ss_st psub.ss t_sub)
//         (apply_c psub.ss c_sub) = typing_ss preamble_sub.g0 preamble_sub.uvs t_typing_sub psub.ss in

//       // AGAIN WE NEED A STRENGTHENING STEP HERE TO TAKE t_typing_sub to preamble_sub.g0
//       // Need a lemma that says, if freevars t in g, and no uvars in t, then freevars t in g0
//       //   Then we can use strengthening lemmas
//       let t_typing_sub : st_typing preamble_sub.g0
//         (apply_ss_st psub.ss t_sub)
//         (apply_c psub.ss c_sub) = magic () in

//       // assume (stateful_comp (apply_c psub.ss c_sub));
//       // assume (comp_pre (apply_c psub.ss c_sub) == apply_ss psub.ss (comp_pre c_sub));
//       // assume (comp_post (apply_c psub.ss c_sub) == apply_ss psub.ss (comp_post c_sub));

//       // g0 |- { p.remaining } psub.steps { psub.remaining * apply_ss psub.ss (comp_pre c_sub) }
//       // g0 |- { apply_ss psub.ss (comp_pre c_sub) } apply_ss_st psub.ss t_sub { apply_ss psub.ss (comp_post c_sub) }
//       // so we can bind these ... and note that c_sub is also ghost
//       let steps : st_term = magic () in  // Tm_Bind steps (apply_ss_st psub.ss t_sub)
//       let steps_c = ghost_comp (list_as_vprop p.remaining)
//                                (Tm_Star (list_as_vprop psub.remaining)
//                                         (apply_ss psub.ss (Tm_ExistsSL u (null_binder t) body))) in
//       let steps_typing : st_typing preamble_sub.g0 steps steps_c = magic () in  // bind typing
//       let steps_typing : st_typing preamble.g0 steps steps_c = steps_typing in

//       let psteps_typing : st_typing preamble.g0 p.steps
//         (ghost_comp preamble.ctxt
//                     (Tm_Star (list_as_vprop p.remaining)
//                              (apply_ss p.ss p.matched))) = p.steps_typing in

//       let ss_new = Map.restrict (Map.domain preamble.uvs) psub.ss in
//       assume (~ (Map.contains preamble.uvs y));
//       assume (~ (Map.contains p.ss y));
//       assert (ss_new `ss_extends` p.ss);
//       assert (well_typed_substitution preamble.g0 preamble.uvs ss_new);

//       extends_apply preamble.g0 preamble.uvs ss_new p.ss p.matched;

//       let psteps_typing : st_typing preamble.g0 p.steps
//         (ghost_comp preamble.ctxt
//                     (Tm_Star (list_as_vprop p.remaining)
//                              (apply_ss ss_new p.matched))) = coerce_eq psteps_typing () in

//       // ss_new = psub.ss - y, and y does not occur free in Tm_ExistsSL u t body
//       assume (apply_ss psub.ss (Tm_ExistsSL u (null_binder t) body) ==
//               apply_ss ss_new (Tm_ExistsSL u (null_binder t) body));
//       let steps_typing : st_typing preamble.g0 steps
//         (ghost_comp (list_as_vprop p.remaining)
//                     (Tm_Star (list_as_vprop psub.remaining)
//                              (apply_ss ss_new (Tm_ExistsSL u (null_binder t) body)))) = steps_typing in

//       // g0 |- { preamble.ctxt } p.steps { p.remaining * apply_ss ss_new p.matched }
//       // g0 |- { p.remaining } steps { psub.remaining * apply_ss ss_new (Tm_ExistsSL u t body) }
//       //
//       // bind them
//       let steps_new : st_term = magic () in
//       let steps_typing_new : st_typing preamble.g0 steps_new
//         (ghost_comp preamble.ctxt
//                     (Tm_Star (list_as_vprop psub.remaining)
//                              (apply_ss ss_new (Tm_Star (Tm_ExistsSL u (null_binder t) body) p.matched)))) =
//         magic () in

//       let matched_new = Tm_Star (Tm_ExistsSL u (null_binder t) body) p.matched in
//       let unmatched_new = unmatched' in
//       let remaining_new = psub.remaining in
//       let steps_new = steps_new in
//       let ss_new = ss_new in

//       let remaining_typing_new : vprop_typing preamble.g0 (list_as_vprop remaining_new) =
//         psub.remaining_typing in

//       // unmatched' is the left component of star term,
//       // whose typing came in to us
//       let unmatched_typing : vprop_typing preamble.g (list_as_vprop unmatched') = magic () in

//       let steps_typing_new : st_typing preamble.g0 steps_new
//         (ghost_comp preamble.ctxt
//                     (Tm_Star (list_as_vprop remaining_new)
//                              (apply_ss ss_new matched_new))) = steps_typing_new in

//       // move Tm_ExistsSL from unmatched to matched
//       let veq : vprop_equiv preamble.g (comp_pre preamble.c)
//                                        (Tm_Star (list_as_vprop unmatched_new) matched_new) = magic () in

//       assert (well_typed_substitution preamble.g0 preamble.uvs ss_new);
//       assert (uvars matched_new preamble.uvs `Set.subset` Map.domain ss_new);

//       Some {
//         matched = matched_new;
//         unmatched = unmatched_new;
//         remaining = remaining_new;
//         steps = steps_new;
//         ss = ss_new;
//         remaining_typing = remaining_typing_new;
//         unmatched_typing;
//         steps_typing = steps_typing_new;
//         veq;
//         props = ();
//       }
//     end
//     else None
// #pop-options

// // let has_no_uvars_from (t:term) (uvs:Set.set var) =
// //   freevars t `Set.disjoint` uvs

// // type uv_st =
// //   uvs:Set.set var & Map.t var (t:term { t `has_no_uvars_from` uvs})

// // let subst_uvs (t:term) (uvs:uv_st) : term = admit ()
// // let subst_uvs_st_term (t:st_term) (uvs:uv_st) : st_term = admit ()

// // noeq
// // type prover_state (g:env) (preamble:prover_state_preamble g) = {
// //   (* uvars and their solutions *)
// //   uv_st : uv_st;

// //   (* the in-progress proof state *)
// //   matched_pre:term; (* conjuncts that we have already derived *)
// //   unmatched_pre:list term; (* conjuncts remaining to be derived *)
// //   remaining_ctxt:list term; (* unused conjuncts in the context *)

// //   (* Ghost proof steps witnessing the derivation of matched_pre from ctxt *)
// //   proof_steps : st_term;

// //   ctxt_no_uvs : squash (
// //     preamble.ctxt `has_no_uvars_from` (dfst uv_st) /\
// //     list_as_vprop remaining_ctxt `has_no_uvars_from` (dfst uv_st)
// //   );

// //   proof_steps_typing:
// //     st_typing g
// //       (subst_uvs_st_term proof_steps uv_st)
// //       (ghost_comp preamble.ctxt (Tm_Star (subst_uvs (list_as_vprop remaining_ctxt) uv_st)
// //                                          (subst_uvs matched_pre uv_st)));

// //   pre_equiv:
// //     vprop_equiv g
// //       (subst_uvs (comp_pre preamble.c) uv_st)
// //       (Tm_Star (subst_uvs (list_as_vprop unmatched_pre) uv_st) (subst_uvs matched_pre uv_st));
// // }

// // let proof_steps_post (#g:_) (#preamble:_) (p:prover_state g preamble) : vprop =
// //   Tm_Star (list_as_vprop p.remaining_ctxt) (subst_uvs p.matched_pre p.uv_st)

// // let bind_proof_steps_with (#g:env) (#preamble:_) (p:prover_state g preamble)
// //   (t:st_term)
// //   (c:comp_st {comp_pre c == proof_steps_post p})
// //   (t_typing:st_typing g t c)
// //   : (t':st_term & st_typing g t' (comp_st_with_pre c preamble.ctxt))
// //   = admit()

// // type prover_step_t =
// //   #g:_ ->
// //   #preamble:_ ->
// //   p:prover_state g preamble ->
// //   T.Tac (option (prover_state g preamble))

// // //
// // // result of an intro (pure, exists, rewrite) step
// // //   that consumes some vprop v from p.unmatched_pre
// // //

// // let intro_comp (c:comp) =
// //   C_STGhost? c /\ comp_u c == u_zero /\ comp_res c == tm_unit

// // //
// // // A proof step that provides v, eating away some of the ctxt
// // //
// // noeq
// // type proof_step (g:env) (ctxt:list vprop) (v:vprop) = {
// //   remaining' : list vprop;

// //   t' : st_term;
// //   c' : c:comp { intro_comp c /\ comp_post c == v };
// //   t'_typing : st_typing g t' c';

// //   remaining_equiv : vprop_equiv g (list_as_vprop ctxt)
// //                                   (Tm_Star (comp_pre c') (list_as_vprop remaining'));
// // }

// // // An intro step that makes progress by solving one conjunct
// // // v from the p.unmatched_pre
// // noeq
// // type intro_from_unmatched_step (#g:env) (#preamble:_) (p:prover_state g preamble) = {
// //   uv_st : uv_st;

// //   v : vprop;

// //   // new unmatched pre and remaining ctxt
// //   remaining' : list vprop; 
// //   unmatched' : list vprop;

// //   t' : st_term;
// //   c' : c:comp { intro_comp c /\ comp_post c == v };
// //   t'_typing : st_typing g t' c';
 
// //   // relation between new and old unmatched_pre and remaining_ctxt
// //   unmatched_equiv : vprop_equiv g (list_as_vprop p.unmatched_pre)
// //                                   (Tm_Star v (list_as_vprop unmatched'));
// // }

// // type proof_step_fn =
// //   #g:_ ->
// //   #ctxt:_ ->
// //   #v:vprop ->
// //   tot_typing g (list_as_vprop ctxt) Tm_VProp ->
// //   tot_typing g v Tm_VProp ->
// //   T.Tac (option (proof_step g ctxt v))

// // type intro_from_unmatched_fn =
// //   #g:_ ->
// //   #preamble:_ ->
// //   p:prover_state g preamble ->
// //   T.Tac (option (intro_from_unmatched_step p))

// // val apply_proof_step
// //   (#g:env)
// //   (#preamble:_)
// //   (p:prover_state g preamble)
// //   (v:vprop)
// //   (r:proof_step g p.remaining_ctxt v)  
// //   : T.Tac (p':prover_state g preamble {
// //       p'.matched_pre == p.matched_pre /\
// //       p'.unmatched_pre == p.unmatched_pre /\
// //       p'.remaining_ctxt == v::r.remaining'
// //     })

// // val apply_intro_from_unmatched_step
// //   (#g:env)
// //   (#preamble:_)
// //   (#p:prover_state g preamble)
// //   (r:intro_from_unmatched_step p)
// //   : T.Tac (p':prover_state g preamble {
// //       p'.matched_pre == Tm_Star p.matched_pre r.v /\
// //       p'.unmatched_pre == r.unmatched' /\
// //       p'.remaining_ctxt == r.ps.remaining'
// //     })
