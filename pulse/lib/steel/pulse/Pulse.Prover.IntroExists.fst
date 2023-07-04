module Pulse.Prover.IntroExists

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Common

module T = FStar.Tactics.V2
module PS = Pulse.Prover.Substs

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

// there will be some side conditions related to the typings
let k_intro_exists (#g:env) (#u:universe) (#b:binder) (#p:vprop)
  (ex_typing:tot_typing g (tm_exists_sl u b p) tm_vprop)
  (#e:term)
  (e_typing:tot_typing g e b.binder_ty)
  (#frame:vprop)
  (frame_typing:tot_typing g frame tm_vprop)
  : T.Tac (continuation_elaborator g (frame * subst_term p [ DT 0 e ])
                                   g (frame * tm_exists_sl u b p)) =
  
  let t = wr (Tm_IntroExists { erased = false;
                               p = tm_exists_sl u b p;
                               witnesses = [e];
                               should_check = should_check_true }) in

  let c = comp_intro_exists u b p e in

  let t_typing = T_IntroExists g u b p e (magic ()) ex_typing e_typing in

  assert (comp_pre c == subst_term p [ DT 0 e ]);
  assert (comp_post c == tm_exists_sl u b p);

  let x = fresh g in
  assume (open_term (comp_post c) x == comp_post c);

  let k
    : continuation_elaborator
        g (frame * subst_term p [ DT 0 e ])
        (push_binding g x ppname_default (comp_res c)) (tm_exists_sl u b p * frame) =
    continuation_elaborator_with_bind frame t_typing (magic ()) x in

  let k
    : continuation_elaborator
        g (frame * subst_term p [ DT 0 e ])
        (push_binding g x ppname_default (comp_res c)) (frame * tm_exists_sl u b p) =
    k_elab_equiv k (VE_Refl _ _) (VE_Comm _ _ _) in

  fun post_hint r ->
  let (| t1, c1, d1 |) = r in
  let d1 : st_typing g t1 c1 = d1 in
  let empty_env = mk_env (fstar_env g) in
  assert (equal g (push_env g empty_env));
  assert (equal (push_env (push_binding g x ppname_default (comp_res c)) empty_env)
                (push_binding g x ppname_default (comp_res c)));
  let d1 : st_typing (push_binding g x ppname_default (comp_res c)) t1 c1 =
    st_typing_weakening
      g
      empty_env
      t1 c1 d1
      (push_binding g x ppname_default (comp_res c)) in

  k post_hint (| t1, c1, d1 |)

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 1"
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
    ctxt = list_as_vprop pst.remaining_ctxt;
    frame = preamble.frame * pst.ss.(pst.solved);
    ctxt_frame_typing = magic ();
    goals = open_term_nv body px * (list_as_vprop unsolved'); 
  } in
  let k_sub:
    continuation_elaborator
      preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
      pst.pg ((list_as_vprop (vprop_as_list preamble_sub.ctxt) * preamble_sub.frame) * pst.ss.(tm_emp)) =
    let k = k_elab_unit preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame) in
    let k = k_elab_equiv k
      (VE_Refl _ _)
      (magic () <:
         vprop_equiv
           preamble_sub.g0
           (preamble_sub.ctxt * preamble_sub.frame)
           ((list_as_vprop (vprop_as_list preamble_sub.ctxt) * preamble_sub.frame) * pst.ss.(tm_emp))) in
    coerce_eq k ()
  in
  let pst_sub : prover_state preamble_sub = {
    pg = pst.pg;
    remaining_ctxt = vprop_as_list preamble_sub.ctxt;
    remaining_ctxt_frame_typing = magic ();
    uvs = pst.uvs;
    ss = pst.ss;
    solved = tm_emp;
    unsolved = [open_term_nv body px] @ unsolved';
    solved_typing = magic ();
    k = k_sub;
    goals_inv = magic ();
  } in
  let pst_sub = prover pst_sub in
  let pst_sub_goals_inv
    : vprop_equiv (push_env pst_sub.pg pst_sub.uvs)
                  preamble_sub.goals
                  (list_as_vprop [] * pst_sub.solved) = pst_sub.goals_inv in
  let ropt = PS.ss_to_nt_substs pst_sub.pg pst_sub.uvs pst_sub.ss in
  if None? ropt then fail pst_sub.pg None "intro exists ss not well-typed";
  // if not (PS.check_well_typedness pst_sub.pg pst_sub.uvs pst_sub.ss)
  // then fail pst_sub.pg None "intro exists ss not well-typed";
  let Some nt = ropt in
  assert (PS.well_typed_nt_substs pst_sub.pg pst_sub.uvs nt);
  let pst_sub_goals_inv
    : vprop_equiv pst_sub.pg
                  pst_sub.ss.(preamble_sub.goals)
                  pst_sub.ss.(list_as_vprop [] * pst_sub.solved) =
    PS.vprop_equiv_nt_substs_derived pst_sub.pg pst_sub.uvs pst_sub_goals_inv nt in
  assume (pst_sub.ss.(list_as_vprop [] * pst_sub.solved) ==
          tm_emp * pst_sub.ss.(pst_sub.solved));
  let pst_sub_goals_inv
    : vprop_equiv pst_sub.pg
                  pst_sub.ss.(preamble_sub.goals)
                  (tm_emp * pst_sub.ss.(pst_sub.solved)) = coerce_eq pst_sub_goals_inv () in
  let pst_sub_goals_inv
    : vprop_equiv pst_sub.pg
                  pst_sub.ss.(preamble_sub.goals)
                  pst_sub.ss.(pst_sub.solved) = VE_Trans _ _ _ _ pst_sub_goals_inv (VE_Unit _ _) in
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble_sub.frame) * pst_sub.ss.(pst_sub.solved)) =
    pst_sub.k in
  // replacing pst_sub.ss.(pst_sub.solved) with
  // pst_sub.ss.(preamble_sub.goals) using the equiv relation
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble_sub.frame) * pst_sub.ss.(preamble_sub.goals)) =
    k_elab_equiv k_sub (VE_Refl _ _) (magic ()) in
  // substitute preamble_sub.goals
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble_sub.frame) *
                    pst_sub.ss.(open_term_nv body px * (list_as_vprop unsolved'))) =
    coerce_eq k_sub () in
  assume (pst_sub.ss.(open_term_nv body px * (list_as_vprop unsolved')) ==
          pst_sub.ss.(open_term_nv body px) * pst_sub.ss.(list_as_vprop unsolved'));
  let witness = pst_sub.ss.(null_var x) in
  assume (pst_sub.ss.(open_term_nv body px) == subst_term (pst_sub.ss.(body)) [DT 0 witness]);
  // rewrite
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble_sub.frame) *
                    (subst_term (pst_sub.ss.(body)) [DT 0 witness] * pst_sub.ss.(list_as_vprop unsolved'))) =
    coerce_eq k_sub () in
  // some * rearrangement
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt *
                     preamble_sub.frame *
                     pst_sub.ss.(list_as_vprop unsolved')) *
                    (subst_term (pst_sub.ss.(body)) [DT 0 witness])) =
    k_elab_equiv k_sub (VE_Refl _ _) (magic ()) in

  let k_intro_exists
    : continuation_elaborator
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt *
                     preamble_sub.frame *
                     pst_sub.ss.(list_as_vprop unsolved')) *
                    (subst_term (pst_sub.ss.(body)) [DT 0 witness]))
        pst_sub.pg ( _ *
                    (tm_exists_sl u (PS.nt_subst_binder b nt) pst_sub.ss.(body))) =
    k_intro_exists
      #pst_sub.pg
      #u
      #(PS.nt_subst_binder b nt)
      #pst_sub.ss.(body)
      (magic ())  // typing of tm_exists_sl with pst_sub.ss applied
      #witness
      (magic ())  // witness typing
      #_
      (magic ())  // frame typing
  in
  assume (tm_exists_sl u (PS.nt_subst_binder b nt) pst_sub.ss.(body) ==
          pst_sub.ss.(tm_exists_sl u b body));
  // pst_sub.ss extends pst.ss, and pst.ss already solved all of pst.solved
  assume (pst.ss.(pst.solved) == pst_sub.ss.(pst.solved));
  // also substitute preamble_sub.frame
  let k_intro_exists
    : continuation_elaborator
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt *
                     preamble_sub.frame *
                     pst_sub.ss.(list_as_vprop unsolved')) *
                    (subst_term (pst_sub.ss.(body)) [DT 0 witness]))
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt *
                     (preamble.frame * pst_sub.ss.(pst.solved)) *
                     pst_sub.ss.(list_as_vprop unsolved')) *
                    (pst_sub.ss.(tm_exists_sl u b body))) = coerce_eq k_intro_exists () in

  // rejig some *s in the continuation context
  let k_intro_exists
    : continuation_elaborator
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt *
                     preamble_sub.frame *
                     pst_sub.ss.(list_as_vprop unsolved')) *
                    (subst_term (pst_sub.ss.(body)) [DT 0 witness]))
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved) *
                     pst_sub.ss.(tm_exists_sl u b body) *
                     pst_sub.ss.(list_as_vprop unsolved'))) =
     k_elab_equiv k_intro_exists (VE_Refl _ _) (magic ()) in
  assume (pst_sub.ss.(pst.solved) *
          pst_sub.ss.(tm_exists_sl u b body) *
          pst_sub.ss.(list_as_vprop unsolved') ==
          pst_sub.ss.(pst.solved * tm_exists_sl u b body * list_as_vprop unsolved'));
  let k_intro_exists
    : continuation_elaborator
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt *
                     preamble_sub.frame *
                     pst_sub.ss.(list_as_vprop unsolved')) *
                    (subst_term (pst_sub.ss.(body)) [DT 0 witness]))
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * tm_exists_sl u b body * list_as_vprop unsolved'))) =
    coerce_eq k_intro_exists () in
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * tm_exists_sl u b body * list_as_vprop unsolved'))) =
    k_elab_trans k_sub k_intro_exists in
  // pst.unsolved == tm_exists_sl u b body::unsolved'
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * list_as_vprop pst.unsolved))) =
    k_elab_equiv k_sub (VE_Refl _ _) (magic ()) in

  let k_sub
    : continuation_elaborator
        pst.pg (list_as_vprop pst.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved)))
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * list_as_vprop pst.unsolved))) =
    coerce_eq k_sub () in

  // rejig *s in the elab ctxt
  let k_sub
    : continuation_elaborator
        pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * list_as_vprop pst.unsolved))) =
    k_elab_equiv k_sub (magic ()) (VE_Refl _ _) in

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * list_as_vprop pst.unsolved))) =
    k_elab_trans pst.k k_sub in

  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs)
                  preamble.goals
                  (list_as_vprop pst.unsolved * pst.solved) =
    pst.goals_inv in

  // weakening
  let goals_inv
    : vprop_equiv (push_env pst_sub.pg pst_sub.uvs)
                  preamble.goals
                  (pst.solved * list_as_vprop pst.unsolved) = magic () in

  let goals_inv
    : vprop_equiv pst_sub.pg
                  (pst_sub.ss.(preamble.goals))
                  (pst_sub.ss.(pst.solved * list_as_vprop pst.unsolved)) =
    PS.vprop_equiv_nt_substs_derived pst_sub.pg pst_sub.uvs goals_inv nt in

  // rewrite k using goals_inv
  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(preamble.goals))) =
    k_elab_equiv k (VE_Refl _ _) (magic ()) in

  let pst' : prover_state preamble = {
    pg = pst_sub.pg;
    remaining_ctxt = pst_sub.remaining_ctxt;
    remaining_ctxt_frame_typing = magic ();
    uvs = pst_sub.uvs;
    ss = pst_sub.ss;
    solved = preamble.goals;
    solved_typing = magic ();
    unsolved = [];
    k;
    goals_inv = magic ();
  } in

  pst'
#pop-options
  // let goals_inv
  //   : vprop_equiv (push_env pst.pg pst.uvs) preamble.goals (list_as_vprop pst.unsolved * pst.solved) =
  //   pst.goals_inv in

  // assert (pst_sub_terminal.pg `env_extends` pst.pg);
  // assert (pst_sub_terminal.uvs `env_extends` pst.uvs);

  // // weakening of goals_inv
  // let goals_inv
  //   : vprop_equiv (push_env pst_sub_terminal.pg pst_sub_terminal.uvs)
  //                 preamble.goals
  //                 (pst.solved * list_as_vprop pst.unsolved) = magic () in

  // // substitution lemma
  // let goals_inv
  //   : vprop_equiv pst_sub_terminal.pg
  //                 (pst_sub_terminal.ss.(preamble.goals))
  //                 (pst_sub_terminal.ss.(pst.solved * list_as_vprop pst.unsolved)) = magic () in

  // // replace in k
  // let k
  //   : continuation_elaborator
  //       preamble.g0 preamble.ctxt
  //       pst_sub_terminal.pg (list_as_vprop pst_sub_terminal.remaining_ctxt *
  //                            pst_sub_terminal.ss.(preamble.goals)) =
  //   magic () in

  // let pst' : prover_state preamble = {
  //   pg = pst_sub_terminal.pg;
  //   remaining_ctxt = pst_sub_terminal.remaining_ctxt;
  //   uvs = pst_sub_terminal.uvs;
  //   ss = pst_sub_terminal.ss;
  //   solved = preamble.goals;
  //   unsolved = [];
  //   k;
  //   goals_inv = magic ();
  //   solved_inv = magic (); // what is this? is this a dynamic check?
  // } in

  // pst'


// let vprop_as_list_of_list_as_vprop (l:list vprop)
//   : Lemma (vprop_as_list (list_as_vprop l) == l)
//           [SMTPat (vprop_as_list (list_as_vprop l))] = admit ()

// let list_as_vprop_of_vprop_as_list (p:vprop)
//   : Lemma (list_as_vprop (vprop_as_list p) == p)
//           [SMTPat (list_as_vprop (vprop_as_list p))] = admit ()


// let intro_exists_sub_prover_state (#preamble:_) (p:prover_state preamble)
//   (u:universe) (b:binder) (body:vprop)
//   (exists_typing:tot_typing (pst_env preamble.uvs p.ss) (tm_exists_sl u b body) tm_vprop)
//   : x:var { ~ (x `Set.mem` (Set.union (dom preamble.g0) (dom preamble.uvs)))} &
//     preamble:_ &
//     prover_state preamble =
  
//   let g0 = preamble.g0 in
//   let x = fresh (push_env g0 preamble.uvs) in

//   let uvs = psubst_env (filter_ss preamble.uvs p.ss) p.ss in
//   let uvs = push_binding_def uvs x b.binder_ty in

//   let preamble_sub = {
//     g0 = g0;
//     ctxt = list_as_vprop p.remaining_ctxt;
//     ctxt_typing = p.remaining_ctxt_typing;

//     t = wr (Tm_IntroExists {
//       erased=false;
//       p=tm_exists_sl u b body;
//       witnesses=[null_var x];
//       should_check=should_check_false });
    
//     c = comp_intro_exists u b body (null_var x);
    
//     uvs;
//   } in

  
//   let ss = Psubst.empty g0 in

//   calc (equal) {
//     pst_env preamble_sub.uvs ss;
//        (equal) { }
//     push_env g0 (psubst_env (filter_ss uvs ss) ss);
//        (equal) { assume (filter_ss uvs (Psubst.empty g0) == uvs) }
//     push_env g0 (psubst_env uvs ss);
//        (equal) { assume (psubst_env uvs (Psubst.empty g0) == uvs) }
//     push_env g0 uvs;
//        (equal) { }
//     push_env g0 (push_binding_def (psubst_env (filter_ss preamble.uvs p.ss) p.ss) x b.binder_ty);
//        (equal) { }
//     push_binding_def (pst_env preamble.uvs p.ss) x b.binder_ty;
//   };

//   let solved_goals = tm_emp in
//   let unsolved_goals = vprop_as_list (comp_pre preamble_sub.c) in
//   let remaining_ctxt = vprop_as_list preamble_sub.ctxt in

//   let t_typing
//     : st_typing (pst_env preamble_sub.uvs ss)
//                 preamble_sub.t
//                 preamble_sub.c =
//     T_IntroExists
//       (pst_env preamble_sub.uvs ss)
//       u b body (null_var x)
//       (magic ())  // binder typing in new env, weakening using the input exists typing and calc above
//       (magic ())  // similarly, exists typing in new env is weakening of the input exists typing
//       (magic ())  // x:t in gamma
//   in

//   // ss is empty
//   assume (Psubst.subst_st_term ss preamble_sub.t == preamble_sub.t);
//   assume (Psubst.subst_comp ss preamble_sub.c == preamble_sub.c);

//   let t_typing
//     : st_typing (pst_env preamble_sub.uvs ss)
//                 (Psubst.subst_st_term ss preamble_sub.t)
//                 (Psubst.subst_comp ss preamble_sub.c) = t_typing in

//   // inversion of t_typing to get comp typing,
//   // inversion of comp typing to get comp pre typing
//   let unsolved_goals_typing:
//     vprop_typing (pst_env preamble_sub.uvs ss)
//                  (list_as_vprop unsolved_goals) = magic () in

//   let remaining_ctxt_typing:
//     vprop_typing g0 (list_as_vprop remaining_ctxt) = p.remaining_ctxt_typing in

//   let (| steps, steps_typing |) = idem_steps (pst_env preamble_sub.uvs ss) (list_as_vprop remaining_ctxt) in
//   let steps_typing:
//     st_typing (pst_env preamble_sub.uvs ss)
//               steps
//               (ghost_comp preamble_sub.ctxt (tm_star (list_as_vprop remaining_ctxt) solved_goals)) = steps_typing in
  
//   // solved_goals is Tm_Tmp, ss is empty, and unsolved_goals = comp_pre preamble_sub.c
//   let c_pre_inv:
//     vprop_equiv (pst_env preamble_sub.uvs ss)
//                 (Psubst.subst_term ss (comp_pre preamble_sub.c))
//                 (tm_star (list_as_vprop unsolved_goals) solved_goals) = magic () in

//   (| x,
//      preamble_sub, 
//     { ss; solved_goals; unsolved_goals; remaining_ctxt; steps;
//       t_typing; unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
//       c_pre_inv; solved_goals_closed = () } |)

// let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y === x} = x

// #push-options "--z3rlimit_factor 4 --fuel 2 --ifuel 2 --query_stats --using_facts_from '* -FStar.Reflection -Steel'"
// let intro_exists_step (#preamble:_) (p:prover_state preamble)
//   (u:universe) (b:binder) (body:vprop) (unsolved_goals':list vprop)
//   (_:squash (p.unsolved_goals == (tm_exists_sl u b body) :: unsolved_goals'))
//   (prover:prover_t)
//   : T.Tac (option (p':prover_state preamble { p' `pst_extends` p })) =
  
//   let g0 = preamble.g0 in
//   let (| x, s_preamble, sp |) = intro_exists_sub_prover_state 
//     p u b body
//     (magic ())  // typing of tm_exists_sl, should come from the typing of unmatched goals
//   in
//   let sp = prover sp in
//   match sp with
//   | None -> None
//   | Some sp ->
//     // The following code to finish a terminal prover state is common
//     //   with the top-level prover, could be factored out
//     if x `Set.mem` Psubst.dom sp.ss
//     then begin
//       let c_pre_inv:
//         vprop_equiv (pst_env s_preamble.uvs sp.ss)
//                     (Psubst.subst_term sp.ss (comp_pre s_preamble.c))
//                     (tm_star (list_as_vprop []) sp.solved_goals) = sp.c_pre_inv in
//       // normalize list_as_vprop []
//       let c_pre_inv:
//         vprop_equiv (pst_env s_preamble.uvs sp.ss)
//                     (Psubst.subst_term sp.ss (comp_pre s_preamble.c))
//                     sp.solved_goals = magic () in
//       let remaining_ctxt = list_as_vprop sp.remaining_ctxt in
//       let steps_typing:
//         st_typing (pst_env s_preamble.uvs sp.ss) sp.steps
//           (ghost_comp s_preamble.ctxt (tm_star remaining_ctxt sp.solved_goals)) = sp.steps_typing in
//       // replace pst.solved_goals with equivalent (Psubst.subst_term pst.ss (comp_pre preamble.c))
//       //   from c_pre_inv
//       // note that all these postconditions are ln
//       let steps_typing:
//         st_typing (pst_env s_preamble.uvs sp.ss) sp.steps
//           (ghost_comp s_preamble.ctxt
//                       (tm_star remaining_ctxt
//                                (Psubst.subst_term sp.ss (comp_pre s_preamble.c)))) = magic () in
//       let t_typing:
//         st_typing (pst_env s_preamble.uvs sp.ss)
//                   (Psubst.subst_st_term sp.ss s_preamble.t)
//                   (Psubst.subst_comp sp.ss s_preamble.c) = sp.t_typing in
//       assert (comp_pre (Psubst.subst_comp sp.ss s_preamble.c) ==
//               Psubst.subst_term sp.ss (comp_pre s_preamble.c));
//       // NT substs are invariant under shifting
//       assume (shift_subst (Psubst.as_subst sp.ss) == Psubst.as_subst sp.ss);
//       assert (comp_post (Psubst.subst_comp sp.ss s_preamble.c) ==
//               Psubst.subst_term sp.ss (tm_exists_sl u b body));
//       // bind steps_typing and t_typing
//       // what's left is remaining ctxt and exists vprop
//       let t : st_term = magic () in
//       let t_typing:
//         st_typing (pst_env s_preamble.uvs sp.ss)
//                   t
//                   (ghost_comp
//                      s_preamble.ctxt
//                      (tm_star remaining_ctxt (Psubst.subst_term sp.ss (tm_exists_sl u b body))))
//         = magic () in

//       // now we get back to the original prover we got,
//       //   and have to find a way to combine the two
    
//       let uvs = psubst_env (filter_ss preamble.uvs p.ss) p.ss in
//       let uvs = push_binding_def uvs x b.binder_ty in


//       // target : pst_env preamble.uvs (ss + p.ss)
//       assume (~ (x `Set.mem` dom g0));
//       assume (freevars (Psubst.lookup sp.ss x) `Set.subset` dom g0);
//       assume (Set.subset (Psubst.dom (Psubst.singleton g0 x (Psubst.lookup sp.ss x))) (Psubst.dom sp.ss));
//       let sp_ss = Psubst.diff sp.ss (Psubst.singleton g0 x (Psubst.lookup sp.ss x)) in
//       assume (Set.disjoint (Psubst.dom p.ss) (Psubst.dom sp_ss));  // this takes time ...
//       assume (equal (pst_env s_preamble.uvs sp.ss)
//                     (pst_env preamble.uvs (Psubst.push p.ss sp_ss)));
//       // calc (equal) {
//       //   pst_env s_preamble.uvs sp.ss;
//       //      (equal) { }
//       //   pst_env (push_binding (psubst_env (filter_ss preamble.uvs p.ss) p.ss) x b.binder_ty) sp.ss;
//       //      (equal) { assume (Psubst.subst_term p.ss b.binder_ty == b.binder_ty) }  // b.binder_ty freevars should be disjoint from p.ss
//       //   pst_env (push_binding (psubst_env (filter_ss preamble.uvs p.ss) p.ss) x (Psubst.subst_term p.ss b.binder_ty)) sp.ss;
//       //      (equal) { assume (push_binding (psubst_env (filter_ss preamble.uvs p.ss) p.ss) x (Psubst.subst_term p.ss b.binder_ty) ==
//       //                        psubst_env (push_binding (filter_ss preamble.uvs p.ss) x b.binder_ty) p.ss) }
//       //   pst_env (psubst_env (push_binding (filter_ss preamble.uvs p.ss) x b.binder_ty) p.ss) sp.ss;
//       //      (equal) { assume (push_binding (filter_ss preamble.uvs p.ss) x b.binder_ty ==
//       //                        filter_ss (push_binding preamble.uvs x b.binder_ty) p.ss) }  // p.ss does not have x
//       //   pst_env (psubst_env (filter_ss (push_binding preamble.uvs x b.binder_ty) p.ss) p.ss) sp.ss;
//       //      (equal) { }
//       //   push_env g0 (psubst_env (filter_ss (psubst_env (filter_ss (push_binding preamble.uvs x b.binder_ty) p.ss) p.ss) sp.ss) sp.ss);
//       //      (equal) { admit () }  // some commutations of filter and push, and then pushing substs,
//       //                            // with the fact that x is in sp.ss, we checked it above
//       //   pst_env preamble.uvs (Psubst.push p.ss sp.ss);
//       // };

//       let ss_new = Psubst.push p.ss sp_ss in
//       let uvs = psubst_env (filter_ss preamble.uvs p.ss) p.ss in
//       assume (well_typed_ss uvs sp_ss);
//       assume (push_env g0 (psubst_env (filter_ss uvs sp_ss) sp_ss) ==
//               pst_env preamble.uvs ss_new);  // may be we can make a single combinator for filter and push,
//                                              // and prove subst push lemma for it

//       let pt_typing:
//         st_typing (pst_env preamble.uvs p.ss)
//                   p.steps
//                   (ghost_comp
//                      preamble.ctxt
//                      (tm_star (list_as_vprop p.remaining_ctxt) p.solved_goals)) = p.steps_typing in

//       let (| _, pt_typing |) = apply_partial_subs uvs sp_ss pt_typing in
//       let pt_typing:
//         st_typing (pst_env preamble.uvs ss_new)
//                   (Psubst.subst_st_term sp_ss p.steps)
//                   (Psubst.subst_comp sp_ss (ghost_comp preamble.ctxt (tm_star (list_as_vprop p.remaining_ctxt) p.solved_goals))) =
//         coerce_eq pt_typing () in
//       // p.solved goals is closed in g0, and p.remaining_ctxt is well typed in g0
//       assume (Psubst.subst_comp sp_ss (ghost_comp preamble.ctxt (tm_star (list_as_vprop p.remaining_ctxt) p.solved_goals)) ==
//               ghost_comp preamble.ctxt (tm_star (list_as_vprop p.remaining_ctxt) p.solved_goals));
//       let pt_typing:
//         st_typing (pst_env preamble.uvs ss_new)
//                   (Psubst.subst_st_term sp_ss p.steps)
//                   (ghost_comp preamble.ctxt (tm_star s_preamble.ctxt p.solved_goals)) = coerce_eq pt_typing () in
//       // recall t_typing from above, from sub prover state
//       let t_typing:
//         st_typing (pst_env preamble.uvs ss_new)
//                   t
//                   (ghost_comp
//                      s_preamble.ctxt
//                      (tm_star remaining_ctxt (Psubst.subst_term sp.ss (tm_exists_sl u b body))))
//         = coerce_eq t_typing () in

//       // bind pt_typing and t_typing
//       let steps : st_term = magic () in
//       let steps_typing:
//         st_typing (pst_env preamble.uvs ss_new)
//                   steps
//                   (ghost_comp
//                      preamble.ctxt (tm_star remaining_ctxt (tm_star (Psubst.subst_term sp.ss (tm_exists_sl u b body)) p.solved_goals))) = magic () in
      
//       assume (Psubst.subst_term sp.ss (tm_exists_sl u b body) ==
//               Psubst.subst_term sp_ss (tm_exists_sl u b body));  // sp_ss = sp.ss - x, and x is not free in tm_exists_sl
       
//       let steps_typing:
//         st_typing (pst_env preamble.uvs ss_new)
//                   steps
//                   (ghost_comp
//                      preamble.ctxt (tm_star remaining_ctxt (tm_star (Psubst.subst_term sp_ss (tm_exists_sl u b body)) p.solved_goals))) =
//         coerce_eq steps_typing () in

//       let c_pre_inv:
//         vprop_equiv (pst_env preamble.uvs p.ss)
//                     (Psubst.subst_term p.ss (comp_pre preamble.c))
//                     (tm_star (list_as_vprop p.unsolved_goals) p.solved_goals) = p.c_pre_inv in

//       let (| _, c_pre_inv |) = apply_partial_subs_veq uvs sp_ss c_pre_inv in
//       assert (Psubst.subst_term sp_ss (Psubst.subst_term p.ss (comp_pre preamble.c)) ==
//               Psubst.subst_term (Psubst.push p.ss sp_ss) (comp_pre preamble.c));
//       let c_pre_inv:
//         vprop_equiv (pst_env preamble.uvs ss_new)
//                     (Psubst.subst_term (Psubst.push p.ss sp_ss) (comp_pre preamble.c))
//                     (Psubst.subst_term sp_ss (tm_star (list_as_vprop ((tm_exists_sl u b body)::unsolved_goals')) p.solved_goals)) =
//         coerce_eq c_pre_inv () in
//       let c_pre_inv:
//         vprop_equiv (pst_env preamble.uvs ss_new)
//                     (Psubst.subst_term (Psubst.push p.ss sp_ss) (comp_pre preamble.c))
//                     (tm_star (Psubst.subst_term sp_ss (list_as_vprop unsolved_goals')) (tm_star (Psubst.subst_term sp_ss (tm_exists_sl u b body)) p.solved_goals))
//         = magic () in  // some rearrangement in the above c_pre_inv

      
//       // move t_typing from p over
//       let t_typing:
//         st_typing (pst_env preamble.uvs p.ss)
//                   (Psubst.subst_st_term p.ss preamble.t)
//                   (Psubst.subst_comp p.ss preamble.c) = p.t_typing in
      
//       let (| _, t_typing |) = apply_partial_subs uvs sp_ss t_typing in
//       let t_typing:
//         st_typing (pst_env preamble.uvs ss_new)
//                   (Psubst.subst_st_term ss_new preamble.t)
//                   (Psubst.subst_comp ss_new preamble.c) = coerce_eq t_typing () in


//       let ss = ss_new in
//       let solved_goals = tm_star (Psubst.subst_term sp_ss (tm_exists_sl u b body)) p.solved_goals in
//       let unsolved_goals = vprop_as_list (Psubst.subst_term sp_ss (list_as_vprop unsolved_goals')) in
//       let remaining_ctxt = vprop_as_list remaining_ctxt in
//       let steps = steps in

//       let t_typing
//         : st_typing (pst_env preamble.uvs ss)
//                     (Psubst.subst_st_term ss preamble.t)
//                     (Psubst.subst_comp ss preamble.c) = t_typing in

//       let remaining_ctxt_typing:
//         vprop_typing g0 (list_as_vprop remaining_ctxt) = sp.remaining_ctxt_typing in

//       let steps_typing
//         : st_typing (pst_env preamble.uvs ss)
//                     steps
//                     (ghost_comp
//                        preamble.ctxt
//                        (tm_star (list_as_vprop remaining_ctxt) solved_goals)) = steps_typing in

//       assume (well_typed_ss preamble.uvs ss);

//       Some ({
//         ss; solved_goals; unsolved_goals; remaining_ctxt; steps;
//         t_typing; unsolved_goals_typing = magic (); remaining_ctxt_typing; steps_typing;
//         c_pre_inv = magic (); solved_goals_closed = magic ()  // we need to add a runtime check that tm_exists_sl u t body is fully closed
//       })
//     end
//     else None
// #pop-options

// let intro_exists_prover_step = fun #_ _ -> magic ()