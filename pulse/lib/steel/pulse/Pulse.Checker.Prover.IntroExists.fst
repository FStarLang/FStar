module Pulse.Checker.Prover.IntroExists

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Checker.Prover.Base
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module PS = Pulse.Checker.Prover.Substs

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
                               witnesses = [e] }) in

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
    Pulse.Checker.Prover.Util.st_typing_weakening
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

  let x = fresh (push_env pst.pg pst.uvs) in
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
  assume (pst.ss.(tm_emp) == tm_emp);
  let pst_sub : prover_state preamble_sub = {
    pg = pst.pg;
    remaining_ctxt = vprop_as_list preamble_sub.ctxt;
    remaining_ctxt_frame_typing = magic ();
    uvs = push_binding pst.uvs x b.binder_ppname b.binder_ty;
    ss = pst.ss;
    solved = tm_emp;
    unsolved = (vprop_as_list (open_term_nv body px)) @ unsolved';
    k = k_sub;
    goals_inv = magic ();
    solved_inv = ();
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
    unsolved = [];
    k;
    goals_inv = magic ();
    solved_inv = magic ();
  } in

  pst'
#pop-options
