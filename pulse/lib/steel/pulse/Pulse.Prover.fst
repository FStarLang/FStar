module Pulse.Prover

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Util
open Pulse.Prover.Common

module T = FStar.Tactics

module Psubst = Pulse.Prover.Substs

let vprop_as_list_of_list_as_vprop (l:list vprop)
  : Lemma (vprop_as_list (list_as_vprop l) == l)
          [SMTPat (vprop_as_list (list_as_vprop l))] = admit ()

let list_as_vprop_of_vprop_as_list (p:vprop)
  : Lemma (list_as_vprop (vprop_as_list p) == p)
          [SMTPat (list_as_vprop (vprop_as_list p))] = admit ()

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y === x} = x

let prover : prover_t = admit ()

#push-options "--z3rlimit_factor 2 --fuel 1 --ifuel 1"
let prove_precondition (#g:env) (#ctxt:term) (ctxt_typing:vprop_typing g ctxt)
  (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
  : T.Tac (option (t:st_term &
                   c:comp_st { comp_pre c == ctxt } &
                   st_typing g t c)) =
  
  let preamble = {
    g0 = g; ctxt; ctxt_typing; t; c; uvs = mk_env (fstar_env g)
  } in

  let ss = Psubst.empty g in
  let solved_goals = Tm_Emp in
  let unsolved_goals = vprop_as_list (comp_pre c) in
  let remaining_ctxt = vprop_as_list ctxt in
  assert (equal (pst_env preamble.uvs ss) g);
  assume (Psubst.subst_st_term ss preamble.t == preamble.t);
  assume (Psubst.subst_comp ss preamble.c == preamble.c);
  let t_typing:
    st_typing (pst_env preamble.uvs ss)
              (Psubst.subst_st_term ss preamble.t)
              (Psubst.subst_comp ss preamble.c) = t_typing in
  
  // inversion of input t_typing to get comp_typing,
  // followed by inversion of comp_typing
  let unsolved_goals_typing:
    vprop_typing g (comp_pre c) = magic () in

  let remaining_ctxt_typing:
    vprop_typing preamble.g0 (list_as_vprop remaining_ctxt) = ctxt_typing in

  let (| steps, steps_typing |) = idem_steps g ctxt in
  let steps_typing:
    st_typing (pst_env preamble.uvs ss)
              steps
              (ghost_comp preamble.ctxt (Tm_Star (list_as_vprop remaining_ctxt) solved_goals)) = steps_typing in

  // some emp manipulation
  let c_pre_inv:
    vprop_equiv (pst_env preamble.uvs ss)
                (Psubst.subst_term ss (comp_pre preamble.c))
                (Tm_Star (list_as_vprop unsolved_goals) solved_goals) = magic () in

  let pst : prover_state preamble = {
    ss; solved_goals; unsolved_goals; remaining_ctxt; steps;
    t_typing; unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
    c_pre_inv; solved_goals_closed = ()
  } in

  let pst = prover pst in
  match pst with
  | None -> None
  | Some pst ->
    let g0 = preamble.g0 in
    assert (equal g0 (pst_env preamble.uvs pst.ss));
    let c_pre_inv:
      vprop_equiv g0 (Psubst.subst_term pst.ss (comp_pre preamble.c))
                     (Tm_Star (list_as_vprop []) pst.solved_goals) = pst.c_pre_inv in
    // normalize Tm_Star in the second vprop of vprop_equiv
    let c_pre_inv:
      vprop_equiv g0 (Psubst.subst_term pst.ss (comp_pre preamble.c))
                     pst.solved_goals = magic () in

    let remaining_ctxt = list_as_vprop pst.remaining_ctxt in
    let steps_typing:
      st_typing g0 pst.steps
        (ghost_comp preamble.ctxt (Tm_Star remaining_ctxt pst.solved_goals)) = pst.steps_typing in
    // replace pst.solved_goals with equivalent (Psubst.subst_term pst.ss (comp_pre preamble.c))
    //   from c_pre_inv
    // note that all these postconditions are ln
    let steps_typing:
      st_typing g0 pst.steps
        (ghost_comp preamble.ctxt
                    (Tm_Star remaining_ctxt
                             (Psubst.subst_term pst.ss (comp_pre preamble.c)))) = magic () in
    let t_typing:
      st_typing g0
                (Psubst.subst_st_term pst.ss preamble.t)
                (Psubst.subst_comp pst.ss preamble.c) = pst.t_typing in
    assert (comp_pre (Psubst.subst_comp pst.ss preamble.c) ==
            Psubst.subst_term pst.ss (comp_pre preamble.c));
    // bind steps_typing and t_typing
    let t : st_term = magic () in
    let post : term = magic () in
    let t_typing:
      st_typing g0 t (ghost_comp preamble.ctxt post) = magic () in
    Some (| t, ghost_comp preamble.ctxt post, t_typing |)
#pop-options
