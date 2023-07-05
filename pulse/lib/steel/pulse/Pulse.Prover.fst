module Pulse.Prover

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Common

module ElimExists = Pulse.Prover.ElimExists
module ElimPure =  Pulse.Prover.ElimPure
module Match = Pulse.Prover.Match
module IntroExists = Pulse.Prover.IntroExists

module T = FStar.Tactics.V2

module PS = Pulse.Prover.Substs

let unsolved_equiv_pst (#preamble:_) (pst:prover_state preamble) (unsolved':list vprop)
  (d:vprop_equiv (push_env pst.pg pst.uvs) (list_as_vprop pst.unsolved) (list_as_vprop unsolved'))
  : prover_state preamble =
  { pst with unsolved = unsolved'; goals_inv = magic () }

let remaining_ctxt_equiv_pst (#preamble:_) (pst:prover_state preamble) (remaining_ctxt':list vprop)
  (d:vprop_equiv pst.pg (list_as_vprop pst.remaining_ctxt) (list_as_vprop remaining_ctxt'))
  : prover_state preamble =
  { pst with remaining_ctxt = remaining_ctxt';
             remaining_ctxt_frame_typing = magic ();
             k = k_elab_equiv pst.k (VE_Refl _ _) (magic ()) }

let rec collect_exists (g:env) (l:list vprop)
  : exs:list vprop &
    rest:list vprop &
    vprop_equiv g (list_as_vprop l) (list_as_vprop (exs @ rest)) =
  
  match l with
  | [] -> (| [], [], VE_Refl _ _ |)
  | hd::tl ->
    let (| exs, rest, _ |) = collect_exists g tl in
    match hd.t with
    | Tm_ExistsSL _ _ _ -> (| hd::exs, rest, magic () |)
    | _ -> (| exs, hd::rest, magic () |)

let rec collect_pures (g:env) (l:list vprop)
  : pures:list vprop &
    rest:list vprop &
    vprop_equiv g (list_as_vprop l) (list_as_vprop (rest @ pures)) =
  
  match l with
  | [] -> (| [], [], VE_Refl _ _ |)
  | hd::tl ->
    let (| pures, rest, _ |) = collect_pures g tl in
    match hd.t with
    | Tm_Pure _ -> (| hd::pures, rest, magic () |)
    | _ -> (| pures, hd::rest, magic () |)


module L = FStar.List.Tot
let move_hd_end (g:env) (l:list vprop { Cons? l })
  : vprop_equiv g (list_as_vprop l) (list_as_vprop (L.tl l @ [L.hd l])) = magic ()

let rec match_q (#preamble:_) (pst:prover_state preamble)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.unsolved == q::unsolved'))
  (i:nat)
  : T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

  if L.length pst.remaining_ctxt = 0
  then None
  else if i = L.length pst.remaining_ctxt
  then None
  else
    let p = L.hd pst.remaining_ctxt in
    let pst_opt =
      Match.match_step pst p (L.tl pst.remaining_ctxt) q unsolved' () in
    match pst_opt with
    | Some pst -> Some pst
    | None ->
      let pst =
        remaining_ctxt_equiv_pst pst (L.tl pst.remaining_ctxt @ [L.hd pst.remaining_ctxt])
          (move_hd_end pst.pg pst.remaining_ctxt) in
      match_q pst q unsolved' () (i+1)

let rec prover
  (#preamble:_)
  (pst0:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst0 /\
                                        is_terminal pst' }) =

  match pst0.unsolved with
  | [] -> pst0
  | _ ->
    let pst = ElimExists.elim_exists_pst pst0 in
    let pst = ElimPure.elim_pure_pst pst in

    let (| exs, rest, d |) = collect_exists (push_env pst.pg pst.uvs) pst.unsolved in
    let pst = unsolved_equiv_pst pst (exs@rest) d in

    match pst.unsolved with
    | {t=Tm_ExistsSL u b body}::unsolved' ->
      IntroExists.intro_exists pst u b body unsolved' () prover
    | _ ->
      let (| pures, rest, d |) = collect_pures (push_env pst.pg pst.uvs) pst.unsolved in
      let pst = unsolved_equiv_pst pst (rest@pures) d in
      match pst.unsolved with
      | {t=Tm_Pure _}::tl -> fail pst.pg None "intro pure not implemented yet"  // only pures left
      | q::tl ->
        let pst_opt = match_q pst q tl () 0 in
        match pst_opt with
        | None -> fail pst.pg None "cannot match a vprop"
        | Some pst -> prover pst  // a little wasteful?

#push-options "--z3rlimit_factor 4"
let prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:vprop_typing g ctxt)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:vprop_typing (push_env g uvs) goals)

  : T.Tac (g1 : env { g1 `env_extends` g } &
           uvs1 : env { uvs1 `env_extends` uvs /\ disjoint uvs1 g1 } &
           ss1 : PS.ss_t { well_typed_ss ss1 uvs1 g1 } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 (ss1.(goals) * remaining_ctxt)) =

  let ctxt_frame_typing : vprop_typing g (ctxt * tm_emp) = magic () in
  let preamble = {
    g0 = g;
    ctxt;
    frame = tm_emp;
    ctxt_frame_typing;
    goals;
  } in
  assume (list_as_vprop (vprop_as_list ctxt) == ctxt);
  assume (well_typed_ss PS.empty (mk_env (fstar_env g)) g);
  let pst : prover_state preamble = {
    pg = g;
    remaining_ctxt = vprop_as_list ctxt;
    remaining_ctxt_frame_typing = ctxt_frame_typing;
    uvs = uvs;
    ss = PS.empty;
    solved = tm_emp;
    unsolved = vprop_as_list goals;
    solved_typing = magic ();
    k = k_elab_equiv (k_elab_unit g ctxt) (magic ()) (magic ());
    goals_inv = magic ();
  } in
  let pst = prover pst in
  let ropt = PS.ss_to_nt_substs pst.pg pst.uvs pst.ss in
  if None? ropt then fail pst.pg None "prove: ss not well-typed";
  let Some nt = ropt in
  // let b = PS.check_well_typedness pst.pg pst.uvs pst.ss in
  // if not b then fail pst.pg None "prove: ss not well-typed";
  let k
    : continuation_elaborator
        g (ctxt * tm_emp)
        pst.pg ((list_as_vprop pst.remaining_ctxt * tm_emp) * pst.ss.(pst.solved)) = pst.k in
  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs) goals (list_as_vprop [] * pst.solved) = pst.goals_inv in
  let goals_inv
    : vprop_equiv pst.pg pst.ss.(goals) pst.ss.(list_as_vprop [] * pst.solved) =
    PS.vprop_equiv_nt_substs_derived pst.pg pst.uvs goals_inv nt in
  (| pst.pg, pst.uvs, pst.ss, list_as_vprop pst.remaining_ctxt, k_elab_equiv k (magic ()) (magic ()) |)
#pop-options

// let vprop_as_list_of_list_as_vprop (l:list vprop)
//   : Lemma (vprop_as_list (list_as_vprop l) == l)
//           [SMTPat (vprop_as_list (list_as_vprop l))] = admit ()

// let list_as_vprop_of_vprop_as_list (p:vprop)
//   : Lemma (list_as_vprop (vprop_as_list p) == p)
//           [SMTPat (list_as_vprop (vprop_as_list p))] = admit ()

// let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y === x} = x

// let prover : prover_t = fun #_ _ -> magic ()

// #push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
// let prove_precondition (#g:env) (#ctxt:term) (ctxt_typing:vprop_typing g ctxt)
//   (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
//   : T.Tac (option (t:st_term &
//                    c:comp_st { comp_pre c == ctxt } &
//                    st_typing g t c)) = magic ()
  
//   // let preamble = {
//   //   g0 = g; ctxt; ctxt_typing; t; c; uvs = mk_env (fstar_env g)
//   // } in

//   // let ss = Psubst.empty g in
//   // let solved_goals = tm_emp in
//   // let unsolved_goals = vprop_as_list (comp_pre c) in
//   // let remaining_ctxt = vprop_as_list ctxt in
//   // assert (equal (pst_env preamble.uvs ss) g);
//   // assume (Psubst.subst_st_term ss preamble.t == preamble.t);
//   // assume (Psubst.subst_comp ss preamble.c == preamble.c);
//   // let t_typing:
//   //   st_typing (pst_env preamble.uvs ss)
//   //             (Psubst.subst_st_term ss preamble.t)
//   //             (Psubst.subst_comp ss preamble.c) = t_typing in
  
//   // // inversion of input t_typing to get comp_typing,
//   // // followed by inversion of comp_typing
//   // let unsolved_goals_typing:
//   //   vprop_typing g (comp_pre c) = magic () in

//   // let remaining_ctxt_typing:
//   //   vprop_typing preamble.g0 (list_as_vprop remaining_ctxt) = ctxt_typing in

//   // let (| steps, steps_typing |) = idem_steps g ctxt in
//   // let steps_typing:
//   //   st_typing (pst_env preamble.uvs ss)
//   //             steps
//   //             (ghost_comp preamble.ctxt (tm_star (list_as_vprop remaining_ctxt) solved_goals)) = steps_typing in

//   // // some emp manipulation
//   // let c_pre_inv:
//   //   vprop_equiv (pst_env preamble.uvs ss)
//   //               (Psubst.subst_term ss (comp_pre preamble.c))
//   //               (tm_star (list_as_vprop unsolved_goals) solved_goals) = magic () in

//   // let pst : prover_state preamble = {
//   //   ss; solved_goals; unsolved_goals; remaining_ctxt; steps;
//   //   t_typing; unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
//   //   c_pre_inv; solved_goals_closed = ()
//   // } in

//   // let pst = prover pst in
//   // match pst with
//   // | None -> None
//   // | Some pst ->
//   //   let g0 = preamble.g0 in
//   //   assert (equal g0 (pst_env preamble.uvs pst.ss));
//   //   let c_pre_inv:
//   //     vprop_equiv g0 (Psubst.subst_term pst.ss (comp_pre preamble.c))
//   //                    (tm_star (list_as_vprop []) pst.solved_goals) = pst.c_pre_inv in
//   //   // normalize tm_star in the second vprop of vprop_equiv
//   //   let c_pre_inv:
//   //     vprop_equiv g0 (Psubst.subst_term pst.ss (comp_pre preamble.c))
//   //                    pst.solved_goals = magic () in

//   //   let remaining_ctxt = list_as_vprop pst.remaining_ctxt in
//   //   let steps_typing:
//   //     st_typing g0 pst.steps
//   //       (ghost_comp preamble.ctxt (tm_star remaining_ctxt pst.solved_goals)) = pst.steps_typing in
//   //   // replace pst.solved_goals with equivalent (Psubst.subst_term pst.ss (comp_pre preamble.c))
//   //   //   from c_pre_inv
//   //   // note that all these postconditions are ln
//   //   let steps_typing:
//   //     st_typing g0 pst.steps
//   //       (ghost_comp preamble.ctxt
//   //                   (tm_star remaining_ctxt
//   //                            (Psubst.subst_term pst.ss (comp_pre preamble.c)))) = magic () in
//   //   let t_typing:
//   //     st_typing g0
//   //               (Psubst.subst_st_term pst.ss preamble.t)
//   //               (Psubst.subst_comp pst.ss preamble.c) = pst.t_typing in
//   //   assert (comp_pre (Psubst.subst_comp pst.ss preamble.c) ==
//   //           Psubst.subst_term pst.ss (comp_pre preamble.c));
//   //   // bind steps_typing and t_typing
//   //   let t : st_term = magic () in
//   //   let post : term = magic () in
//   //   let t_typing:
//   //     st_typing g0 t (ghost_comp preamble.ctxt post) = magic () in
//   //   Some (| t, ghost_comp preamble.ctxt post, t_typing |)
// #pop-options
