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

module P = Pulse.Syntax.Printer
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

  debug_prover pst0.pg (fun _ ->
    Printf.sprintf "At the prover top-level with remaining_ctxt: %s\nunsolved: %s"
      (P.term_to_string (list_as_vprop pst0.remaining_ctxt))
      (P.term_to_string (list_as_vprop pst0.unsolved)));

  match pst0.unsolved with
  | [] -> pst0
  | _ ->
    let pst = ElimExists.elim_exists_pst pst0 in

    debug_prover pst.pg (fun _ ->
      Printf.sprintf "prover: remaining_ctxt after elim exists: %s\n"
        (P.term_to_string (list_as_vprop pst.remaining_ctxt)));

    let pst = ElimPure.elim_pure_pst pst in

    debug_prover pst.pg (fun _ ->
      Printf.sprintf "prover: remaining_ctxt after elim pure: %s\n"
        (P.term_to_string (list_as_vprop pst.remaining_ctxt)));

    let (| exs, rest, d |) = collect_exists (push_env pst.pg pst.uvs) pst.unsolved in

    debug_prover pst.pg (fun _ ->
      Printf.sprintf "prover: tried to pull exists: exs: %s and rest: %s\n"
        (P.term_to_string (list_as_vprop exs)) (P.term_to_string (list_as_vprop rest)));

    let pst = unsolved_equiv_pst pst (exs@rest) d in

    debug_prover pst.pg (fun _ ->
      Printf.sprintf "prover: unsolved after pulling exists at the top: %s\n"
        (P.term_to_string (list_as_vprop pst.unsolved)));

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
           nts1 : PS.nt_substs { PS.well_typed_nt_substs g1 uvs1 nts1 } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 ((PS.nt_subst_term goals nts1) * remaining_ctxt)) =

  debug_prover g (fun _ ->
    Printf.sprintf "\nEnter top-level prove with ctxt: %s\ngoals: %s\n"
      (P.term_to_string ctxt) (P.term_to_string goals));

  let ctxt_frame_typing : vprop_typing g (ctxt * tm_emp) = magic () in
  let preamble = {
    g0 = g;
    ctxt;
    frame = tm_emp;
    ctxt_frame_typing;
    goals;
  } in
  assume (list_as_vprop (vprop_as_list ctxt) == ctxt);
  assume ((PS.empty).(tm_emp) == tm_emp);
  let pst : prover_state preamble = {
    pg = g;
    remaining_ctxt = vprop_as_list ctxt;
    remaining_ctxt_frame_typing = ctxt_frame_typing;
    uvs = uvs;
    ss = PS.empty;
    solved = tm_emp;
    unsolved = vprop_as_list goals;
    k = k_elab_equiv (k_elab_unit g ctxt) (magic ()) (magic ());
    goals_inv = magic ();
    solved_inv = ()
  } in

  let pst = prover pst in

  let ropt = PS.ss_to_nt_substs pst.pg pst.uvs pst.ss in

  if None? ropt then fail pst.pg None "prove: ss not well-typed";
  let Some nts = ropt in
  let k
    : continuation_elaborator
        g (ctxt * tm_emp)
        pst.pg ((list_as_vprop pst.remaining_ctxt * tm_emp) * (PS.nt_subst_term pst.solved nts)) = pst.k in
  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs) goals (list_as_vprop [] * pst.solved) = pst.goals_inv in
  let goals_inv
    : vprop_equiv pst.pg (PS.nt_subst_term goals nts) (PS.nt_subst_term (list_as_vprop [] * pst.solved) nts) =
    PS.vprop_equiv_nt_substs_derived pst.pg pst.uvs goals_inv nts in
  (| pst.pg, pst.uvs, nts, list_as_vprop pst.remaining_ctxt, k_elab_equiv k (magic ()) (magic ()) |)
#pop-options
