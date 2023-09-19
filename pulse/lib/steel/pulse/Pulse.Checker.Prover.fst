module Pulse.Checker.Prover

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Base


module L = FStar.List.Tot
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Pprint = FStar.Stubs.Pprint
module Metatheory = Pulse.Typing.Metatheory
module PS = Pulse.Checker.Prover.Substs
module ElimExists = Pulse.Checker.Prover.ElimExists
module ElimPure =  Pulse.Checker.Prover.ElimPure
module Match = Pulse.Checker.Prover.Match
module IntroExists = Pulse.Checker.Prover.IntroExists
module IntroPure = Pulse.Checker.Prover.IntroPure


let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

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

let rec prove_pures #preamble (pst:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        is_terminal pst' }) =
  
  match pst.unsolved with
  | [] -> pst
  | {t=Tm_Pure p}::unsolved' ->
    let pst_opt = IntroPure.intro_pure pst p unsolved' () in
    (match pst_opt with
     | None ->
       let open Pulse.PP in
       fail_doc pst.pg None [
         text "Cannot prove pure proposition" ^/^
           pp p
       ]
     | Some pst1 ->
       let pst2 = prove_pures pst1 in
       assert (pst1 `pst_extends` pst);
       assert (pst2 `pst_extends` pst1);
       assert (pst2 `pst_extends` pst);
       pst2)
  | _ ->
    fail pst.pg None
      (Printf.sprintf "Impossible! prover.prove_pures: %s is not a pure, please file a bug-report"
         (P.term_to_string (L.hd pst.unsolved)))

#push-options "--z3rlimit_factor 4"
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
      | {t=Tm_Pure _}::tl -> prove_pures pst
      | q::tl ->
        let pst_opt = match_q pst q tl () 0 in
        match pst_opt with
        | None ->
          let open Pprint in
          let open Pulse.PP in
          let msg = [
            text "Error in proving precondition";
            text "Cannot prove:" ^^
                indent (pp q);
            text "In the context:" ^^
                indent (pp (list_as_vprop pst.remaining_ctxt))
          ] @ (if Pulse.Config.debug_flag "initial_solver_state" then [
                text "The prover was started with goal:" ^^
                    indent (pp preamble.goals);
                text "and initial context:" ^^
                    indent (pp preamble.ctxt);
               ] else [])
          in
          // GM: I feel I should use (Some q.range) instead of None, but that makes
          // several error locations worse.
          fail_doc pst.pg None msg
        | Some pst -> prover pst  // a little wasteful?
#pop-options

let rec get_q_at_hd (g:env) (l:list vprop) (q:vprop { L.existsb (fun v -> eq_tm v q) l })
  : l':list vprop &
    vprop_equiv g (list_as_vprop l) (q * list_as_vprop l') =

  match l with
  | hd::tl ->
    if eq_tm hd q then (| tl, magic () |)
    else let (| tl', _ |) = get_q_at_hd g tl q in
         (| hd::tl', magic () |)

#push-options "--z3rlimit_factor 4"
let prove
  (#g:env) (#ctxt:vprop) (ctxt_typing:vprop_typing g ctxt)
  (uvs:env { disjoint g uvs })
  (#goals:vprop) (goals_typing:vprop_typing (push_env g uvs) goals)

  : T.Tac (g1 : env { g1 `env_extends` g /\ disjoint g1 uvs } &
           nts : PS.nt_substs { PS.well_typed_nt_substs g1 uvs nts } &
           remaining_ctxt : vprop &
           continuation_elaborator g ctxt g1 ((PS.nt_subst_term goals nts) * remaining_ctxt)) =

  debug_prover g (fun _ ->
    Printf.sprintf "\nEnter top-level prove with ctxt: %s\ngoals: %s\n"
      (P.term_to_string ctxt) (P.term_to_string goals));

  let ctxt_l = vprop_as_list ctxt in

  if false && Nil? (bindings uvs) && L.existsb (fun v -> eq_tm v goals) ctxt_l
  then begin
    let (| l', d_eq |) = get_q_at_hd g ctxt_l goals in
    let g1 = g in
    let nts : PS.nt_substs = [] in
    let remaining_ctxt = list_as_vprop l' in
    let k : continuation_elaborator g ctxt g1 ctxt = k_elab_unit g ctxt in
    assume (list_as_vprop (vprop_as_list ctxt) == ctxt);
    let d_eq
      : vprop_equiv g ctxt ((PS.nt_subst_term goals nts) * remaining_ctxt) = coerce_eq d_eq () in
    (| g1, nts, remaining_ctxt, k_elab_equiv k (VE_Refl _ _) d_eq |)
  end
  else
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
    let pst0 : prover_state preamble = {
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

    let pst = prover pst0 in

    let nts : nts:PS.nt_substs { PS.well_typed_nt_substs pst.pg pst.uvs nts /\
                                 PS.is_permutation nts pst.ss } =
      let r = PS.ss_to_nt_substs pst.pg pst.uvs pst.ss in
      match r with
      | Inr msg ->
        fail pst.pg None
          (Printf.sprintf "prover error: ill-typed substitutions (%s)" msg)
      | Inl nts -> nts in
    let nts_uvs = PS.well_typed_nt_substs_prefix pst.pg pst.uvs nts uvs in
    let k
      : continuation_elaborator
          g (ctxt * tm_emp)
          pst.pg ((list_as_vprop pst.remaining_ctxt * tm_emp) * (PS.nt_subst_term pst.solved nts)) = pst.k in
    // admit ()
    let goals_inv
      : vprop_equiv (push_env pst.pg pst.uvs) goals (list_as_vprop [] * pst.solved) = pst.goals_inv in
    let goals_inv
      : vprop_equiv pst.pg (PS.nt_subst_term goals nts) (PS.nt_subst_term (list_as_vprop [] * pst.solved) nts) =
      PS.vprop_equiv_nt_substs_derived pst.pg pst.uvs goals_inv nts in
  
    // goals is well-typed in initial g + uvs
    // so any of the remaining uvs in pst.uvs should not be in goals
    // so we can drop their substitutions from the tail of nts
    assume (PS.nt_subst_term goals nts == PS.nt_subst_term goals nts_uvs);

    (| pst.pg, nts_uvs, list_as_vprop pst.remaining_ctxt, k_elab_equiv k (magic ()) (magic ()) |)
#pop-options

#push-options "--z3rlimit_factor 8 --fuel 0 --ifuel 1 --retry 5"
let try_frame_pre_uvs (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (uvs:env { disjoint g uvs })
  (#t:st_term) (#c:comp_st) (d:st_typing (push_env g uvs) t c)
  (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None) =

  let g = push_context g "try_frame_pre" t.range in

  let (| g1, nts, remaining_ctxt, k_frame |) =
    prove #g #_ ctxt_typing uvs #(comp_pre c) (magic ()) in
  // assert (nts == []);

  let d : st_typing (push_env g1 uvs) t c =
    Metatheory.st_typing_weakening g uvs t c d g1 in

  assert (comp_pre (PS.nt_subst_comp c nts) == PS.nt_subst_term (comp_pre c) nts);
  let t = PS.nt_subst_st_term t nts in
  let c = PS.nt_subst_comp c nts in

  let d : st_typing g1 t c =
    PS.st_typing_nt_substs_derived g1 uvs d nts in

  let k_frame : continuation_elaborator g ctxt g1 (comp_pre c * remaining_ctxt) = coerce_eq k_frame () in

  let x = fresh g1 in
  let ty = comp_res c in
  let g2 = push_binding g1 x res_ppname ty in
  assert (g2 `env_extends` g1);
  let ctxt' = (open_term_nv (comp_post c) (res_ppname, x) * remaining_ctxt) in

  let d : st_typing g1 t c = Metatheory.st_typing_weakening_standard d g1 in

  let k
    : continuation_elaborator g1 (remaining_ctxt * comp_pre c)
                              g2 ctxt' =
    continuation_elaborator_with_bind remaining_ctxt d (magic ()) (res_ppname, x) in

  let k
    : continuation_elaborator g1 (comp_pre c * remaining_ctxt)
                              g2 ctxt' =
    k_elab_equiv k (VE_Comm _ _ _) (VE_Refl _ _) in

  let k = k_elab_trans k_frame k in

  let comp_res_typing_in_g1, _, f =
    Metatheory.st_comp_typing_inversion_cofinite
      (Metatheory.comp_typing_inversion (Metatheory.st_typing_correctness d)) in

  let d_ty
    : universe_of g2 ty (comp_u c) =
    Metatheory.tot_typing_weakening_single comp_res_typing_in_g1 x (comp_res c) in

  assume (~ (x `Set.mem` freevars (comp_post c)));
  let d_post
    : vprop_typing g2 (open_term_nv (comp_post c) (res_ppname, x)) =
    f x in

  // the magic is for the ctxt' typing
  // see d_post for post typing
  // then the remaining_ctxt typing should come from the prover state
  //   TODO: add it there
  // and then ctxt' is just their `*`
  (| x, g2, (| comp_u c, ty, d_ty |), (| ctxt', magic () |), k |)
#pop-options

let try_frame_pre (#g:env) (#ctxt:vprop) (ctxt_typing:tot_typing g ctxt tm_vprop)
  (#t:st_term) (#c:comp_st) (d:st_typing g t c) (res_ppname:ppname)

  : T.Tac (checker_result_t g ctxt None) =

  let uvs = mk_env (fstar_env g) in
  assert (equal g (push_env g uvs));
  try_frame_pre_uvs ctxt_typing uvs d res_ppname

let prove_post_hint (#g:env) (#ctxt:vprop)
  (r:checker_result_t g ctxt None)
  (post_hint:post_hint_opt g)
  (rng:range)
  
  : T.Tac (checker_result_t g ctxt post_hint) =

  let g = push_context g "prove_post_hint" rng in

  match post_hint with
  | None -> r
  | Some post_hint ->
    let (| x, g2, (| u_ty, ty, ty_typing |), (| ctxt', ctxt'_typing |), k |) = r in

    let ppname = mk_ppname_no_range "_posth" in
    let post_hint_opened = open_term_nv post_hint.post (ppname, x) in

    // TODO: subtyping
    if not (eq_tm ty post_hint.ret_ty)
    then
      let open Pulse.PP in
      fail_doc g (Some rng) [
        text "Error in proving postcondition";
        text "The return type" ^^
          indent (pp ty) ^/^
        text "does not match the expected" ^^
          indent (pp post_hint.ret_ty)
      ]
    else if eq_tm post_hint_opened ctxt'
    then (| x, g2, (| u_ty, ty, ty_typing |), (| ctxt', ctxt'_typing |), k |)
    else
      let (| g3, nts, remaining_ctxt, k_post |) =
        prove #g2 #ctxt' ctxt'_typing (mk_env (fstar_env g2)) #post_hint_opened (magic ()) in
          
      assert (nts == []);
      let k_post
        : continuation_elaborator g2 ctxt' g3 (post_hint_opened * remaining_ctxt) =
        coerce_eq k_post () in

      match check_equiv_emp g3 remaining_ctxt with
      | None -> 
        let open Pulse.PP in
        fail_doc g (Some rng) [
          text "Error in proving postcondition";
          text "Inferred postcondition additionally contains" ^^
            indent (pp remaining_ctxt);
          (if Tm_Star? remaining_ctxt.t
           then text "Did you forget to free these resources?"
           else text "Did you forget to free this resource?");
        ]
      | Some d ->
        let k_post
          : continuation_elaborator g2 ctxt' g3 post_hint_opened =
          k_elab_equiv k_post (VE_Refl _ _) (magic ()) in
        //
        // for the typing of ty in g3,
        // we have typing of ty in g2 above, and g3 `env_extends` g2
        //
        //
        // for the typing of post_hint_opened,
        // again post_hint is well-typed in g, and g3 `env_extends` g
        //
        (| x, g3, (| u_ty, ty, magic () |), (| post_hint_opened, magic () |), k_elab_trans k k_post |)
