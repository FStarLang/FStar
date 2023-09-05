module Pulse.Checker.Prover.IntroPure

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Typing.Metatheory
open Pulse.Checker.Pure
open Pulse.Checker.VPropEquiv
open Pulse.Checker.Prover.Base
open Pulse.Checker.Base
open Pulse.Checker.Prover.Util

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module PS = Pulse.Checker.Prover.Substs

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

let k_intro_pure (g:env) (p:term)
  (d:tot_typing g p tm_prop)
  (token:prop_validity g p) (frame:vprop)
  
  : T.Tac (continuation_elaborator g frame g (frame * tm_pure p)) =

  let t = wr (Tm_IntroPure {p}) in
  let c = comp_intro_pure p in
  let d : st_typing g t c = T_IntroPure g p d token in

  let x = fresh g in

  // p is well-typed in g, so it does not have x free
  assume (open_term p x == p);

  let ppname = mk_ppname_no_range "_pintrop" in
  let k : continuation_elaborator
            g (frame * tm_emp)
            (push_binding g x ppname_default tm_unit) (tm_pure p * frame) =
    continuation_elaborator_with_bind frame d (magic ()) (ppname, x) in

  let k : continuation_elaborator
            g frame
            (push_binding g x ppname_default tm_unit) (frame * tm_pure p) =
    k_elab_equiv k (magic ()) (magic ()) in

  fun post_hint r ->
  let (| t1, c1, d1 |) = r in
  let d1 : st_typing g t1 c1 = d1 in
  let empty_env = mk_env (fstar_env g) in
  assert (equal g (push_env g empty_env));
  assert (equal (push_env (push_binding g x ppname_default tm_unit) empty_env)
                (push_binding g x ppname_default tm_unit));
  let d1 : st_typing (push_binding g x ppname_default tm_unit) t1 c1 =
    st_typing_weakening
      g
      empty_env
      t1 c1 d1
      (push_binding g x ppname_default tm_unit) in

  k post_hint (| t1, c1, d1 |)

module R = FStar.Reflection.V2

// let is_eq2 (t:R.term) : option (R.term & R.term) =
//   let head, args = R.collect_app_ln t in
//   match R.inspect_ln head, args with
//   | R.Tv_FVar fv, [_; (a1, _); (a2, _)]
//   | R.Tv_UInst fv _, [_; (a1, _); (a2, _)] -> 
//     let l = R.inspect_fv fv in
//     if l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"] ||
//        l = ["Prims"; "eq2"]
//     then Some (a1, a2)
//     else None
//   | _ -> None

let is_eq2_uvar (uvs:env) (t:term)
  : option (uv:var { uv `Set.mem` freevars t } & term) =
  
  match is_eq2 t with
  | None -> None
  | Some (l, r) ->
    match is_var l with
    | Some nm ->
      if Set.mem nm.nm_index (dom uvs)
      then Some (| nm.nm_index, r |)
      else None
    | None ->
      match is_var r with
      | Some nm ->
        if Set.mem nm.nm_index (dom uvs)
        then Some (| nm.nm_index, l |)
        else None
      | _ -> None

module RF = FStar.Reflection.V2.Formula
let rec try_collect_substs (uvs:env) (t:term)
  : T.Tac (ss:PS.ss_t { PS.dom ss `Set.subset` freevars t }) =
  assume (PS.dom PS.empty == Set.empty);
  match t.t with
  | Tm_FStar rt ->
    let f = RF.term_as_formula' rt in
    begin
      match f with
      | RF.And rt0 rt1 ->
        assume (not_tv_unknown rt0 /\ not_tv_unknown rt1);
        let ss0 = try_collect_substs uvs (tm_fstar rt0 FStar.Range.range_0) in
        let ss1 = try_collect_substs uvs (tm_fstar rt1 FStar.Range.range_0) in
        if PS.check_disjoint ss0 ss1
        then let r = PS.push_ss ss0 ss1 in
             assume (PS.dom r `Set.subset` freevars t);
             r
        else PS.empty
      | _ ->
        match is_eq2_uvar uvs t with
        | Some (| uv, e |) ->
          assume (~ (uv `Set.mem` (PS.dom PS.empty)));
          let r = PS.push PS.empty uv e in
          assume (PS.dom r `Set.subset` freevars t);
          r
        | None -> PS.empty
    end

  | _ -> PS.empty

let intro_pure (#preamble:_) (pst:prover_state preamble)
  (t:term)
  (unsolved':list vprop)
  (_:squash (pst.unsolved == (tm_pure t)::unsolved'))
  : T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

  let t_ss = pst.ss.(t) in

  debug_prover pst.pg (fun _ ->
    Printf.sprintf "Intro pure trying to typecheck prop: %s with uvs: %s\n"
      (P.term_to_string t_ss)
      (env_to_string pst.uvs));


  let ss' = try_collect_substs pst.uvs t_ss in
  assume (PS.dom pst.ss `Set.disjoint` PS.dom ss');
  let ss_new = PS.push_ss pst.ss ss' in
  assume (ss_new `ss_extends` pst.ss);

  let t_ss = ss_new.(t) in
  let d = core_check_tot_term_with_expected_type pst.pg t_ss tm_prop in
  let d_valid = check_prop_validity pst.pg t_ss d in

  // let (| ss_new, t_ss, d, d_valid |) : ss_new:PS.ss_t { ss_new `ss_extends` pst.ss } &
  //                                      t_ss:term { t_ss == ss_new.(t) } &
  //                                      tot_typing pst.pg t_ss tm_prop &
  //                                      prop_validity pst.pg t_ss =
  //   match is_eq2_uvar pst.pg pst.uvs t_ss with
  //   | Some (| uv, e |) ->
  //     // uv is a freevar in t_ss,
  //     //   which is obtained by applying pst.ss to t
  //     // so uv can't possibly in the domain of pst.ss
  //     // or it could be a check?
  //     assume (~ (uv `Set.mem` (PS.dom pst.ss)));
  //     assume (~ (PS.contains PS.empty uv));
  //     let ss_uv = PS.push PS.empty uv e in
  //     let t_ss_new = ss_uv.(t_ss) in
  //     assume (Set.disjoint (PS.dom ss_uv) (PS.dom pst.ss));
  //     let ss_new = PS.push_ss pst.ss ss_uv in
  //     assume (t_ss_new == ss_new.(t));
  //     // we know this is refl, can we avoid this call?
  //     let token = check_prop_validity pst.pg t_ss_new (magic ()) in
  //     (| ss_new,
  //        t_ss_new,
  //        magic (),
  //        token |)
  //   | None ->
  //     //
  //     // we need to check that t is closed in pst.pg
  //     // this is one way
  //     //
  //     let d = core_check_term_with_expected_type pst.pg t_ss tm_prop in
  //     (| pst.ss, t_ss, E d, check_prop_validity pst.pg t_ss (E d) |) in

  let x = fresh (push_env pst.pg pst.uvs) in

  let solved_new = (tm_pure t) * pst.solved in
  let unsolved_new = unsolved' in

  let k : continuation_elaborator
            preamble.g0 (preamble.ctxt * preamble.frame)
            pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * ss_new.(solved_new)) =
    let frame = (list_as_vprop pst.remaining_ctxt * preamble.frame) * ss_new.(pst.solved) in
    let k_pure
      : continuation_elaborator
          pst.pg frame
          pst.pg (frame * (tm_pure t_ss)) =
      k_intro_pure _ _ d d_valid frame in
    // some *s
    let veq
      : vprop_equiv pst.pg
          (((list_as_vprop pst.remaining_ctxt * preamble.frame) * ss_new.(pst.solved)) * tm_pure t_ss)
          ((list_as_vprop pst.remaining_ctxt * preamble.frame) * (tm_pure t_ss * ss_new.(pst.solved))) =
      magic () in

    // need lemmas in Prover.Subst
    assume (tm_pure ss_new.(t) * ss_new.(pst.solved) ==
            ss_new.(tm_pure t * pst.solved));

    let k_pure : continuation_elaborator
      pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * ss_new.(pst.solved))
      pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * ss_new.(solved_new)) =

      k_elab_equiv k_pure (VE_Refl _ _) veq in


    let k_pst : continuation_elaborator
      preamble.g0 (preamble.ctxt * preamble.frame)
      pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved)) = pst.k in

    assume (pst.ss.(pst.solved) == ss_new.(pst.solved));
    let k_pst : continuation_elaborator
      preamble.g0 (preamble.ctxt * preamble.frame)
      pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * ss_new.(pst.solved)) = coerce_eq k_pst () in

    k_elab_trans k_pst k_pure in

  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs)
                  preamble.goals
                  (list_as_vprop ((tm_pure t)::unsolved_new) * pst.solved) = pst.goals_inv in

  let veq : vprop_equiv (push_env pst.pg pst.uvs)
                        (list_as_vprop ((tm_pure t)::unsolved_new))
                        (list_as_vprop unsolved_new * tm_pure t) = magic () in

  let veq : vprop_equiv (push_env pst.pg pst.uvs)
                        (list_as_vprop ((tm_pure t)::unsolved_new) * pst.solved)
                        ((list_as_vprop unsolved_new * tm_pure t) * pst.solved) =
    VE_Ctxt _ _ _ _ _ veq (VE_Refl _ _) in

  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs)
                  preamble.goals
                  ((list_as_vprop unsolved_new * tm_pure t) * pst.solved) =
    VE_Trans _ _ _ _ goals_inv veq in

  let veq : vprop_equiv (push_env pst.pg pst.uvs)
                        ((list_as_vprop unsolved_new * tm_pure t) * pst.solved)
                        (list_as_vprop unsolved_new * (tm_pure t * pst.solved)) =
    VE_Sym _ _ _ (VE_Assoc _ _ _ _) in

  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs)
                  preamble.goals
                  (list_as_vprop unsolved_new * solved_new) =
    VE_Trans _ _ _ _ goals_inv veq in

  assume (freevars ss_new.(solved_new) `Set.subset` dom pst.pg);

  let pst_new : prover_state preamble = { pst with ss = ss_new;
                                                   solved = solved_new;
                                                   unsolved = unsolved_new;
                                                   k;
                                                   goals_inv;
                                                   solved_inv = () } in

  Some pst_new
