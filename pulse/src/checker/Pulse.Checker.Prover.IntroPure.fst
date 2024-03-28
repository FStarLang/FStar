(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

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
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module PS = Pulse.Checker.Prover.Substs

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

let k_intro_pure (g:env) (p:term)
  (d:tot_typing g p tm_prop)
  (token:prop_validity g p) (frame:vprop)
  
  : T.Tac (continuation_elaborator g frame g (frame * tm_pure p)) =

  let t = wtag (Some STT_Ghost) (Tm_IntroPure {p}) in
  let c = comp_intro_pure p in
  let d : st_typing g t c = T_IntroPure g p d token in

  let x = fresh g in

  // p is well-typed in g, so it does not have x free
  assume (open_term p x == p);

  let ppname = mk_ppname_no_range "_pintrop" in
  let k : continuation_elaborator
            g (frame * tm_emp)
            (push_binding g x ppname_default tm_unit) (tm_pure p * frame) =
    continuation_elaborator_with_bind frame d (RU.magic ()) (ppname, x) in

  let k : continuation_elaborator
            g frame
            (push_binding g x ppname_default tm_unit) (frame * tm_pure p) =
    k_elab_equiv k (RU.magic ()) (RU.magic ()) in

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

let pure_uv_heuristic_t =
  uvs:env -> t:term ->
  T.Tac (option (uv:var { uv `Set.mem` freevars t } & term))
 
let is_eq2_uvar
: pure_uv_heuristic_t
= fun (uvs:env) (t:term) ->
    match is_eq2 t with
    | None -> None
    | Some (_, l, r) ->
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
let is_host_var (x:R.term) =
  match R.inspect_ln x with
  | R.Tv_Var nv ->
    let nv_view = R.inspect_namedv nv in
    Some {nm_index=nv_view.uniq;
          nm_ppname=mk_ppname (nv_view.ppname) (R.range_of_term x)}
  | _ -> None

let is_uvar_implication
: pure_uv_heuristic_t
= fun (uvs:env) (t:term) ->
    debug uvs (fun _ -> Printf.sprintf "is_uvar_implication??: %s\n" (P.term_to_string t));
    match inspect_term t with
    | Some _ -> None
    | None -> (
      let tt = t in
      let f = RF.term_as_formula' tt in
      match f with
      | RF.Implies t0 t1 -> (
        debug uvs (fun _ -> Printf.sprintf "is_uvar_implication, LHS=: %s\n" (T.term_to_string t0));
        match R.inspect_ln t0 with
        | R.Tv_Unknown -> None
        | _ -> (
          let t0 = tm_fstar t0 FStar.Range.range_0 in
          match is_eq2 t0 with
          | None -> None
          | Some (ty, lhs, rhs) ->
            if eq_tm ty (tm_fstar (`bool) FStar.Range.range_0)
            then (
              let try_negated maybe_var other_side
              : T.Tac  (option (uv:var { uv `Set.mem` freevars t } & term))
              = match is_var lhs with
                | None -> None
                | Some nm ->
                  if Set.mem nm.nm_index (dom uvs)
                  then (
                      match inspect_term rhs with
                      | Some _ -> None
                      | None -> 
                        let rhs = tm_fstar (`(not (`#(rhs)))) FStar.Range.range_0 in
                        assume (nm.nm_index `Set.mem` freevars t);
                        Some (| nm.nm_index, rhs |)
                      | _ -> None
                  )
                  else None
              in
              match try_negated lhs rhs with
              | None -> try_negated rhs lhs
              | x -> x
            )
            else None
          )
      )
      | _ -> None
    )
    | _ -> None

let pure_uvar_heursitics : pure_uv_heuristic_t
  = let h = [is_eq2_uvar; is_uvar_implication] in
    fun (uvs:env) (t:term) ->
      let rec loop (h:list pure_uv_heuristic_t)
       : T.Tac (option (uv:var { uv `Set.mem` freevars t } & term)) =
        match h with
        | [] -> None
        | h::hs ->
          match h uvs t with
          | None -> loop hs
          | Some (| uv, e |) -> Some (| uv, e |)
      in loop h

let rec try_collect_substs (uvs:env) (t:term)
  : T.Tac (ss:PS.ss_t { PS.dom ss `Set.subset` freevars t }) =
  assume (PS.dom PS.empty == Set.empty);
  match inspect_term t with
  | Some _ -> PS.empty
  | _ ->
    let rt = t in
    let f = RF.term_as_formula' rt in
    begin
      match f with
      | RF.And rt0 rt1 ->
        let ss0 = try_collect_substs uvs (tm_fstar rt0 FStar.Range.range_0) in
        let ss1 = try_collect_substs uvs (tm_fstar rt1 FStar.Range.range_0) in
        if PS.check_disjoint ss0 ss1
        then let r = PS.push_ss ss0 ss1 in
             assume (PS.dom r `Set.subset` freevars t);
             r
        else PS.empty
      | _ ->
        match pure_uvar_heursitics uvs t with
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
  let _ = 
    let fvs = freevars t_ss in
    if check_disjoint pst.uvs fvs
    then ()
    else 
      fail_doc pst.pg (Some (Pulse.RuntimeUtils.range_of_term t_ss))
        [Pulse.PP.text "Could not resolve all free variables in the proposition: ";
         P.term_to_doc t_ss;]
  in
  let d = core_check_tot_term pst.pg t_ss tm_prop in
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
  //     let token = check_prop_validity pst.pg t_ss_new (RU.magic ()) in
  //     (| ss_new,
  //        t_ss_new,
  //        RU.magic (),
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
      RU.magic () in

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
                        (list_as_vprop unsolved_new * tm_pure t) = RU.magic () in

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
                                                   nts = None;
                                                   solved = solved_new;
                                                   unsolved = unsolved_new;
                                                   k;
                                                   goals_inv;
                                                   solved_inv = () } in

  Some pst_new
