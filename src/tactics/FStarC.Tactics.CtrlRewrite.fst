(*
   Copyright 2008-2016 Microsoft Research

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

module FStarC.Tactics.CtrlRewrite

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Util
open FStarC.Reflection.V2.Data
open FStarC.Reflection.V2.Builtins
open FStarC.Tactics.Result
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Tactics.Types
open FStarC.Tactics.Monad
open FStarC.Tactics.Common
open FStarC.Syntax.Syntax
open FStarC.Class.Show
open FStarC.Class.Monad
open FStarC.Syntax.Print {}

module BU     = FStarC.Util
module S      = FStarC.Syntax.Syntax
module U      = FStarC.Syntax.Util
module SS     = FStarC.Syntax.Subst
module Env    = FStarC.TypeChecker.Env
module TcComm = FStarC.TypeChecker.Common
module N      = FStarC.TypeChecker.Normalize
module Const  = FStarC.Const
module Errors = FStarC.Errors

let rangeof g = g.goal_ctx_uvar.ctx_uvar_range

let __do_rewrite
    (g0:goal)
    (rewriter : rewriter_ty)
    (env : env)
    (tm : term)
  : tac term
=
  (*
   * We skip certain terms. In particular if the term is a constant
   * which must have an argument (reify, reflect, range_of,
   * set_range_of), since typechecking will then fail, and the tactic
   * will also not be able to do anything useful. Morally, `reify` is
   * not a term, so it's fine to skip it.
   *
   * This is not perfect since if we have any other node wrapping the
   * `reify` (metadata?) this will still fail. But I don't think that
   * ever happens currently.
   *)
  let should_skip =
    match (SS.compress tm).n with
    | S.Tm_constant (Const.Const_reify _)
    | S.Tm_constant (Const.Const_reflect _)
    | S.Tm_constant Const.Const_range_of
    | S.Tm_constant Const.Const_set_range_of ->
      true
    | _ -> false
  in
  if should_skip then return tm else begin

    (* It's important to keep the original term if we want to do
     * nothing, (hence the underscore below) since after the call to
     * the typechecker, t can be elaborated and have more structure. In
     * particular, it can be abscribed and hence CONTAIN t AS A SUBTERM!
     * Which would cause an infinite loop between this function and
     * ctrl_fold_env.
     *
     * If we got an error about a layered effect missing an annotation,
     * we just skip the term, for reasons similar to unapplied constants
     * above. Other exceptions are re-raised.
     *)
    let res =
      try
        Errors.with_ctx "While typechecking a subterm for ctrl_rewrite" (fun () ->
          (* NS: Should we use Core here? *)
          
          Some (env.tc_term ({ env with admit = true }) tm))
      with
      | Errors.Error (Errors.Error_LayeredMissingAnnot, _, _, _) -> None
      | e -> raise e
    in
    match res with
    | None -> return tm
    | Some (_, lcomp, g) ->

    if not (TcComm.is_pure_or_ghost_lcomp lcomp) then 
      return tm (* SHOULD THIS CHECK BE IN maybe_rewrite INSTEAD? *)
    else
    let g = FStarC.TypeChecker.Rel.solve_deferred_constraints env g in
    let typ = lcomp.res_typ in

    (* unrefine typ as is done for the type arg of eq2 *)
    let typ =
      if Options.Ext.enabled "__unrefine" then
        let typ_norm = N.unfold_whnf' [Env.DontUnfoldAttr [Parser.Const.do_not_unrefine_attr]] env typ in
        if Tm_refine? (SS.compress typ_norm).n then
          (* It is indeed a refinement, normalize again to remove them. *)
          let typ' = N.unfold_whnf' [Env.DontUnfoldAttr [Parser.Const.do_not_unrefine_attr]; Env.Unrefine] env typ_norm in
          typ'
        else
          typ
      else
        typ
    in

    let should_check =
      if FStarC.TypeChecker.Common.is_total_lcomp lcomp 
      then None
      else Some (Allow_ghost "do_rewrite.lhs")
    in
    let! ut, uvar_t =
      new_uvar "do_rewrite.rhs" env typ 
               should_check
               (goal_typedness_deps g0)
               (rangeof g0)
    in
    if_verbose (fun () ->
                  BU.print2 "do_rewrite: making equality\n\t%s ==\n\t%s\n"
                    (show tm) (show ut)) ;!
    add_irrelevant_goal
                      g0
                      "do_rewrite.eq"
                      env
                      (U.mk_eq2 (env.universe_of env typ) typ tm ut)
                      None ;!
    (* v1 and v2 match *)
    focus rewriter ;!
    // Try to get rid of all the unification lambdas
    let ut = N.reduce_uvar_solutions env ut in
    if_verbose (fun () ->
       BU.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                   (show tm)
                   (show ut)) ;!
    return ut
  end

(* If __do_rewrite fails with the SKIP exception we do nothing *)
let do_rewrite
    (g0:goal)
    (rewriter : rewriter_ty)
    (env : env)
    (tm : term)
  : tac term
  = match! catch (__do_rewrite g0 rewriter env tm) with
    | Inl SKIP -> return tm
    | Inl e -> traise e
    | Inr tm' -> return tm'

type ctac 'a = 'a -> tac ('a & ctrl_flag)

(* Transform a value x with c1, and continue with c2 if needed *)
let seq_ctac (c1 : ctac 'a) (c2 : ctac 'a)
  : ctac 'a
  = fun (x:'a) ->
      let! x', flag = c1 x in
      match flag with
      | Abort -> return (x', Abort)
      | Skip -> return (x', Skip)
      | Continue -> c2 x'

let par_combine = function
  | Abort, _
  | _, Abort -> Abort
  | Skip, _
  | _, Skip -> Skip
  | Continue, Continue -> Continue

(* Transform a value (x, y) with cl and cr respectively.
 * Skip on x will still run c2 on y, but Abort will abort. *)
let par_ctac (cl : ctac 'a) (cr : ctac 'b)
  : ctac ('a & 'b)
  = fun (x, y) ->
      let! x, flag = cl x in
      match flag with
      | Abort -> return ((x, y), Abort)
      | fa ->
        let! y, flag = cr y in
        match flag with
        | Abort -> return ((x, y),Abort)
        | fb ->
          return ((x, y), par_combine (fa, fb))

let rec map_ctac (c : ctac 'a)
  : ctac (list 'a)
  = fun xs ->
      match xs with
      | [] -> return ([], Continue)
      | x::xs ->
        let! ((x, xs), flag) = par_ctac c (map_ctac c) (x, xs) in
        return (x::xs, flag)

(* let bind_ctac *)
(*     (t : ctac 'a) *)
(*     (f : 'a -> ctac 'b) *)
(*   : ctac 'b *)
(*   = fun b -> failwith "" *)

let ctac_id : #a:Type -> ctac a =
  fun #a (x:a) -> return (x, Continue)

let ctac_args (c : ctac term) : ctac args =
  map_ctac (par_ctac c (ctac_id #_))

let maybe_rewrite
    (g0 : goal)
    (controller : controller_ty)
    (rewriter   : rewriter_ty)
    (env : env)
    (tm : term)
  : tac (term & ctrl_flag)
  = let! (rw, ctrl_flag) = controller tm in
    let! tm' = 
         if rw
         then do_rewrite g0 rewriter env tm
         else return tm
    in
    return (tm', ctrl_flag)

let rec ctrl_fold_env
    (g0 : goal)
    (d : direction)
    (controller : controller_ty)
    (rewriter : rewriter_ty)
    (env : env)
    (tm : term)
  : tac (term & ctrl_flag)
  = let recurse tm =
      ctrl_fold_env g0 d controller rewriter env tm
    in
    match d with
    | TopDown ->
      seq_ctac (maybe_rewrite g0 controller rewriter env)
               (on_subterms g0 d controller rewriter env) tm

    | BottomUp ->
      seq_ctac (on_subterms g0 d controller rewriter env)
               (maybe_rewrite g0 controller rewriter env) tm

and recurse_option_residual_comp (env:env) (retyping_subst:list subst_elt) (rc_opt:option residual_comp) recurse
  : tac (option residual_comp & ctrl_flag)
  = // return (None, Continue)
    match rc_opt with
    | None -> return (None, Continue)
    | Some rc ->
      match rc.residual_typ with
      | None -> return (Some rc, Continue)
      | Some t ->
        let t = SS.subst retyping_subst t in
        let! t, flag = recurse env t in
        return (Some ({rc with residual_typ=Some t}), flag)

and on_subterms
    (g0 : goal)
    (d : direction)
    (controller : controller_ty)
    (rewriter : rewriter_ty)
    (env : env)
    (tm : term)
  : tac (term & ctrl_flag)
  = let recurse env tm = ctrl_fold_env g0 d controller rewriter env tm in
    let rr = recurse env in (* recurse on current env *)

    //
    // t is the body and k is the option residual comp
    // 
    // Note, the type of the binder sorts may change as we rewrite them
    // The retyping_subst is an identity substitution that replaces the bound vars
    // in the term with their new variants tagged with the rewritten bv sorts
    //
    let rec descend_binders orig accum_binders retyping_subst accum_flag env bs t k rebuild =
      match bs with
      | [] ->
        let t = SS.subst retyping_subst t in
        let! t, t_flag = recurse env t in
        begin
        match t_flag with
        | Abort -> return (orig.n, t_flag) //if anything aborts, just return the original abs
        | _ ->
          let! k, k_flag = recurse_option_residual_comp env retyping_subst k recurse in
          let bs = List.rev accum_binders in
          let subst = SS.closing_of_binders bs in
          // For dependent binders, we need to re-compute the substitution incrementally; applying subst to bs doesn't work
          let bs = SS.close_binders bs in
          let t = SS.subst subst t in
          let k = BU.map_option (SS.subst_residual_comp subst) k in
          return (rebuild bs t k,
               par_combine (accum_flag, (par_combine (t_flag, k_flag))))
        end
        
      | b::bs ->
        let s = SS.subst retyping_subst b.binder_bv.sort in
        let! s, flag = recurse env s in
        match flag with
        | Abort -> return (orig.n, flag) //if anything aborts, just return the original abs
        | _ ->
          let bv = {b.binder_bv with sort = s} in
          let b = {b with binder_bv = bv} in
          let env = Env.push_binders env [b] in
          let retyping_subst = NT(bv, bv_to_name bv) :: retyping_subst in
          descend_binders orig (b::accum_binders) retyping_subst (par_combine (accum_flag, flag)) env bs t k rebuild
    in
    let go () : tac (term' & ctrl_flag) =
      let tm = SS.compress tm in
      match tm.n with
      (* Run on hd and args in parallel *)
      | Tm_app {hd; args} ->
        let! ((hd, args), flag) = par_ctac rr (ctac_args rr) (hd, args) in
        return (Tm_app {hd; args}, flag)

      (* Open, descend, rebuild *)
      | Tm_abs {bs; body=t; rc_opt=k} ->
        let bs_orig, t, subst = SS.open_term' bs t in
        let k = k |> BU.map_option (SS.subst_residual_comp subst) in
        descend_binders tm [] [] Continue env bs_orig t k
                        (fun bs t k -> Tm_abs {bs; body=t; rc_opt=k})

      | Tm_refine {b=x; phi} -> 
        let bs, phi = SS.open_term [S.mk_binder x] phi in
        descend_binders tm [] [] Continue env bs phi None  //no residual comp
                        (fun bs phi _ ->
                          let x = 
                            match bs with
                            | [x] -> x.binder_bv
                            | _ -> failwith "Impossible"
                          in
                          Tm_refine {b=x; phi})

      | Tm_arrow { bs = bs; comp = comp } ->
        (match comp.n with
        | Total t ->
          let bs_orig, t = SS.open_term bs t in
          descend_binders tm [] [] Continue env bs_orig t None
                          (fun bs t _ -> Tm_arrow {bs; comp = {comp with n = Total t}})
        | GTotal t ->
          let bs_orig, t = SS.open_term bs t in
          descend_binders tm [] [] Continue env bs_orig t None
                          (fun bs t _ -> Tm_arrow {bs; comp = {comp with n = GTotal t}})
        | _ ->
          (* Do nothing (FIXME).
            What should we do for effectful computations? *)
          return (tm.n, Continue))

      (* Descend on head and branches in parallel. Branches
       * are opened with their contexts extended. Ignore the when clause,
       * and do not go into patterns.
       * also ignoring the return annotations *)
      | Tm_match {scrutinee=hd; ret_opt=asc_opt; brs; rc_opt=lopt} ->
        let c_branch (br:S.branch) : tac (S.branch & ctrl_flag) =
          let (pat, w, e) = SS.open_branch br in
          let bvs = S.pat_bvs pat in
          let! e, flag = recurse (Env.push_bvs env bvs) e in
          let br = SS.close_branch (pat, w, e) in
          return (br, flag)
        in
        let! ((hd, brs), flag) = par_ctac rr (map_ctac c_branch) (hd, brs) in
        return (Tm_match {scrutinee=hd; ret_opt=asc_opt; brs; rc_opt=lopt}, flag)

      (* Descend, in parallel, in the definiens and the body, where
       * the body is extended with the bv. Do not go into the type. *)
      | Tm_let {lbs=(false, [{ lbname = Inl bv; lbdef = def }]); body=e} ->
        (* ugh *)
        let lb = match (SS.compress tm).n with
                 | Tm_let {lbs=(false, [lb])} -> lb
                 | _ -> failwith "impossible"
        in
        let bv, e = SS.open_term_bv bv e in
        let! ((lbdef, e), flag) =
             par_ctac rr (recurse (Env.push_bv env bv)) (lb.lbdef, e)
        in
        let lb = { lb with lbdef = lbdef } in
        let e = SS.close [S.mk_binder bv] e in
        return (Tm_let {lbs=(false, [lb]); body=e}, flag)

      (* Descend, in parallel, in *every* definiens and the body.
       * Again body is properly opened, and we don't go into types. *)
     | Tm_let {lbs=(true, lbs); body=e} ->
       let c_lb (lb:S.letbinding) : tac (S.letbinding & ctrl_flag) =
         let! (def, flag) = rr lb.lbdef in
         return ({lb with lbdef = def }, flag)
       in
       let lbs, e = SS.open_let_rec lbs e in
       (* TODO: the `rr` has to be wrong, we need more binders *)
       let! ((lbs, e), flag) = par_ctac (map_ctac c_lb) rr (lbs, e) in
       let lbs, e = SS.close_let_rec lbs e in
       return (Tm_let {lbs=(true, lbs); body=e}, flag)

     (* Descend into the ascripted term, ignore all else *)
     | Tm_ascribed {tm=t; asc; eff_opt=eff} ->
       let! t, flag = rr t in
       return (Tm_ascribed {tm=t; asc; eff_opt=eff}, flag)

     (* Ditto *)
     | Tm_meta {tm=t; meta=m} ->
       let! (t, flag) = rr t in
       return (Tm_meta {tm=t; meta=m}, flag)

     | _ ->
       (* BU.print1 "GG ignoring %s\n" (tag_of tm); *)
       return (tm.n, Continue)
    in
    let! (tmn', flag) = go () in
    return ({tm with n = tmn'}, flag)

let do_ctrl_rewrite
    (g0 : goal)
    (dir : direction)
    (controller : controller_ty)
    (rewriter   : rewriter_ty)
    (env : env)
    (tm : term)
  : tac term
  = let! tm', _ = ctrl_fold_env g0 dir controller rewriter env tm in
    return tm'

let ctrl_rewrite
    (dir : direction)
    (controller : controller_ty)
    (rewriter   : rewriter_ty)
  : tac unit
  = wrap_err "ctrl_rewrite" <| (
    let! ps = get in
    let g, gs = match ps.goals with
                | g::gs -> g, gs
                | [] -> failwith "no goals"
    in
    dismiss_all ;!
    let gt = (goal_type g) in
    if_verbose (fun () ->
        BU.print1 "ctrl_rewrite starting with %s\n" (show gt)) ;!

    let! gt' = do_ctrl_rewrite g dir controller rewriter (goal_env g) gt in

    if_verbose (fun () ->
        BU.print1 "ctrl_rewrite seems to have succeded with %s\n" (show gt')) ;!

    push_goals gs ;!
    let g = goal_with_type g gt' in
    add_goals [g]
    )
