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

module FStar.Tactics.CtrlRewrite

open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Syntax.Syntax
open FStar.Reflection.Data
open FStar.Reflection.Basic
open FStar.Tactics.Result
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Tactics.Basic
open FStar.Tactics.Types
open FStar.Tactics.Monad
open FStar.Tactics.Common

module Print  = FStar.Syntax.Print
module BU     = FStar.Compiler.Util
module S      = FStar.Syntax.Syntax
module U      = FStar.Syntax.Util
module SS     = FStar.Syntax.Subst
module Z      = FStar.BigInt
module Env    = FStar.TypeChecker.Env
module TcComm = FStar.TypeChecker.Common
module N      = FStar.TypeChecker.Normalize
module Const  = FStar.Const
module Errors = FStar.Errors

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
    | S.Tm_constant Const.Const_reify
    | S.Tm_constant (Const.Const_reflect _)
    | S.Tm_constant Const.Const_range_of
    | S.Tm_constant Const.Const_set_range_of ->
      true
    | _ -> false
  in
  if should_skip then ret tm else begin

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
          Some (env.tc_term ({ env with Env.lax = true }) tm))
      with
      | Errors.Error (Errors.Error_LayeredMissingAnnot, _, _, _) -> None
      | e -> raise e
    in
    match res with
    | None -> ret tm
    | Some (_, lcomp, g) ->

    if not (TcComm.is_pure_or_ghost_lcomp lcomp) then 
      ret tm (* SHOULD THIS CHECK BE IN maybe_rewrite INSTEAD? *)
    else
    let typ = lcomp.res_typ in
    bind (new_uvar "do_rewrite.rhs" env typ None [] (rangeof g0)) (fun (ut, uvar_ut) ->
    mlog (fun () ->
       BU.print2 "do_rewrite: making equality\n\t%s ==\n\t%s\n"
         (Print.term_to_string tm) (Print.term_to_string ut)) (fun () ->
    bind (add_irrelevant_goal
                      g0
                      "do_rewrite.eq"
                      env
                      (U.mk_eq2 (env.universe_of env typ) typ tm ut)) (fun _ ->
    bind (focus rewriter) (fun () ->
    // Try to get rid of all the unification lambdas
    let ut = N.reduce_uvar_solutions env ut in
    mlog (fun () ->
       BU.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                   (Print.term_to_string tm)
                   (Print.term_to_string ut)) (fun () ->
    ret ut)))))
  end

(* If __do_rewrite fails with "SKIP" we do nothing *)
let do_rewrite
    (g0:goal)
    (rewriter : rewriter_ty)
    (env : env)
    (tm : term)
  : tac term
= bind (catch (__do_rewrite g0 rewriter env tm)) (function
       | Inl (TacticFailure "SKIP") -> ret tm
       | Inl e -> traise e
       | Inr tm' -> ret tm')

type ctac 'a = 'a -> tac ('a * ctrl_flag)

(* Transform a value x with c1, and continue with c2 if needed *)
let seq_ctac (c1 : ctac 'a) (c2 : ctac 'a)
  : ctac 'a
  = fun (x:'a) ->
      bind (c1 x) (fun (x', flag) ->
      match flag with
      | Abort -> ret (x', Abort)
      | Skip -> ret (x', Skip)
      | Continue -> c2 x')

let par_combine = function
  | Abort, _
  | _, Abort -> Abort
  | Skip, _
  | _, Skip -> Skip
  | Continue, Continue -> Continue

(* Transform a value (x, y) with cl and cr respectively.
 * Skip on x will still run c2 on y, but Abort will abort. *)
let par_ctac (cl : ctac 'a) (cr : ctac 'b)
  : ctac ('a * 'b)
  = fun (x, y) ->
      bind (cl x) (fun (x, flag) ->
      match flag with
      | Abort -> ret ((x, y), Abort)
      | fa ->
        bind (cr y) (fun (y, flag) ->
        match flag with
        | Abort -> ret ((x, y),Abort)
        | fb ->
          ret ((x, y), par_combine (fa, fb))))

let rec map_ctac (c : ctac 'a)
  : ctac (list 'a)
  = fun xs ->
      match xs with
      | [] -> ret ([], Continue)
      | x::xs ->
        bind (par_ctac c (map_ctac c) (x, xs)) (fun ((x, xs), flag) ->
        ret (x::xs, flag))

(* let bind_ctac *)
(*     (t : ctac 'a) *)
(*     (f : 'a -> ctac 'b) *)
(*   : ctac 'b *)
(*   = fun b -> failwith "" *)

let ctac_id (* : ctac 'a *) =
  fun (x:'a) -> ret (x, Continue)

let ctac_args (c : ctac term) : ctac args =
  map_ctac (par_ctac c ctac_id)

let maybe_rewrite
    (g0 : goal)
    (controller : controller_ty)
    (rewriter   : rewriter_ty)
    (env : env)
    (tm : term)
  : tac (term * ctrl_flag)
  = bind (controller tm) (fun (rw, ctrl_flag) ->
    bind (if rw
          then do_rewrite g0 rewriter env tm
          else ret tm) (fun tm' ->
    ret (tm', ctrl_flag)))

let rec ctrl_fold_env
    (g0 : goal)
    (d : direction)
    (controller : controller_ty)
    (rewriter : rewriter_ty)
    (env : env)
    (tm : term)
  : tac (term * ctrl_flag)
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
  = // ret (None, Continue)
    match rc_opt with
    | None -> ret (None, Continue)
    | Some rc ->
      match rc.residual_typ with
      | None -> ret (Some rc, Continue)
      | Some t ->
        let t = SS.subst retyping_subst t in
        bind (recurse env t) (fun (t, flag) ->
        ret (Some ({rc with residual_typ=Some t}), flag))

and on_subterms
    (g0 : goal)
    (d : direction)
    (controller : controller_ty)
    (rewriter : rewriter_ty)
    (env : env)
    (tm : term)
  : tac (term * ctrl_flag)
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
        bind (recurse env t) (fun (t, t_flag) ->
        match t_flag with
        | Abort -> ret (orig.n, t_flag) //if anything aborts, just return the original abs
        | _ ->
          bind (recurse_option_residual_comp env retyping_subst k recurse) (fun (k, k_flag) ->
          let bs = List.rev accum_binders in
          let subst = SS.closing_of_binders bs in
          let bs = SS.subst_binders subst bs in
          let t = SS.subst subst t in
          let k = BU.map_option (SS.subst_residual_comp subst) k in
          ret (rebuild bs t k,
               par_combine (accum_flag, (par_combine (t_flag, k_flag))))))
      | b::bs ->
        let s = SS.subst retyping_subst b.binder_bv.sort in
        bind (recurse env s) (fun (s, flag) ->
        match flag with
        | Abort -> ret (orig.n, flag) //if anything aborts, just return the original abs
        | _ ->
          let bv = {b.binder_bv with sort = s} in
          let b = {b with binder_bv = bv} in
          let env = Env.push_binders env [b] in
          let retyping_subst = NT(bv, bv_to_name bv) :: retyping_subst in
          descend_binders orig (b::accum_binders) retyping_subst (par_combine (accum_flag, flag)) env bs t k rebuild)
    in
    let go () : tac (term' * ctrl_flag) =
      let tm = SS.compress tm in
      match tm.n with
      (* Run on hd and args in parallel *)
      | Tm_app (hd, args) ->
        bind (par_ctac rr (ctac_args rr) (hd, args)) (fun ((hd, args), flag) ->
        ret (Tm_app (hd, args), flag))

      (* Open, descend, rebuild *)
      | Tm_abs (bs, t, k) ->
        let bs_orig, t, subst = SS.open_term' bs t in
        let k = k |> BU.map_option (SS.subst_residual_comp subst) in
        descend_binders tm [] [] Continue env bs_orig t k
                        (fun bs t k -> Tm_abs(bs, t, k))

      | Tm_refine (x, phi) -> 
        let bs, phi = SS.open_term [S.mk_binder x] phi in
        descend_binders tm [] [] Continue env bs phi None  //no residual comp
                        (fun bs phi _ ->
                          let x = 
                            match bs with
                            | [x] -> x.binder_bv
                            | _ -> failwith "Impossible"
                          in
                          Tm_refine (x, phi))
      
      (* Do nothing (FIXME) *)
      | Tm_arrow (bs, k) ->
        ret (tm.n, Continue)

      (* Descend on head and branches in parallel. Branches
       * are opened with their contexts extended. Ignore the when clause,
       * and do not go into patterns.
       * also ignoring the return annotations *)
      | Tm_match (hd, asc_opt, brs, lopt) ->
        let c_branch (br:S.branch) : tac (S.branch * ctrl_flag) =
          let (pat, w, e) = SS.open_branch br in
          let bvs = S.pat_bvs pat in
          bind (recurse (Env.push_bvs env bvs) e) (fun (e, flag) ->
          let br = SS.close_branch (pat, w, e) in
          ret (br, flag))
        in
        bind (par_ctac rr (map_ctac c_branch) (hd, brs)) (fun ((hd, brs), flag) ->
        ret (Tm_match (hd, asc_opt, brs, lopt), flag))

      (* Descend, in parallel, in the definiens and the body, where
       * the body is extended with the bv. Do not go into the type. *)
      | Tm_let ((false, [{ lbname = Inl bv; lbdef = def }]), e) ->
        (* ugh *)
        let lb = match (SS.compress tm).n with
                 | Tm_let ((false, [lb]), _) -> lb
                 | _ -> failwith "impossible"
        in
        let bv, e = SS.open_term_bv bv e in
        bind (par_ctac rr (recurse (Env.push_bv env bv)) (lb.lbdef, e))
                                                                (fun ((lbdef, e), flag) ->
        let lb = { lb with lbdef = lbdef } in
        let e = SS.close [S.mk_binder bv] e in
        ret (Tm_let ((false, [lb]), e), flag))

      (* Descend, in parallel, in *every* definiens and the body.
       * Again body is properly opened, and we don't go into types. *)
     | Tm_let ((true, lbs), e) ->
       let c_lb (lb:S.letbinding) : tac (S.letbinding * ctrl_flag) =
         bind (rr lb.lbdef) (fun (def, flag) ->
         ret ({lb with lbdef = def }, flag))
       in
       let lbs, e = SS.open_let_rec lbs e in
       (* TODO: the `rr` has to be wrong, we need more binders *)
       bind (par_ctac (map_ctac c_lb) rr (lbs, e)) (fun ((lbs, e), flag) ->
       let lbs, e = SS.close_let_rec lbs e in
       ret (Tm_let ((true, lbs), e), flag))

     (* Descend into the ascripted term, ignore all else *)
     | Tm_ascribed (t, asc, eff) ->
       bind (rr t) (fun (t, flag) -> ret (Tm_ascribed (t, asc, eff), flag))

     (* Ditto *)
     | Tm_meta (t, m) ->
       bind (rr t) (fun (t, flag) -> ret (Tm_meta (t, m), flag))

     | _ ->
       (* BU.print1 "GG ignoring %s\n" (Print.tag_of_term tm); *)
       ret (tm.n, Continue)
    in
    bind (go ()) (fun (tmn', flag) ->
    ret ({tm with n = tmn'}, flag))

let do_ctrl_rewrite
    (g0 : goal)
    (dir : direction)
    (controller : controller_ty)
    (rewriter   : rewriter_ty)
    (env : env)
    (tm : term)
  : tac term
  = bind (ctrl_fold_env g0 dir controller rewriter env tm) (fun (tm', _) ->
    ret tm')

let ctrl_rewrite
    (dir : direction)
    (controller : controller_ty)
    (rewriter   : rewriter_ty)
  : tac unit
  = wrap_err "ctrl_rewrite" <|
    bind get (fun ps ->
    let g, gs = match ps.goals with
                | g::gs -> g, gs
                | [] -> failwith "no goals"
    in
    bind dismiss_all (fun _ ->

    let gt = (goal_type g) in
    log ps (fun () ->
        BU.print1 "ctrl_rewrite starting with %s\n" (Print.term_to_string gt));

    bind (do_ctrl_rewrite g dir controller rewriter (goal_env g) gt) (fun gt' ->

    log ps (fun () ->
        BU.print1 "ctrl_rewrite seems to have succeded with %s\n" (Print.term_to_string gt'));

    bind (push_goals gs) (fun _ ->
    let g = goal_with_type g gt' in
    add_goals [g]))))
