(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.CoreCheck

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
open FStarC.Class.Show
module Env = FStarC.TypeChecker.Env
module Core = FStarC.TypeChecker.Core
module TcUtil = FStarC.TypeChecker.Util
module Rel = FStarC.TypeChecker.Rel
module N = FStarC.TypeChecker.Normalize
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module Err = FStarC.TypeChecker.Err
module Errors = FStarC.Errors
module TcTerm = FStarC.TypeChecker.TcTerm
module S = FStarC.Syntax.Syntax

let enabled (env:Env.env) : ML bool =
  TcUtil.phase2_core_enabled () && not env.phase1 && not env.admit

let phase2 (env:Env.env) (what:string) (core:unit -> ML 'a) (tcterm:unit -> ML 'a) : ML 'a =
  if not (enabled env) then tcterm ()
  else
    let mode = TcUtil.phase2_core_mode () in
    if mode = "warn" || mode = "compare"
    then (
      let issues, res = Errors.catch_errors (fun () -> TcUtil.as_phase2_core_attempt core) in
      let errs, others = List.partition (fun (i:Errors.issue) -> Errors.EError? i.issue_level) issues in
      match errs, res with
      | [], Some r -> Errors.add_issues others; r
      | _ ->
        Errors.log_issue env Errors.Warning_Defensive
          (Errors.Msg.text ("Core failed to check " ^ what ^ ":")
           :: List.map (fun i -> Errors.Msg.text (Errors.format_issue i)) errs);
        tcterm ()
    )
    else core ()

let raise_core_error #a (env:Env.env) (what:string) (err:Core.error) : ML a =
  let r = match Core.error_range err with Some r -> r | None -> Env.get_range env in
  match Core.error_code err with
  | Some code -> Errors.raise_error r code (Core.error_message err)
  | None ->
    Errors.raise_error r Errors.Error_TypeError [
      Errors.Msg.text ("Core failed to check " ^ what ^ ".");
      Errors.Msg.text (Core.print_error err)
    ]

let discharge (env:Env.env) (g:option Core.guard_and_tok_t) : ML unit =
  match g with
  | None -> ()
  | Some (g, tok) ->
    Rel.force_trivial_guard env
      (Rel.simplify_guard env (Env.guard_of_guard_formula (NonTrivial g)));
    Core.commit_guard tok

let check_term (env:Env.env) (what:string) (e:term) (t:typ) (must_tot:bool) : ML unit =
  match Core.check_term env e t must_tot with
  | Inl g -> discharge env g
  | Inr err -> raise_core_error env what err

let compute_term_type (env:Env.env) (what:string) (e:term) : ML (Core.tot_or_ghost & typ) =
  match Core.compute_term_type env e with
  | Inl (eff, t, g) -> discharge env g; eff, t
  | Inr err -> raise_core_error env what err

let universe_of (env:Env.env) (what:string) (t:typ) : ML universe =
  let _, k = compute_term_type env what t in
  let k' = N.unfold_whnf env k |> U.unrefine in
  match (SS.compress k').n with
  | Tm_type u -> u
  | _ -> Err.expected_expression_of_type env t.pos (fst (U.type_u ())) t k

let check_subtyping (env:Env.env) (t0 t1:typ) : ML bool =
  match Core.check_term_subtyping true true env t0 t1 with
  | Inl g -> discharge env g; true
  | Inr _ -> false

let check_binders (env:Env.env) (what:string) (bs:binders) : ML (Env.env & universes) =
  let env, us =
    List.fold_left (fun (env, us) (b:binder) ->
      let u = universe_of env what b.binder_bv.sort in
      Env.push_binders env [b], u :: us) (env, []) bs
  in
  env, List.rev us

let rec check_smt_patterns (env:Env.env) (t:term) : ML unit =
  let under (bs:binders) (k:Env.env -> ML unit) : ML unit =
    let env = List.fold_left (fun env (b:binder) ->
      check_smt_patterns env b.binder_bv.sort;
      Env.push_binders env [b]) env bs in
    k env
  in
  let comp (env:Env.env) (c:comp) : ML unit =
    check_smt_patterns env (U.comp_result c)
  in
  match (SS.compress t).n with
  | Tm_arrow _ ->
    TcTerm.check_smt_pat env t;
    let bs, c = U.arrow_node_formals_comp_ln t in
    let bs, c = SS.open_comp bs c in
    under bs (fun env -> comp env c)
  | Tm_abs {b; body} ->
    let bs, body = SS.open_term [b] body in
    under bs (fun env -> check_smt_patterns env body)
  | Tm_refine {b; phi} ->
    check_smt_patterns env b.sort;
    let bs, phi = SS.open_term [S.mk_binder b] phi in
    check_smt_patterns (Env.push_binders env bs) phi
  | Tm_app {hd; arg=(a, _)} ->
    check_smt_patterns env hd;
    check_smt_patterns env a
  | Tm_ascribed {tm; asc=(asc, _, _)} ->
    check_smt_patterns env tm;
    (match asc with
     | Inl t -> check_smt_patterns env t
     | Inr c -> comp env c)
  | Tm_let {lbs=(false, [lb]); body} ->
    check_smt_patterns env lb.lbtyp;
    check_smt_patterns env lb.lbdef;
    (match lb.lbname with
     | Inl x ->
       let bs, body = SS.open_term [S.mk_binder x] body in
       check_smt_patterns (Env.push_binders env bs) body
     | Inr _ -> check_smt_patterns env body)
  | Tm_let {lbs=(true, lbs); body} ->
    let lbs, body = SS.open_let_rec lbs body in
    let env = List.fold_left (fun env (lb:letbinding) ->
      Env.push_let_binding env lb.lbname (lb.lbunivs, lb.lbtyp)) env lbs in
    List.iter (fun (lb:letbinding) ->
      check_smt_patterns env lb.lbtyp;
      check_smt_patterns env lb.lbdef) lbs;
    check_smt_patterns env body
  | Tm_match {scrutinee; brs} ->
    check_smt_patterns env scrutinee;
    List.iter (fun br ->
      let p, _, e = SS.open_branch br in
      let env = Env.push_bvs env (FStarC.Syntax.Syntax.pat_bvs p) in
      check_smt_patterns env e) brs
  | Tm_meta {tm} -> check_smt_patterns env tm
  | Tm_uinst (t, _) -> check_smt_patterns env t
  | _ -> ()
