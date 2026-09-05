(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.SMTEncoding.ErrorReporting

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.BaseTypes
open FStarC.SMTEncoding.Term
open FStarC.SMTEncoding.Util
open FStarC.SMTEncoding
open FStarC.SMTEncoding.Env
open FStarC.SMTEncoding.EncodeTerm
open FStarC.Range
open FStarC.Class.Show
open FStarC.Ident
open FStarC.Syntax.Formula

module BU    = FStarC.Util
module Const = FStarC.Parser.Const
module S     = FStarC.Syntax.Syntax
module SE    = FStarC.Syntax.Embeddings
module SS    = FStarC.Syntax.Subst
module U     = FStarC.Syntax.Util

(* Smart constructors: a context or a branch with no goals under it is
   itself trivial, and must not be emitted. *)
let gctx (ds:list decl) (cs:list ctx_elt) (t:goal_tree) : goal_tree =
  match t with
  | GTrivial -> GTrivial
  | _ -> GCtx ds cs t

let gbranch (ts:list goal_tree) : ML goal_tree =
  match ts |> List.filter (function GTrivial -> false | _ -> true) with
  | [] -> GTrivial
  | [t] -> t
  | ts -> GBranch ts

let rec goals_of (t:goal_tree) : ML (list goal) =
  match t with
  | GTrivial -> []
  | GLeaf g -> [g]
  | GCtx _ _ t -> goals_of t
  | GBranch ts -> List.collect goals_of ts

let goal_context (t:goal_tree) (g:goal) : ML (list ctx_elt) =
  let rec aux (t:goal_tree) : ML (option (list ctx_elt)) =
    match t with
    | GTrivial -> None
    | GLeaf g' -> if g'.goal_id = g.goal_id then Some [] else None
    | GCtx _ cs t -> aux t |> Option.map (fun cs' -> cs @ cs')
    | GBranch ts ->
      List.fold_left (fun acc t -> match acc with Some _ -> acc | None -> aux t) None ts
  in
  Option.dflt [] (aux t)

let rec all_decls (t:goal_tree) : ML (list decl) =
  match t with
  | GTrivial -> []
  | GLeaf g -> [mkAssume (g.goal_term, None, "@goal_" ^ show g.goal_id)]
  | GCtx ds _ t -> ds @ all_decls t
  | GBranch ts -> List.collect all_decls ts

(* Is [t] a small quantifier-free formula?  Such a formula is cheap to
   assume: it adds no new quantifier instantiations, it only brings ground
   terms into the solver's congruence closure. *)
let quantifier_free (t:term) : ML bool =
    let budget = mk_ref 200 in
    let rec aux (t:term) : ML bool =
        if !budget <= 0 then false
        else begin
          budget := !budget - 1;
          match t with
          | Quant _ _ _ _ _ _ -> false
          | App _ tms _ -> List.for_all aux tms
          | Let tms t -> List.for_all aux tms && aux t
          | Labeled t _ _ -> aux t
          | _ -> true
        end
    in
    aux t

(* The nodes [encode_formula] looks through without changing the formula: a
   [Meta_labeled], which only attaches an error message, an explicit
   [FStar.Range.labeled], which is the same thing written by the user, and the
   [squash]/[by_tactic] wrappers. *)
let destruct_label (q:S.term) : ML (option (S.term & Errors.error_message & Range.t)) =
  match (SS.compress q).n with
  | S.Tm_meta {tm; meta=S.Meta_labeled (msg, r, _)} -> Some (tm, msg, r)
  | S.Tm_app _ ->
    let head, args = U.head_and_args_full q in
    (match (U.un_uinst head).n, args with
     | S.Tm_fvar fv, [(r, _); (msg, _); (phi, _)] when S.fv_eq_lid fv Const.labeled_lid ->
       (match SE.try_unembed r SE.id_norm_cb, SE.try_unembed msg SE.id_norm_cb with
        | Some r, Some s -> Some (phi, Errors.mkmsg s, r)
        | None, Some s -> Some (phi, Errors.mkmsg s, (phi <: S.term).pos)
        | _ -> None)
     | _ -> None)
  | _ -> None

let destruct_transparent (q:S.term) : ML (option S.term) =
  match (SS.compress q).n with
  | S.Tm_app _ ->
    let head, args = U.head_and_args_full q in
    (match (U.un_uinst head).n, args with
     | S.Tm_fvar fv, [_; (phi, _)] when S.fv_eq_lid fv Const.by_tactic_lid -> Some phi
     | S.Tm_fvar fv, [_; _; (phi, _)] when S.fv_eq_lid fv Const.rewrite_by_tactic_lid -> Some phi
     | S.Tm_fvar fv, [(phi, _)] when S.fv_eq_lid fv Const.squash_lid -> Some phi
     | _ -> None)
  | _ -> None

(* Flatten a conjunction, so that a left-nested chain of [/\] is walked in
   one pass rather than quadratically.  Labels are opaque: we never look
   through one. *)
let rec collect_conjuncts (q:S.term) : ML (list S.term) =
  if Some? (destruct_label q) || Some? (destruct_transparent q) then [q]
  else
    match destruct_typ_as_formula q with
    | Some (BaseConn (lid, [(p1, _); (p2, _)])) when lid_equals lid Const.and_lid ->
      collect_conjuncts p1 @ collect_conjuncts p2
    | _ -> [q]

let split_goals use_env_msg  //when present, provides an alternate error message,
                             //usually "could not check implicit argument",
                             //        "could not prove post-condition"
                             //or something like that
               (env:env_t)
               (q:S.term)    //the query
             : ML (goal_tree & decls_t)
             =
    let ctr = mk_ref 0 in
    (* Names for the constants and hypotheses we introduce.  The counter is
       local to the query: all of these declarations live inside a push/pop
       frame, so they only have to be unique within it, and keeping them
       independent of the rest of the run makes error messages reproducible. *)
    let name_ctr = mk_ref 0 in
    let fresh_name (prefix:string) : ML string =
      name_ctr := !name_ctr + 1;
      prefix ^ show !name_ctr
    in
    let flag, msg_prefix = match use_env_msg with
        | None -> false, Pprint.empty
        | Some f -> true, Pprint.doc_of_string (f()) in
    (* An assumption emitted by the walker.  It is given a fresh name, and no
       fact ids, so that --using_facts_from never filters it out. *)
    let hyp (t:term) : ML decl =
        mkAssume (t, None, fresh_name "@hypothesis_")
    in
    let mk_leaf (env:env_t) (msg:Errors.error_message) (ropt:option Range.t) (q:S.term)
      : ML (goal_tree & decls_t) =
        let open FStarC.Pprint in
        let t, decls = encode_formula q env in
        match t with
        | App TrueOp [] _ -> GTrivial, decls
        | _ ->
          let msg = if flag
                    then (Errors.Msg.text "Failed to verify implicit argument: " ^^ msg_prefix) :: msg
                    else msg in
          let rng = q.pos in
          let rng = match ropt with
                    | None -> rng
                    | Some r -> if Range.rng_included (Range.use_range rng) (Range.use_range r)
                                then rng
                                else Range.set_def_range r (Range.def_range rng)
          in
          ctr := !ctr + 1;
          GLeaf { goal_id = !ctr; goal_msg = msg; goal_range = rng;
                  goal_term = t; goal_source = q }, decls
    in
    (* [aux] returns the goal tree, the auxiliary declarations produced while
       encoding it, and a flag saying whether the tree really establishes the
       formula it was given.  The flag is false when the formula contains a
       match: we do not prove its default case, which F* has already shown to
       be unreachable, so the formula may not be assumed elsewhere. *)
    let rec aux (env:env_t)
                (default_msg : Errors.error_message) //the error message to report for a leaf
                (ropt:option Range.t)                //position of the enclosing Labeled node, if any
                (q:S.term)                           //the formula being split
     : ML (goal_tree & decls_t & bool)
     =
        let q = U.unascribe q in
        match destruct_label q with
        | Some (phi, msg, r) ->
          (* [check_expected_effect] labels a definition's *whole* guard with
             "Could not prove post-condition", so it says nothing about the
             individual goal.  Keep it only as a position, and report whatever
             more specific message is in scope. *)
          let msg = match msg with
                    | [d] when Errors.Msg.renderdoc d = "Could not prove post-condition" -> default_msg
                    | _ -> msg
          in
          aux env msg (Some r) phi

        | None ->
        match destruct_transparent q with
        | Some phi -> aux env default_msg ropt phi

        | None ->
        match destruct_typ_as_formula q with
        | Some (BaseConn (lid, [])) when lid_equals lid Const.true_lid ->
          GTrivial, [], true

        | Some (BaseConn (lid, [_; _])) when lid_equals lid Const.and_lid ->
          (* To prove [c1 /\ ... /\ cn] we prove each [ci] under the assumption
             of the preceding conjuncts.  This is sound, and it is what keeps
             the terms occurring in the earlier conjuncts available to the
             solver -- in a single monolithic query they were all in scope. *)
          let rec seq (cs:list S.term) : ML (goal_tree & decls_t & bool) =
            match cs with
            | [] -> GTrivial, [], true
            | [c] -> aux env default_msg ropt c
            | c::cs ->
              let t, decls, ok = aux env default_msg ropt c in
              let rest, decls', ok' = seq cs in
              let rest, decls'' =
                if ok && not (GTrivial? rest)
                then let e, decls'' = encode_formula c env in
                     if quantifier_free e
                     then gctx [hyp e] [CHyp c] rest, decls''
                     else rest, decls''
                else rest, []
              in
              gbranch [t; rest], decls@decls'@decls'', ok && ok'
          in
          seq (collect_conjuncts q)

        | Some (BaseConn (lid, [(lhs, _); (rhs, _)])) when lid_equals lid Const.imp_lid ->
          let t, decls, ok = aux env default_msg ropt rhs in
          (match t with
           | GTrivial -> GTrivial, decls, ok
           | _ ->
             let l, decls' = encode_formula lhs env in
             gctx [hyp l] [CHyp lhs] t, decls@decls', ok)

        | Some (BaseConn (lid, [(g, _); (th, _); (el, _)])) when lid_equals lid Const.ite_lid ->
          let t1, decls1, ok1 = aux env default_msg ropt th in
          let t2, decls2, ok2 = aux env default_msg ropt el in
          (match t1, t2 with
           | GTrivial, GTrivial -> GTrivial, decls1@decls2, ok1 && ok2
           | _ ->
             let ge, decls3 = encode_formula g env in
             gbranch [ gctx [hyp ge]          [CHyp g]             t1;
                       gctx [hyp (mkNot ge)]  [CHyp (U.mk_neg g)]  t2 ],
             decls1@decls2@decls3, ok1 && ok2)

        | Some (QAll (bs, _pats, body)) ->
          (* Skolemize: each bound variable becomes a fresh constant, declared
             and given its typing hypothesis.  Note the constants are FreeV,
             which prints exactly like a constant but keeps the hash-consed
             encodings of refinements parameterized over them.
             A variable of unit refinement type needs no constant at all: it
             is bound to the unit constant, and only its refinement is kept
             as a hypothesis. *)
          let vars, guards, env', decls, names =
            bs |> List.fold_left (fun (vars, guards, env, decls, names) b ->
              let x = (b <: S.binder).binder_bv in
              let t = norm env x.sort in
              match unit_refinements env t with
              | Some fs ->
                let env' = push_term_var env x mk_Term_unit in
                let g, decls' = encode_unit_refinements env fs in
                vars, g::guards, env', decls@decls', x::names
              | None ->
                let fv = mk_fv (fresh_name "@sk_", Term_sort) in
                let env' = push_term_var env x (mkFreeV fv) in
                let g, decls' = encode_term_pred_inline_refinements None t env (mkFreeV fv) in
                fv::vars, g::guards, env', decls@decls', x::names)
              ([], [], env, [], [])
          in
          let vars, guards, names = List.rev vars, List.rev guards, List.rev names in
          let t, decls', ok = aux env' default_msg ropt body in
          let ds = (vars |> List.map (fun fv -> DeclFun (fv_name fv) [] (fv_sort fv) None))
                 @ (guards |> List.filter (function App TrueOp [] _ -> false | _ -> true) |> List.map hyp) in
          gctx ds (names |> List.map CVar) t, decls@decls', ok

        | _ ->
        match (SS.compress q).n with
        | S.Tm_match {scrutinee=e; brs} ->
          (* Mirror [EncodeTerm.encode_match]: bind the scrutinee to a fresh
             constant, and prove each branch under its pattern guard.  The
             default case is unreachable and is not proved, which is why we
             return [false]. *)
          let scrsym = fresh_name "@sk_" in
          let scr' = mkFreeV (mk_fv (scrsym, Term_sort)) in
          let scr, decls0 = encode_term e env in
          let env' = env in
          let rec go (negs:list term) (brs:list S.branch) : ML (goal_tree & decls_t & bool) =
            match brs with
            | [] -> GTrivial, [], false
            | b::brs ->
              let guard, p, br, envb, declsb = encode_branch_pattern env' scr' b in
              let t, declst, ok = aux envb default_msg ropt br in
              let rest, declsr, ok' = go (mkNot guard :: negs) brs in
              gbranch [ gctx [hyp (mk_and_l (List.rev (guard :: negs)))] [CMatch e p] t; rest ],
              declsb@declst@declsr, ok && ok'
          in
          let t, decls, ok = go [] brs in
          gctx [ DeclFun scrsym [] Term_sort None; hyp (mkEq (scr', scr)) ] [] t,
          decls0@decls, ok

        | S.Tm_let {lbs=(false, [{lbname=Inl x; lbtyp=t1; lbdef=e1}]); body=e2} ->
          (* Mirror [EncodeTerm.encode_let]. *)
          let ee1, decls1 = encode_term (U.ascribe e1 (Inl t1, None, false)) env in
          let xs, e2 = SS.open_term [S.mk_binder x] e2 in
          let x = (List.hd xs).binder_bv in
          let env' = push_term_var env x ee1 in
          let t, decls2, ok = aux env' default_msg ropt e2 in
          gctx [] [CDef x e1] t, decls1@decls2, ok

        | S.Tm_meta {tm} ->
          aux env default_msg ropt tm

        (* Everything else is an atomic goal: existentials, disjunctions,
           equalities, applications of uninterpreted predicates, ... *)
        | _ ->
          let t, decls = mk_leaf env default_msg ropt q in
          t, decls, true
    in
    let t, decls, _ = aux env (Errors.mkmsg "Assertion failed") None q in
    t, decls
