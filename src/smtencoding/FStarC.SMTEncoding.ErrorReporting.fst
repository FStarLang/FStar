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
open FStarC.Syntax.Print {}

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

(* Ground typing facts.

   The result refinement of a pure application [f a1 .. an] is known to the
   solver only through [f]'s typing axiom: it has to instantiate the axiom,
   prove the typing hypotheses of the arguments -- including their refinements,
   i.e. [f]'s preconditions -- and then unfold the result type's refinement.
   For [eval (slice s k n) : nat] under nonlinear arithmetic that chain is
   often not found (issue #4591).

   Instead we state the result type of each such application directly, as a
   hypothesis next to the formula it occurs in: at the left-hand side of an
   implication, at an [if] guard, and before a goal.  The application is well
   typed at that position (that is what the typechecker established), so the
   fact holds there -- provided we do not look under a binder or a guard, see
   [is_guarding_connective].

   [typing_facts] is controlled by [--ext typing_facts=<mode>]: [off],
   [hastype] (default; assert [HasType e t]), or [refinement] (assert the
   refinement formulas of [t] about [e]). *)
let typing_facts_mode () : ML string =
  match Options.Ext.get "typing_facts" with
  | "" -> "hastype"
  | m -> m

let app_result_type (env:env_t) (t:S.term) : ML (option S.typ) =
  let hd, args = U.head_and_args_full t in
  if Nil? args then None else
  let fv_us =
    match (SS.compress hd).n with
    | S.Tm_fvar fv -> Some (fv, [])
    | S.Tm_uinst (hd, us) ->
      (match (SS.compress hd).n with
       | S.Tm_fvar fv -> Some (fv, us)
       | _ -> None)
    | _ -> None
  in
  match fv_us with
  | None -> None
  | Some (fv, us) ->
    let lid = S.lid_of_fv fv in
    if TypeChecker.Env.is_datacon env.tcenv lid then None else
    match TypeChecker.Env.try_lookup_lid env.tcenv lid with
    | None -> None
    | Some ((uvs, ty), _) ->
      if List.length uvs <> List.length us then None else
      let ty =
        if Nil? us then Some ty
        else Option.map fst (TypeChecker.Env.try_lookup_and_inst_lid env.tcenv us lid) in
      match ty with
      | None -> None
      | Some ty ->
      (* Locally nameless, so as not to draw fresh names: argument [i] of [n]
         is the bound variable with index [n - 1 - i] in [c]. *)
      let bs, c = U.arrow_formals_comp_ln ty in
      let n = List.length bs in
      if n <> List.length args
         || not (U.is_tot_or_gtot_comp c)
      then None
      else
        let subst = List.mapi (fun i (a, _) -> S.DT (n - 1 - i, a)) args in
        Some (SS.subst subst (U.comp_result c))

(* The conjuncts of the refinements of [ty], as formulas about [e]. *)
let rec refinement_conjuncts (env:env_t) (e:S.term) (ty:S.typ) (fuel:int) : ML (list S.term) =
  if fuel <= 0 then [] else
  let ty = TypeChecker.Normalize.unfold_whnf env.tcenv ty in
  match (SS.compress ty).n with
  | S.Tm_refine {b=x; phi} ->
    let xs, phi = SS.open_term [S.mk_binder x] phi in
    let x = (List.hd xs).binder_bv in
    let phi = SS.subst [S.NT (x, e)] phi in
    phi :: refinement_conjuncts env e x.sort (fuel - 1)
  | _ -> []

(* Like [Cons? (refinement_conjuncts env e ty 1)], without opening the
   refinement: that would draw fresh names, and change the output of F*. *)
let is_refined (env:env_t) (ty:S.typ) : ML bool =
  S.Tm_refine? (SS.compress (TypeChecker.Normalize.unfold_whnf env.tcenv ty)).n

let dbg_TypingFacts = Debug.get_toggle "TypingFacts"

(* The typechecker checks the later operands of these connectives assuming the
   earlier ones (see [TcUtil.short_circuit]), so an application in them is
   only well typed under that guard, and a fact about it must not be stated
   outside of it.  E.g. from [x >= 0 ==> p (g x)] with [g : x:int{x >= 0} -> r:nat{r <= x}]
   we must not conclude [g x <= x], hence [x >= 0].  In a position known to
   hold (a hypothesis), both operands of a conjunction hold, so it is no
   guard there. *)
let head_is (hd:S.term) (ls:list lident) : ML bool =
  match (U.un_uinst hd).n with
  | S.Tm_fvar fv -> List.existsb (S.fv_eq_lid fv) ls
  | _ -> false

let is_guarding_connective (holds:bool) (hd:S.term) : ML bool =
  head_is hd [Const.or_lid; Const.op_Or; Const.imp_lid; Const.ite_lid]
  || (not holds && head_is hd [Const.and_lid; Const.op_And])

(* Whether the arguments of a formula known to hold are known to hold. *)
let preserves_truth (hd:S.term) : ML bool =
  head_is hd [Const.and_lid; Const.op_And; Const.b2t_lid]

(* The implicit arguments and the first explicit one. *)
let rec unguarded_args (args:S.args) : S.args =
  match args with
  | [] -> []
  | (a, aq) :: rest ->
    if S.is_aqual_implicit aq then (a, aq) :: unguarded_args rest else [(a, aq)]

(* [Some e] for a formula [x == e] or [e == x] known to hold, where [x] is a
   variable whose type is the type we would state for [e].  This is how
   [let x = e] reaches us, and [x]'s typing then already says it about [e]. *)
let defines_name (env:env_t) (holds:bool) (hd:S.term) (args:S.args) : ML (option S.term) =
  if not holds || not (head_is hd [Const.eq2_lid]) then None else
  let names (x:S.term) (e:S.term) : ML bool =
    match (SS.compress (U.unmeta x)).n with
    | S.Tm_name x ->
      (match app_result_type env e with
       | Some ty ->
         let ty = TypeChecker.Normalize.normalize [TypeChecker.Env.Beta] env.tcenv ty in
         U.term_eq x.sort ty
       | None -> false)
    | _ -> false
  in
  match List.filter (fun (_, aq) -> not (S.is_aqual_implicit aq)) args with
  | [(a, _); (b, _)] ->
    if names a b then Some b
    else if names b a then Some a
    else None
  | _ -> None

(* The applications in [q] at which we state a typing fact: those not under a
   binder (a lambda, a refinement, a [let], a [match]) nor under a guard, with
   a top-level head, whose result type is refined.  [hyp] says whether [q] is
   known to hold. *)
let typed_applications (env:env_t) (stated:list S.term) (hyp:bool) (q:S.term)
  : ML (list (S.term & S.typ)) =
  let acc : ref (list (S.term & S.typ)) = mk_ref [] in
  let seen (t:S.term) : ML bool =
    List.existsb (fun (t', _) -> U.term_eq t t') !acc
    || List.existsb (fun t' -> U.term_eq t t') stated in
  (* [self]: whether to consider [t] itself, besides its subterms. *)
  let rec visit (holds:bool) (self:bool) (t:S.term) : ML unit =
    let t = SS.compress t in
    match t.n with
    | S.Tm_meta {tm} -> visit holds self tm
    | S.Tm_ascribed {tm} -> visit holds self tm
    | S.Tm_app _ ->
      let hd, args = U.head_and_args_full t in
      (match defines_name env holds hd args with
       | Some e ->
         (* As in A-normal form, [e] is typed through [x]. *)
         visit false false e
       | None ->
         let args = if is_guarding_connective holds hd then unguarded_args args else args in
         let holds = holds && preserves_truth hd in
         List.iter (fun (a, _) -> visit holds true a) args;
         if self && not (seen t) then
           (match app_result_type env t with
            | Some ty when is_refined env ty ->
              acc := (t, ty) :: !acc
            | _ -> ()))
    | _ -> ()
  in
  if typing_facts_mode () = "off" then []
  else (visit hyp true q; List.rev !acc)

(* The facts, their auxiliary declarations, and the applications they are
   about, which the caller adds to [stated] for the scope of the facts. *)
let typing_facts (env:env_t) (stated:list S.term) (hyp:bool) (q:S.term)
  : ML (list term & decls_t & list S.term) =
  let mode = typing_facts_mode () in
  let apps = typed_applications env stated hyp q in
  if !dbg_TypingFacts && Cons? apps then
    Format.print1 "Typing facts: %s\n" (show (List.map (fun (e, ty) -> show e ^ " : " ^ show ty) apps));
  let facts, decls = apps |> List.fold_left (fun (facts, decls) (e, ty) ->
    if mode = "refinement" then
      let phis = refinement_conjuncts env e ty 8 in
      let fs, ds = phis |> List.fold_left (fun (fs, ds) phi ->
        let f, d = encode_formula phi env in f::fs, ds@d) ([], []) in
      facts @ List.rev fs, decls @ ds
    else
      let ee, d1 = encode_term e env in
      let f, d2 = encode_term_pred None ty env ee in
      facts @ [f], decls @ d1 @ d2) ([], []) in
  facts, decls, List.map fst apps

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
    (* The applications whose typing facts are in scope. *)
    let stated : ref (list S.term) = mk_ref [] in
    let with_stated (ts:list S.term) (f:unit -> ML 'a) : ML 'a =
      let saved = !stated in
      stated := ts @ saved;
      let r = f () in
      stated := saved;
      r
    in
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
          let fs, decls', _ =
            if Options.Ext.get "typing_facts_leaves" = "off" then [], [], []
            else typing_facts env !stated false q in
          gctx (List.map hyp fs) []
            (GLeaf { goal_id = !ctr; goal_msg = msg; goal_range = rng;
                     goal_term = t; goal_source = q }),
          decls @ decls'
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
          let fs, decls'', ts = typing_facts env !stated true lhs in
          let t, decls, ok = with_stated ts (fun () -> aux env default_msg ropt rhs) in
          (match t with
           | GTrivial -> GTrivial, decls, ok
           | _ ->
             let l, decls' = encode_formula lhs env in
             gctx (hyp l :: List.map hyp fs) [CHyp lhs] t, decls@decls'@decls'', ok)

        | Some (BaseConn (lid, [(g, _); (th, _); (el, _)])) when lid_equals lid Const.ite_lid ->
          let fs, decls4, ts = typing_facts env !stated false g in
          let t1, decls1, ok1 = with_stated ts (fun () -> aux env default_msg ropt th) in
          let t2, decls2, ok2 = with_stated ts (fun () -> aux env default_msg ropt el) in
          (match t1, t2 with
           | GTrivial, GTrivial -> GTrivial, decls1@decls2, ok1 && ok2
           | _ ->
             let ge, decls3 = encode_formula g env in
             let fs = List.map hyp fs in
             gbranch [ gctx (hyp ge :: fs)          [CHyp g]             t1;
                       gctx (hyp (mkNot ge) :: fs)  [CHyp (U.mk_neg g)]  t2 ],
             decls1@decls2@decls3@decls4, ok1 && ok2)

        | Some (QAll (bs, _pats, body)) ->
          (* Skolemize: each bound variable becomes a fresh constant, declared
             and given its typing hypothesis.  Note the constants are FreeV,
             which prints exactly like a constant but keeps the hash-consed
             encodings of refinements parameterized over them. *)
          let vars, guards, env', decls, names =
            bs |> List.fold_left (fun (vars, guards, env, decls, names) b ->
              let x = (b <: S.binder).binder_bv in
              let fv = mk_fv (fresh_name "@sk_", Term_sort) in
              let env' = push_term_var env x (mkFreeV fv) in
              let g, decls' = encode_term_pred None (norm env x.sort) env (mkFreeV fv) in
              fv::vars, g::guards, env', decls@decls', x::names)
              ([], [], env, [], [])
          in
          let vars, guards, names = List.rev vars, List.rev guards, List.rev names in
          let t, decls', ok = aux env' default_msg ropt body in
          let ds = (vars |> List.map (fun fv -> DeclFun (fv_name fv) [] (fv_sort fv) None))
                 @ (guards |> List.filter (function App TrueOp [] _ -> false | _ -> true) |> List.map hyp) in
          gctx ds (names |> List.map (fun (x:S.bv) ->
                     (* A precondition is a [squash]-typed binder.  Report it as
                        the hypothesis it stands for rather than as a variable of
                        an uninformative type. *)
                     match U.un_squash x.sort with
                     | Some p -> CHyp p
                     | None -> CVar x)) t, decls@decls', ok

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
