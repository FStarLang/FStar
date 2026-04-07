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

module PulseSyntaxExtension.Desugar
open FStarC
open FStarC.Effect
module Sugar = PulseSyntaxExtension.Sugar
module A = FStarC.Parser.AST
module D = FStarC.Syntax.DsEnv
module ToSyntax = FStarC.ToSyntax.ToSyntax
module S = FStarC.Syntax.Syntax
module L = FStarC.List
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module R = FStarC.Range

open Pulse.Syntax.Base
module PSP = Pulse.Syntax.Pure
module PSBuild = Pulse.Syntax.Builder
module PSN = Pulse.Syntax.Naming
module RT = FStar.Reflection.Typing

open FStarC.Class.Show
open FStarC.Class.HasRange
open FStarC.Class.Monad
open FStarC.Ident
open FStar.List.Tot
open PulseSyntaxExtension.Err
open PulseSyntaxExtension.Env

(* Helper functions replacing PulseSyntaxExtension.SyntaxWrapper *)
let ppname_of_id (i:ident) : ppname =
  mk_ppname (RT.seal_pp_name (Ident.string_of_id i)) (Ident.range_of_id i)

let sw_mk_binder (x:ident) (t:term) : binder =
  mk_binder_ppname t (ppname_of_id x)

let sw_mk_binder_with_attrs (x:ident) (t:term) (attrs:list term) : binder =
  Pulse.Syntax.Base.mk_binder_with_attrs t (ppname_of_id x) (FStar.Sealed.seal attrs)

let sw_mk_bv (i:index) (name:string) (r:FStarC.Range.range) : bv =
  { bv_index = i; bv_ppname = mk_ppname (RT.seal_pp_name name) r }

let sw_mk_fv (nm:lident) (r:FStarC.Range.range) : fv =
  { fv_name = Ident.path_of_lid nm; fv_range = r }

let as_qual (imp:bool) : option qualifier = if imp then Some Implicit else None
let tc_qual : option qualifier = Some TcArg
let meta_qual (t:term) : option qualifier = Some (Meta t)

let tm_emp (r:FStarC.Range.range) : term = PSP.pack_term_view PSP.Tm_Emp r
let tm_pure (p:term) (r:FStarC.Range.range) : term = PSP.pack_term_view (PSP.Tm_Pure p) r
let tm_unknown (r:FStarC.Range.range) : term = PSP.pack_term_view PSP.Tm_Unknown r
let tm_expr (t:S.term) (r:FStarC.Range.range) : term = PSP.wr t r

let sw_mk_st_comp (pre:term) (ret:binder) (post:term) : st_comp =
  { u = PSP.u_unknown; res = ret.binder_ty; pre; post }

let mk_comp (pre:term) (ret:binder) (post:term) : comp =
  C_ST (sw_mk_st_comp pre ret post)

let ghost_comp (opens:term) (pre:term) (ret:binder) (post:term) : comp =
  C_STGhost opens (sw_mk_st_comp pre ret post)

let atomic_comp (opens:term) (pre:term) (ret:binder) (post:term) : comp =
  C_STAtomic opens Observable (sw_mk_st_comp pre ret post)

let unobs_comp (opens:term) (pre:term) (ret:binder) (post:term) : comp =
  C_STAtomic opens Neutral (sw_mk_st_comp pre ret post)

let mk_tot (t:term) : comp = C_Tot t

let tm_return (t:term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_return PSP.tm_unknown false t) r)

let tm_ghost_return (t:term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_return PSP.tm_unknown false t) r)

let tm_abs (b:binder) (q:option qualifier) (c:option comp) (body:st_term) (r:FStarC.Range.range) : st_term =
  let asc = { annotated = c; elaborated = None } in
  PSBuild.(with_range (tm_abs b q asc body) r)

let tm_st (head:term) (args:list st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_st head args) r)

let tm_bind (x:binder) (e1:st_term) (e2:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_bind x e1 e2) r)

let tm_totbind (x:binder) (e1:term) (e2:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_totbind x e1 e2) r)

let tm_let_mut (x:binder) (v:option term) (k:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_with_local x v k) r)

let tm_let_mut_array (x:binder) (v:option term) (n:term) (k:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_with_local_array x v n k) r)

let tm_while (head:st_term) (invariant:slprop) (body:st_term) (loop_requires:term) (meas:list term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_while invariant head body loop_requires meas) r)

let tm_if (head:st_term) (returns_annot:option slprop) (then_ else_:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_if head then_ else_ returns_annot) r)

let tm_match (sc:st_term) (returns_:option slprop) (brs:list branch) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_match sc returns_ brs) r)

let tm_intro_exists (p:slprop) (witnesses:list term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_intro_exists p witnesses) r)

let tm_with_options (options:string) (body:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_pragma_with_options options body) r)

let tm_forward_jump_label (body:st_term) (lbl:ident) (post:comp) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_forward_jump_label body (ppname_of_id lbl) post) r)

let tm_goto (lbl:term) (arg:term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_goto lbl arg) r)

let tm_defer (handler_pre:term) (handler:st_term) (body:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_defer handler_pre handler body) r)

let tm_admit (r:FStarC.Range.range) : st_term =
  PSBuild.(with_range (tm_admit STT PSP.u_zero (PSP.pack_term_view PSP.Tm_Unknown r) None) r)

let tm_proof_hint_with_binders (ht:proof_hint_type) (binders:list binder) (s:st_term) (r:FStarC.Range.range) : st_term =
  PSBuild.with_range (Tm_ProofHintWithBinders { hint_type=ht; binders; t=s }) r

let mk_assert_hint_type = PSBuild.mk_assert_hint_type
let mk_unfold_hint_type = PSBuild.mk_unfold_hint_type
let mk_fold_hint_type = PSBuild.mk_fold_hint_type
let mk_rename_hint_type = PSBuild.mk_rename_hint_type
let mk_rewrite_hint_type = PSBuild.mk_rewrite_hint_type
let mk_wild_hint_type : proof_hint_type = WILD
let mk_show_proof_state_hint_type (r:FStarC.Range.range) : proof_hint_type = SHOW_PROOF_STATE r

let inspect_const (c:FStarC.Const.sconst) : constant =
  FStarC.Reflection.V2.Builtins.inspect_const c

let pat_var (s:string) (_r:FStarC.Range.range) : pattern = Pat_Var (RT.seal_pp_name s) S.tun
let pat_constant (c:constant) (_r:FStarC.Range.range) : pattern = Pat_Constant c
let pat_cons (hd:fv) (ps:list pattern) (_r:FStarC.Range.range) : pattern =
  Pat_Cons hd (L.map (fun v -> (v, false)) ps)

let mk_branch (p:pattern) (t:st_term) (norw:bool) : branch = PSBuild.mk_branch p t norw

let bvs_as_subst (vars:list var) : PSN.subst =
  L.fold_left
    (fun s b -> RT.ND b 0 :: PSN.shift_subst s)
    [] vars

let subst_st_term (s:PSN.subst) (t:st_term) : st_term = PSN.subst_st_term t s
let subst_proof_hint (s:PSN.subst) (h:proof_hint_type) : proof_hint_type = PSN.subst_proof_hint h s

let fn_defn rng id isrec us bs comp meas body : decl =
  PSBuild.mk_decl (PSBuild.mk_fn_defn id isrec us bs comp meas body) rng
let fn_decl rng id us bs comp : decl =
  PSBuild.mk_decl (PSBuild.mk_fn_decl id us bs comp) rng
let slprop_defn rng id bs body : decl =
  PSBuild.mk_decl (PSBuild.mk_slprop_defn id bs body) rng

assume val print_exn (e:exn) : string

let close_st_term_bvs (e:st_term) (xs:list bv) : ML st_term = 
  PSN.close_st_term_n e (L.map (fun (b:bv) -> b.bv_index) xs)

let close_comp_bvs  (e:comp) (xs:list bv) : ML comp = 
  PSN.close_comp_n e (L.map (fun (b:bv) -> b.bv_index) xs)


let rec fold_right1 (f : 'a -> 'a -> ML 'a) (l : list 'a) : ML 'a =
  match l with
  | [h] -> h
  | h::t -> f h (fold_right1 f t)

let sugar_app (r:Range.range) (f:A.term) (aa : list A.term) : ML A.term =
  L.fold_left  (fun f a ->
    A.mk_term (A.App (f, a, A.Nothing)) r A.Expr)
  f aa

let sugar_var (i: lid) (r:Range.range) : ML A.term =
  A.mk_term (A.Var i) r A.Expr
let sugar_unit (r:Range.range) : ML A.term =
  A.mk_term (A.Var FStarC.Parser.Const.unit_lid) r A.Expr
let sugar_unit_const (r:Range.range) : ML A.term =
  A.mk_term (A.Const FStarC.Const.Const_unit) r A.Expr
let sugar_emp (r:Range.range) : ML A.term =
  A.mk_term (A.Var emp_lid) r A.Expr
let sugar_star (r:Range.range) : ML A.term =
  A.mk_term (A.Var star_lid) r A.Expr

let sugar_star_of_list (r:Range.range) (ts : list A.term) : ML A.term =
  match ts with
  | [] -> sugar_emp r
  | ts -> fold_right1 (fun a b -> sugar_app r (sugar_star r) [a; b]) ts

let parse_annots (r:Range.range) (cs : list Sugar.computation_annot) : ML (err Sugar.parsed_annots) =
  let open PulseSyntaxExtension.Sugar in
  let pres = filter (fun (a, _) -> Preserves ? a) cs in
  let reqs  = filter (fun (a, _) -> Requires? a) cs in
  let enss  = filter (fun (a, _) -> Ensures?  a) cs in
  let rets  = filter (fun (a, _) -> Returns?  a) cs in
  let opens = filter (fun (a, _) -> Opens?    a) cs in

  // let reqs  = choose (function (Sugar.Requires t, _) -> Some t | _ -> None) cs in
  // let enss  = choose (function (Sugar.Ensures  t, _) -> Some t | _ -> None) cs in
  // let rets  = choose (function (Sugar.Returns  t, _) -> Some t | _ -> None) cs in
  // let opens = choose (function (Sugar.Opens    t, _) -> Some t | _ -> None) cs in
  let req = pres @ reqs |> List.map (function (Requires t, _) | (Preserves t, _) -> t) |> sugar_star_of_list r in
  let ens = pres @ enss |> List.map (function (Ensures  t, _) | (Preserves t, _) -> t) |> sugar_star_of_list r in
  let! return_name, return_type =
    match rets with
    | [] -> return (None, sugar_unit r)
    | (Returns (name, t), _)::[] -> return (name, t)
    | _::(_,r)::_ ->
      fail "Multiple returns are not allowed." r
  in
  let return_name =
    match return_name with
    | None -> Ident.mk_ident ("_", r)
    | Some id -> id
  in
  let! opens : option A.term =
    match opens with
    | [] -> return None
    | (Opens t, _)::[] -> return (Some t)
    | _::(_,r)::_ ->
      fail "Multiple opens are not allowed." r
  in
  let rec check_order cs ((*have we seen a: *)req ret ens : bool) =
    match cs with
    | [] -> return ()
    | (a, r)::cs ->
      let req = req || Requires? a in
      let ret = ret || Returns? a in
      let ens = ens || Ensures? a in
      if ens && Requires? a then
        fail "requires must come before any ensures" r
      else if ret && Requires? a then
        fail "requires must come before the return" r
      else if ret && Opens? a then
        fail "opens must come before the return (the name returned is *not* in scope for the opens clause)" r
      else if ens && Returns? a then
        fail "returns must come before ensures (the name returned is in scope for the ensures clause)" r
      else if ret && Preserves? a then
        fail "preserves must come before the return" r
      else if ens && Preserves? a then
        fail "preserves must come before ensures" r
      else
        check_order cs req ret ens
  in
  check_order cs false false false;!
  return {
    precondition =  req;
    postcondition = ens;
    return_name = return_name;
    return_type = return_type;
    opens = opens;
  }

let as_term (t:S.term)
  : term
  = match t.n with
    | S.Tm_unknown ->
      tm_unknown t.pos
    | _ -> 
      tm_expr t t.pos

let desugar_const (c:FStarC.Const.sconst) : constant =
  inspect_const c

let comp_to_ast_term (c:Sugar.computation_type) : ML (err A.term) =
  let open Sugar in
  let open FStarC.Parser.AST in
  let! annots = parse_annots c.range c.annots in
  let return_ty = annots.return_type in
  let r = c.range in
  let head =
    match c.tag with
    | Sugar.ST ->
      let h = mk_term (Var stt_lid) r Expr in
      let h = mk_term (App (h, return_ty, Nothing)) r Expr in
      h
    | Sugar.STAtomic ->
      (* hack for now *)
      let is = mk_term (Var (Ident.lid_of_str "Pulse.Lib.Core.emp_inames")) r Expr in
      let h = mk_term (Var stt_atomic_lid) r Expr in
      let h = mk_term (App (h, return_ty, Nothing)) r Expr in
      mk_term (App (h, is, Nothing)) r Expr
    | Sugar.STUnobservable ->
      (* hack for now *)
      let is = mk_term (Var (Ident.lid_of_str "Pulse.Lib.Core.emp_inames")) r Expr in
      let h = mk_term (Var stt_atomic_lid) r Expr in
      let h = mk_term (App (h, mk_term (Var neutral_lid) r Expr, Hash)) r Expr in
      let h = mk_term (App (h, return_ty, Nothing)) r Expr in
      mk_term (App (h, is, Nothing)) r Expr
   | Sugar.STGhost ->
      (* hack for now *)
      let h = mk_term (Var stt_ghost_lid) r Expr in
      let h = mk_term (App (h, return_ty, Nothing)) r Expr in
      h
  in
  let pre  = annots.precondition in
  let post = annots.postcondition in
  let post =
    let pat = mk_pattern (PatVar (annots.return_name, None, [])) r in
    let pat = mk_pattern (PatAscribed (pat, (return_ty, None))) r in
    mk_term (Abs ([pat], post)) r Expr
  in
  let t = mk_term (App (head, pre, Nothing)) r Expr in
  let t = mk_term (App (t, post, Nothing)) r Expr in
  return t


let faux (qb : option qualifier & binder) (bv : S.bv)
  : ML (option qualifier & binder & Pulse.Syntax.Base.bv)
   =
    let (q,b) = qb in
    let bv = sw_mk_bv bv.S.index
                      (Ident.string_of_id bv.S.ppname)
                      bv.S.sort.pos
    in
    (q,b,bv)

let app_lid lid (args:list S.term) (r:_)
  : ML S.term
  = let head_fv = S.lid_as_fv lid None in
    let head = S.fv_to_tm head_fv in
    let app = 
      L.fold_left 
        (fun head (arg:S.term) ->
          S.mk_Tm_app head [(arg, None)] arg.pos)
        head args
    in
    app


let ret (s:S.term) = tm_return (as_term s) s.pos

type admit_or_return_t =
  | AdmitOrReturn_STTerm : st_term -> admit_or_return_t
  | AdmitOrReturn_Return : S.term -> admit_or_return_t

let st_term_of_admit_or_return (t:admit_or_return_t) : st_term =
  match t with
  | AdmitOrReturn_STTerm t -> t
  | AdmitOrReturn_Return t -> ret t

let admit_or_return (env:env_t) (s:S.term)
  : ML admit_or_return_t
  = let r = s.pos in
    let head, args = U.head_and_args_full s in
    match head.n, args with
    | S.Tm_fvar fv, [_] -> (
      if S.fv_eq_lid fv admit_lid
      then AdmitOrReturn_STTerm (tm_admit r)
      else AdmitOrReturn_Return s
    )
    | _ -> AdmitOrReturn_Return s

let prepend_ctx_issue (c : Pprint.document) (i : Errors.issue) : Errors.issue =
  { i with issue_msg = c :: i.issue_msg }


let tosyntax' (env:env_t) (t:A.term)
  : ML (err S.term)
  = try 
      return (ToSyntax.desugar_term env.dsenv t)
    with 
      | e -> 
        match FStarC.Errors.issue_of_exn e with
        | Some i ->
          FStarC.Errors.add_issues [i];
          just_fail ()

        | None -> 
          fail (Format.fmt2 "Failed to desugar Pulse term %s\nUnexpected exception: %s\n"
                             (A.term_to_string t)
                             (print_exn e))
                t.range

let tosyntax (env:env_t) (t:A.term)
  : ML (err S.term)
  = let! s = tosyntax' env t in
    return s

let desugar_term (env:env_t) (t:A.term)
  : ML (err term) 
  = let! s = tosyntax env t in
    return (as_term s)
  
let desugar_term_opt (env:env_t) (t:option A.term)
  : ML (err term)
  = match t with
    | None -> return (tm_unknown FStarC.Range.dummyRange)
    | Some e -> desugar_term env e

//
// Only add undeclared tick names (e.g. 'x) as binders,
//   and with erased types
//
// Undeclared unticked names are errors
//
let idents_as_binders (env:env_t) (l:list ident)
  : ML (err (env_t & list (option qualifier & binder) & list S.bv))
  =   let erased_tm = A.(mk_term (Var FStarC.Parser.Const.erased_lid) FStarC.Range.dummyRange Un) in
      let mk_ty i =
        let wild = A.(mk_term Wild (Ident.range_of_id i) Un) in
        A.(mkApp erased_tm [wild, A.Nothing] (Ident.range_of_id i)) in
      let rec aux env binders bvs l 
        : ML (err (env_t & list (option qualifier & binder) & list S.bv))
        = match l with
          | [] -> return (env, L.rev binders, L.rev bvs)
          | i::l ->
            let env, bv = push_bv env i in
            let qual = as_qual true in      
            let ty = mk_ty i in
            let! ty = desugar_term env ty in
            aux env ((qual, sw_mk_binder i ty)::binders) (bv::bvs) l
      in
      aux env [] [] l

let desugar_slprop (env:env_t) (v:Sugar.slprop)
  : ML (err slprop)
  = tosyntax env v

let desugar_slprop_annot (env:env_t) (v:Sugar.slprop) (lit:bool)
  : ML (err slprop)
  = let! p = tosyntax env v in
    if lit then
      return <| U.mk_app (S.tconst (FStarC.Parser.Const.p2l ["Pulse"; "Lib"; "Core"; "literally"]))
        [p, None]
    else
      return p

let desugar_computation_type (env:env_t) (c:Sugar.computation_type)
  : ML (err comp)
  = //let! pres = map_err (desugar_slprop env) c.preconditions in
    //let pre = fold_right1 (fun a b -> tm_star a b c.range) pres in
    let! annots = parse_annots c.range c.annots in
    let! pre = desugar_slprop_annot env annots.Sugar.precondition c.literally in

    let! ret = desugar_term env annots.Sugar.return_type in

    let! opens =
      match annots.Sugar.opens with
      | Some t -> desugar_term env t
      | None -> return PSP.tm_emp_inames
    in

    (* Should have return_name in scope I think *)
    // let! openss = map_err (desugar_term env) c.opens in
    // let opens = L.fold_right (fun i is -> tm_add_inv i is c.range) openss PSP.tm_emp_inames in

    let env1, bv = push_bv env annots.Sugar.return_name in
    // let! posts = map_err (desugar_slprop env1) c.postconditions in
    // let post = fold_right1 (fun a b -> tm_star a b c.range) posts in
    let! post = desugar_slprop_annot env1 annots.Sugar.postcondition c.literally in
    let post = PSN.close_term post bv.index in

    match c.tag with
    | Sugar.ST ->
      if Some? annots.Sugar.opens then
        fail "STT computations are not indexed by invariants. Either remove the `opens` or make this function ghost/atomic."
             (Some?.v annots.Sugar.opens).range
      else return ();!
      return (mk_comp pre (sw_mk_binder annots.Sugar.return_name ret) post)
    | Sugar.STAtomic ->
      return (atomic_comp opens pre (sw_mk_binder annots.Sugar.return_name ret) post)
    | Sugar.STUnobservable ->
      return (unobs_comp opens pre (sw_mk_binder annots.Sugar.return_name ret) post)
    | Sugar.STGhost ->
      return (ghost_comp opens pre (sw_mk_binder annots.Sugar.return_name ret) post)

let mk_totbind b s1 s2 r : st_term =
  tm_totbind b s1 s2 r

let mk_bind b s1 s2 r : st_term = 
  tm_bind b s1 s2 r

let qual = option qualifier

(* We open FStar.Tactics.V2 in the scope of every `by` as a convenience. *)
let desugar_tac_opt (env:env_t) (topt : option A.term) : ML (err (option term)) =
  match topt with
  | None -> return None
  | Some t ->
    let tactics_module_lid = Ident.lid_of_str "FStar.Tactics.V2" in
    let env = push_namespace env tactics_module_lid in
    let! t = desugar_term env t in
    return (Some t)

let desugar_hint_type (env:env_t) (ht:Sugar.hint_type)
  : ML (err proof_hint_type)
  = let open Sugar in
    match ht with
    | ASSERT vp ->
      let! vp = desugar_slprop env vp in
      return (mk_assert_hint_type vp)
    | UNFOLD (ns, vp) -> 
      let! vp = desugar_slprop env vp in
      let! ns = resolve_names env ns in
      let ns = Option.map (L.map FStarC.Ident.string_of_lid) ns in
      return (mk_unfold_hint_type ns vp)
    | FOLD (ns, vp) -> 
      let! vp = desugar_slprop env vp in
      let! ns = resolve_names env ns in
      let ns = Option.map (L.map FStarC.Ident.string_of_lid) ns in
      return (mk_fold_hint_type ns vp)
    | RENAME (pairs, goal, tac_opt) ->
      let! pairs =
        pairs |>
        mapM 
          (fun (t1, t2) ->
            let! t1 = desugar_term env t1 in
            let! t2 = desugar_term env t2 in
            return (t1, t2))
      in
      let! goal = map_err_opt (desugar_slprop env) goal in
      let! tac_opt = desugar_tac_opt env tac_opt in
      return (mk_rename_hint_type pairs goal tac_opt)
    | REWRITE (t1, t2, tac_opt) ->
      let! t1 = desugar_slprop env t1 in
      let! t2 = desugar_slprop env t2 in
      let! tac_opt = desugar_tac_opt env tac_opt in
      return (mk_rewrite_hint_type t1 t2 tac_opt)
    | WILD ->
      return (mk_wild_hint_type)
    | SHOW_PROOF_STATE r ->
      return (mk_show_proof_state_hint_type r)

// FIXME
// should just mimic let resolve_lid
let desugar_datacon (env:env_t) (l:lid) : ML (err fv) =
  let rng = Ident.range_of_lid l in
  let t = A.mk_term (A.Name l) rng A.Expr in
  let! tt = tosyntax env t in
  let! sfv =
    match (SS.compress tt).n with
    | S.Tm_fvar fv -> return fv
    | S.Tm_uinst ({n = S.Tm_fvar fv}, _) -> return fv
    | _ -> fail (Format.fmt1 "Not a datacon? %s" (Ident.string_of_lid l)) rng
  in
  return (sw_mk_fv (S.lid_of_fv sfv) rng)

let mk_abs_with_comp qbs comp body range : ML _ =
  let _, abs =
    L.fold_right
      (fun (q,b,bv) (c, body) ->
        let body' = PSN.close_st_term body bv.bv_index in
        let asc =
          match c with
          | None -> None
          | Some c -> Some  (PSN.close_comp c bv.bv_index) in
        None, tm_abs b q asc body' range)
      qbs (comp, body)
  in
  abs

(* s has already been transformed with explicit dereferences for r-values *)
let rec desugar_stmt' (env:env_t) (s:Sugar.stmt)
  : ML (err st_term)
  = let open Sugar in
    match s.s with
    | Expr { e; args } -> 
      let! tm = tosyntax env e in
      if Nil? args then
        return (st_term_of_admit_or_return (admit_or_return env tm))
      else (
        let! args = desugar_st_args env args in
        return (tm_st tm args s.range)
      )

    | ArrayAssignment { arr; index; value } ->
      let! arr = tosyntax env arr in
      let! index = tosyntax env index in
      let! value = tosyntax env value in      
      let! array_assignment_lid = resolve_lid env (op_array_assignment_lid s.range) in
      let tm = (app_lid array_assignment_lid [arr; index; value] s.range) in
      return (st_term_of_admit_or_return (admit_or_return env tm))

    | Sequence { s1={s=Open l; range}; s2 } ->
      let! env = 
        try 
          let env = push_namespace env l in
          return env
        with
          | FStarC.Errors.Error(e, msg, r, ctx) ->
            fail (Format.fmt2
            "Failed to open namespace %s; \
            You may need to bind this namespace outside Pulse for the F* dependency scanner to pick it up, \
            e.g., write ``module _X = %s`` in F*"
            (Ident.string_of_lid l)
            (Ident.string_of_lid l)) range
      in
      desugar_stmt env s2

    | Sequence { s1={s=LetBinding lb; range=s1range}; s2 } ->
      begin match lb.pat.pat with
      | A.PatVar _
      | A.PatWild _ ->
        (* simple bind *)
        desugar_bind env lb s2 s.range
      | _ ->
        (* a single-branch pattern match *)
        let id = Ident.id_of_text "_letpattern" in
        let id = Ident.set_id_range lb.pat.prange id in
        let pat = lb.pat in
        if Some? lb.qualifier then
          fail "Qualifiers are not allowed for pattern bindings" lb.pat.prange
        else return ();!
        let! init_expr =
          match lb.init with
          | None -> fail "Pattern bindings must have an initializer" lb.pat.prange
          | Some (Default_initializer (Some e, [])) -> return e
          | Some _ -> fail "Pattern bindings cannot have complext initializers" lb.pat.prange
        in
        let lb' =
          { norw = lb.norw;
            qualifier = lb.qualifier;
            pat = A.mk_pattern (A.PatVar (id, None, [])) lb.pat.prange;
            typ = lb.typ;
            init = lb.init }
        in
        let t_let =
          { mk_stmt (LetBinding lb') s1range with source = false }
        in
        let seq s1 s2 =
          { mk_stmt (Sequence { s1; s2 }) s1range with source = false }
        in
        let t_match =
          {
          mk_stmt (Match { head = mk_stmt (Expr { e = A.(mk_term (Var (Ident.id_as_lid id)) lb.pat.prange Expr); args = [] }) s1range;
                          returns_annot = None;
                          branches = [(lb.norw, pat, s2)] }) s1range
                          with source = false }
        in
        let t_match =
          (* We only inject a variable when the rhs is a variable *)
          if not lb.norw &&
              (match init_expr.A.tm with
                | A.Var _ -> true
                | A.Name _ -> true
                | _ -> false)
          then
            let s_rw =
              mk_stmt (ProofHintWithBinders {
                    hint_type = RENAME ([(init_expr, A.mk_term (A.Var (Ident.id_as_lid id)) lb.pat.prange A.Expr)], None, None);
                    binders = []}) s1range
            in
            let s_rw = { s_rw with source=false } in
            seq s_rw t_match
          else t_match
        in
        let s'' =
          seq t_let t_match
        in
        // Format.print2 "GG Rewrote \n(%s)\n to \n(%s)\n\n" (show s) (show s'');
        desugar_stmt env s''
      end

    | ProofHintWithBinders _ ->
      desugar_proof_hint_with_binders env s None s.range

    | Sequence { s1; s2 } when ProofHintWithBinders? s1.s ->
      desugar_proof_hint_with_binders env s1 (Some s2) s1.range

    | Sequence { s1; s2 } when Defer? s1.s ->
      let Defer { handler_pre; defer_handler } = s1.s in
      let! cpre = desugar_slprop env handler_pre in
      let! handler = desugar_stmt env defer_handler in
      let! body = desugar_stmt env s2 in
      return (tm_defer cpre handler body s.range)

    | Sequence { s1; s2 } -> 
      desugar_sequence env s1 s2 s.range
      
    | Block { stmt } ->
      desugar_stmt env stmt

    | If { head; join_slprop; then_; else_opt } -> 
      let! head = desugar_stmt env head in
      let! join_slprop =
        match join_slprop with
        | None -> return None
        | Some (None, t, _opens) -> 
          let! vp = desugar_slprop env t in
          return (Some vp)
      in
      let! then_ = desugar_stmt env then_ in
      let! else_ = 
        match else_opt with
        | None -> 
          return (tm_return (tm_expr S.unit_const R.dummyRange) R.dummyRange)
        | Some e -> 
          desugar_stmt env e
      in
      return (tm_if head join_slprop then_ else_ s.range)

    | Match { head; returns_annot; branches } ->
      let! head = desugar_stmt env head in
      let! returns_annot = map_err_opt (fun (_, t, _opens) -> desugar_slprop env t) returns_annot in
      let! branches = branches |> mapM (desugar_branch env) in
      return (tm_match head returns_annot branches s.range)

    | While { guard; invariant=invs0; body } ->
      let! invs = invs0 |> mapM (function
                        | LoopInvariant i -> return [i]
                        | LoopEnsures _ -> return []
                        | LoopRequires _ -> return []
                        | Decreases _ -> return []) in
      let invs = L.concat invs in
      let inv = sugar_star_of_list s.range invs in
      let! guard = desugar_stmt env guard in
      let! inv = desugar_slprop env inv in
      let body = { body with s = ForwardJumpLabel { body; lbl = id_of_text "_continue"; post = None } } in
      let breaklbl = Ident.mk_ident ("_break", s.range) in
      let env', lblx = push_bv env breaklbl in
      let! body = desugar_stmt env' body in
      
      let loop_requires = invs0 |> L.concatMap (function | LoopRequires r -> [r] | _ -> []) in
      let! loop_requires = mapM (tosyntax env) loop_requires in
      let loop_requires =
        match loop_requires with
        | [] -> U.t_true
        | r::rs -> L.fold_left U.mk_conj r rs in

      let meas_list = invs0 |> L.concatMap (function | Decreases r -> [r] | _ -> []) in
      let! _ =
        if L.length meas_list > 1
        then fail "At most one decreases clause is allowed per while loop." s.range
        else return () in
      let! meas =
        match meas_list with
        | [{ A.tm = A.LexList ts }] -> mapM (tosyntax env) ts
        | _ -> mapM (tosyntax env) meas_list
      in

      let while = tm_while guard inv body loop_requires meas s.range in
      let while = PSN.close_st_term while lblx.index in

      let loop_ensures = invs0 |> L.concatMap (function | LoopEnsures r -> [r] | _ -> []) in
      let! loop_ensures = mapM (tosyntax env) loop_ensures in
      let loop_ensures =
        match loop_ensures with
        | [] -> tm_emp s.range
        | r::rs -> tm_pure (L.fold_left U.mk_disj r rs) s.range in
      let loop_ensures = mk_comp (tm_unknown s.range) (sw_mk_binder (id_of_text "_") (tm_unknown s.range)) loop_ensures in
      return (tm_forward_jump_label while breaklbl loop_ensures s.range)

    | Introduce { slprop; witnesses } -> (
      let! vp = desugar_slprop env slprop in
      let! witnesses = witnesses |> mapM (desugar_term env) in
      return (tm_intro_exists vp witnesses s.range)
    )

    | LetBinding _ -> 
      fail "Terminal let binding" s.range

    | PragmaSetOptions { options; body } ->
      FStarC.Syntax.Util.process_pragma (S.PushOptions <| Some options) s.range;
      let! body = desugar_stmt env body in
      FStarC.Syntax.Util.process_pragma S.PopOptions s.range;
      return (tm_with_options options body s.range)
    
    | ForwardJumpLabel { body; lbl; post } ->
      let env', lblx = push_bv env lbl in
      let! body = desugar_stmt env' body in
      let body = PSN.close_st_term body lblx.index in
      let! post =
        match post with
        | None -> return (tm_emp s.range)
        | Some (_, t, _opens) -> desugar_slprop env t
      in
      let post = mk_comp (tm_unknown s.range) (sw_mk_binder (id_of_text "_") (tm_unknown s.range)) post in
      return (tm_forward_jump_label body lbl post s.range)

    | Goto { lbl; arg } ->
      let! lbl = tosyntax env (sugar_var (id_as_lid lbl) s.range) in
      let arg = match arg with Some arg -> arg | None -> sugar_unit_const s.range in
      let! arg = tosyntax env arg in
      return (tm_goto lbl arg s.range)

    | Defer { handler_pre; defer_handler } ->
      fail "defer must be followed by a body (use defer pre { handler }; body)" s.range

    | Return { arg } ->
      desugar_stmt' env { s with s = Goto { lbl = id_of_text "_return"; arg } } 
    
    | Continue ->
      desugar_stmt' env { s with s = Goto { lbl = id_of_text "_continue"; arg = None } } 

    | Break ->
      desugar_stmt' env { s with s = Goto { lbl = id_of_text "_break"; arg = None } } 

and desugar_st_args (env:env_t) (args:list Sugar.lambda) : ML (err (list st_term)) =
  match args with
  | arg::args ->
    let! arg = desugar_lambda env arg in
    let! args = desugar_st_args env args in
    return (arg::args)
  | [] -> return []

and desugar_stmt (env:env_t) (s:Sugar.stmt) : ML (err st_term) =
  let! r = desugar_stmt' env s in
  if not s.source then
    return (PSBuild.mark_not_source r)
  else
    return r

and desugar_branch (env:env_t) (br: bool & A.pattern & Sugar.stmt)
  : ML (err branch)
  = let (norw, p, e) = br in
    let! (p, vs) = desugar_pat env p in
    let env, bvs = push_bvs env vs in
    let! e = desugar_stmt env e in
    let e = PSN.close_st_term_n e (L.map (fun (v:S.bv) -> v.index <: nat) bvs) in
    return (mk_branch p e norw)

and desugar_pat (env:env_t) (p:A.pattern)
  : ML (err (pattern & list ident))
  = let r = p.prange in
    match p.pat with
    | A.PatVar (id, _, _) ->
      return (pat_var (Ident.string_of_id id) r, [id])
    | A.PatWild _ ->
      let id = Ident.mk_ident ("_", r) in
      return (pat_var "_" r, [id])
    | A.PatConst c ->
      let c = desugar_const c in
      return (pat_constant c r, [])
    | A.PatName lid ->
      let! fv = desugar_datacon env lid in
      return (pat_cons fv [] r, [])
    | A.PatApp ({pat=A.PatName lid}, [{pat = A.PatRest}]) ->
      let A.PatApp (hd, _) = p.pat in
      let! fv = desugar_datacon env lid in
      let rest = ToSyntax.rest_pat_for_lid env.dsenv lid in
      let newpat = A.mk_pattern (A.PatApp (hd, rest)) r in
      desugar_pat env newpat

    | A.PatApp ({pat=A.PatName lid}, args) ->
      let! fv = desugar_datacon env lid in
      let! idents =
        args |>
        mapM (fun (p:A.pattern) ->
                match p.pat with
                | A.PatVar (id, _, _) -> return id
                | A.PatWild _ -> return (Ident.mk_ident ("_", r))
                | _ -> fail "invalid pattern: no deep patterns allowed" r)
      in
      let strs = L.map Ident.string_of_id idents in
      let pats = L.map (fun s -> pat_var s r) strs in
      return (pat_cons fv pats r, idents)

    | A.PatList ps ->
      let! ps = ps |> mapM (fun p -> desugar_pat env p) in
      let pats, idents = L.unzip ps in
      let cons = sw_mk_fv Parser.Const.cons_lid r in
      let nil  = sw_mk_fv Parser.Const.nil_lid r in
      let pat = FStarC.List.fold_right (fun p acc -> pat_cons cons [p;acc] r) pats (pat_cons nil [] r) in
      return (pat, L.flatten idents)

    | A.PatTuple (ps, dep) ->
      let! ps = ps |> mapM (fun p -> desugar_pat env p) in
      let pats, idents = L.unzip ps in
      let ctor = sw_mk_fv (Parser.Const.Tuples.mk_tuple_data_lid (L.length pats) r) r in
      let pat = pat_cons ctor pats r in
      return (pat, L.flatten idents)

    | A.PatRest ->
      fail "Invalid pattern: `..` can only appear applied to a constructor" r

    | _ ->
      fail "invalid pattern" r

and desugar_bind (env:env_t) (lb:_) (s2:Sugar.stmt) (r:R.range)
  : ML (err st_term)
  = let open Sugar in
    let! annot = desugar_term_opt env lb.typ in
    let id = 
      match lb.pat.pat with
      | A.PatWild _ -> Ident.mk_ident ("_", r)
      | A.PatVar (id, _, _) -> id
    in
    let b = sw_mk_binder id annot in
    let! s2 =
      let env, bv = push_bv env id in
      let! s2 = desugar_stmt env s2 in
      return (PSN.close_st_term s2 bv.index)
    in
    match lb.init with
    | None ->
      fail "Uninitialized variables are not yet handled" r

    | Some e1 -> (
      match lb.qualifier with
      | None -> ( //just a regular bind
        match e1 with
        | Sugar.Array_initializer _ ->
          fail "immutable local arrays are not yet supported" r
        | Sugar.Lambda_initializer {
            id; is_rec=false;
            binders;
            ascription=Inl c;
            measure=None;
            body=Inl stmt;
            range
          } ->
          let lam : lambda = {
              binders = binders;
              ascription = Some c;
              body = stmt;
              range
            }
          in
          let! lam = desugar_lambda env lam in
          return <| mk_bind b lam s2 r

        | Sugar.Lambda_initializer {
            id; is_rec=false;
            binders;
            ascription=Inr ascription;
            measure=None;
            body=Inr body;
            range
          } ->
          let! env, bs, bvs = desugar_binders env binders in
          let! comp =
            match ascription with
            | None -> return (mk_tot (tm_unknown range))
            | Some t -> let! t = desugar_term env t in return (mk_tot t)
          in
          let! body = desugar_lambda env body in
          let! qbs = map2 faux bs bvs in
          let abs = mk_abs_with_comp qbs (Some comp) body range in
          return <| mk_bind b abs s2 r

        | Sugar.Lambda_initializer _ ->
          fail "Nested functions are not yet fully supported" r

        | Default_initializer (Some e1, []) ->
          let! s1 = tosyntax env e1 in
          let t =
            match admit_or_return env s1 with
            | AdmitOrReturn_STTerm s1 ->
              mk_bind b s1 s2 r
            | AdmitOrReturn_Return s1 ->
              mk_totbind b (as_term s1) s2 r
          in
          return t

        | Default_initializer (Some e1, args) ->
          let! s1 = tosyntax env e1 in
          let! args = desugar_st_args env args in
          let t = mk_bind b (tm_st s1 args r) s2 r in
          return t

        | Stmt_initializer e ->
          let! s = desugar_stmt env e in
          return (mk_bind b s s2 r)
      )
      | Some MUT //these are handled the same for now
      | Some REF ->
        let b = sw_mk_binder id annot in
        match e1 with
        | Sugar.Array_initializer {init; len} ->
          let! init = 
            match init with
            | Some init ->
              let! init = desugar_term env init in
              return (Some init)
            | None -> return None in
          let! len = desugar_term env len in
          return (tm_let_mut_array b init len s2 r)
        | Sugar.Default_initializer (init, []) ->
          let! init = 
            match init with
            | Some init ->
              let! init = desugar_term env init in
              return (Some init)
            | None -> return None in
          return (tm_let_mut b init s2 r)
        | Sugar.Default_initializer (e1, args) ->
          fail "Lambda arguments not yet supported in let mut" r
    )

and desugar_sequence (env:env_t) (s1 s2:Sugar.stmt) r
  : ML (err st_term)
  = let semicolon = not (Sugar.LetBinding? s1.s) in
    let! s1 = desugar_stmt env s1 in
    let s1 =
      if semicolon
      then PSBuild.mark_statement_sequence s1
      else s1
    in
    let! s2 = desugar_stmt env s2 in
    let annot = sw_mk_binder (Ident.id_of_text "_") (tm_unknown r) in
    return (mk_bind annot s1 s2 r)

and desugar_proof_hint_with_binders (env:env_t) (s1:Sugar.stmt) (k:option Sugar.stmt) r
  : ML (err st_term)
  = match s1.s with
    | Sugar.ProofHintWithBinders { hint_type = Sugar.ASSUME p; binders=[] } ->
      let assume_fv = sw_mk_fv assume_lid r in
      let assume_ : term = PSP.tm_fvar assume_fv in
      let! p = desugar_slprop env p in
      let s1 = tm_st (S.mk_Tm_app assume_ [p, None] r) [] r in
      let! s2 =
        match k with
        | None -> return (tm_ghost_return (tm_expr S.unit_const r) r)
        | Some s2 -> desugar_stmt env s2 in
      let annot = sw_mk_binder (Ident.id_of_text "_") (tm_unknown r) in
      return (mk_bind annot s1 s2 r)

    | Sugar.ProofHintWithBinders { hint_type = Sugar.ASSUME _; binders=b1::_ } ->
      fail "'assume' cannot have binders" b1.brange

    | Sugar.ProofHintWithBinders { hint_type; binders=bs } -> //; slprop=v } ->
      let! env, binders, bvs = desugar_binders env bs in
      let vars = L.map #_ #nat (fun bv -> bv.S.index) bvs in
      let! ht = desugar_hint_type env hint_type in
      let! s2 = 
        match k with
        | None -> return (tm_ghost_return (tm_expr S.unit_const r) r)
        | Some s2 -> desugar_stmt env s2 in
      let binders = L.map snd binders in
      let sub = bvs_as_subst vars in
      let s2 = subst_st_term sub s2 in
      let ht = subst_proof_hint sub ht in
      return (tm_proof_hint_with_binders ht (PSN.close_binders binders vars) s2 r)
    | _ -> fail "Expected ProofHintWithBinders" s1.range

and desugar_binders (env:env_t) (bs:Sugar.binders)
  : ML (err (env_t & list (option qualifier & binder) & list S.bv))
  = let rec aux env bs 
      : ML (err (env_t & list (qual & ident & term & list term) & list S.bv))
      = match bs with
        | [] -> return (env, [], [])
        | b::bs -> 
          let rng = b.A.brange in
          let (aq, b, t, attrs) = destruct_binder b in
          let! t = desugar_term env t in
          let! attrs = mapM (desugar_term env) attrs in
          let env, bv = push_bv env b in
          let! env, bs, bvs = aux env bs in
          let! aq = as_qual env aq rng in
          return (env, (aq, b, t, attrs)::bs, bv::bvs)
    in
    let! env, bs, bvs = aux env bs in
    return (env, L.map (fun (aq, b, t, attrs) -> aq, sw_mk_binder_with_attrs b t attrs) bs, bvs)

and desugar_lambda (env:env_t) (l:Sugar.lambda)
  : ML (err st_term)
  = let { binders; ascription; body; range } = l in
    let! env, bs, bvs = desugar_binders env binders in
    let! env, bs, bvs, comp =
      match ascription with
      | None ->
        return (env, bs, bvs, None)
      | Some c -> 
        let! pannots = parse_annots c.range c.annots in
        let fvs = free_vars_comp env pannots in
        let! env, bs', bvs' = idents_as_binders env fvs in
        let bs = bs@bs' in
        let bvs = bvs@bvs' in
        let! comp = desugar_computation_type env c in
        return (env, bs, bvs, Some comp)
    in
    let body = { body with s = Sugar.ForwardJumpLabel { body; lbl = id_of_text "_return"; post = None } } in
    let! body = desugar_stmt env body in
    let! qbs = map2 faux bs bvs in
    let abs = mk_abs_with_comp qbs comp body range in
    return abs

and as_qual (env:env_t) (q:A.aqual) rng : ML (err qual) =
  match q with
  | Some A.Implicit -> return <| as_qual true
  | Some A.TypeClassArg -> return <| tc_qual
  | Some (A.Meta t) ->
    let! t = desugar_term env t in
    return <| meta_qual t
  | Some A.Equality ->
    fail "Pulse does not yet support equality arguments" rng
  | None -> return <| as_qual false


let desugar_decl (env:env_t) (d:Sugar.decl)
  : ML (err decl) =
  match d with
  // A normal definition with a statament body, recursive or not
  | Sugar.FnDefn { id; is_rec; us; binders; ascription=Inl ascription; measure; body=Inl body; range } ->
    let! env, bs, bvs = desugar_binders env binders in
    let! pannots = parse_annots ascription.range ascription.annots in
    let fvs = free_vars_comp env pannots in
    let! env, bs', bvs' = idents_as_binders env fvs in
    let bs = bs@bs' in
    let bvs = bvs@bvs' in
    let! comp = desugar_computation_type env ascription in
    let! meas = map_err_opt (desugar_term env) measure in
    (* Perhaps push the recursive binding. *)
    let! (env, bs, bvs) =
      if is_rec
      then
        let ty = tm_unknown FStarC.Range.dummyRange in
        let env, bv = push_bv env id in
        let b = sw_mk_binder id ty in
        return (env, bs@[(None, b)], bvs@[bv])
      else
        return (env, bs, bvs)
    in
    let body = { body with s = Sugar.ForwardJumpLabel { body; lbl = id_of_text "_return"; post = None } } in
    let! body = desugar_stmt env body in
    let! qbs = map2 faux bs bvs in
    return (fn_defn range id is_rec us qbs comp meas body)

  // A (non-recursive) definition where the body is a lambda.
  | Sugar.FnDefn { id; is_rec=false; us; binders; ascription=Inr ascription; measure=None; body=Inr body; range } ->
    let! env, bs, bvs = desugar_binders env binders in
    let! comp = 
      match ascription with
      | None -> return (mk_tot (tm_unknown range))
      | Some t -> let! t = desugar_term env t in return (mk_tot t)
    in
    let! body = desugar_lambda env body in
    let! qbs = map2 faux bs bvs in
    return (fn_defn range id false us qbs comp None body)

  // A recursive definition where the body is a lambda, not supported yet.
  | Sugar.FnDefn { id; is_rec=true; us; binders; ascription=Inr ascription; measure=None; body=Inr body; range } ->
    fail "Recursive Pulse functions cannot be defined as lambdas (yet)" range

  // Just a val declaration, with a computation type
  | Sugar.FnDecl { id; us; binders; ascription=Inl ascription; range } ->
    let! env, bs, bvs = desugar_binders env binders in

    (* Process ticks *)
    let! pannots = parse_annots ascription.range ascription.annots in
    let fvs = free_vars_comp env pannots in
    let! env, bs', bvs' = idents_as_binders env fvs in
    let bs = bs@bs' in
    let bvs = bvs@bvs' in

    let! comp = desugar_computation_type env ascription in
    let! qbs = map2 faux bs bvs in
    let comp = close_comp_bvs comp (List.Tot.map (fun (_,_,bv) -> bv) qbs) in
    return (fn_decl range id us qbs comp)

  // A val declaration with an F* type. Currently the parser forbids them,
  // but make sure to raise a nice error if we ever get one.
  | Sugar.FnDecl { id; us; binders; ascription=Inr ascription; range } ->
    fail "Unexpected FnDecl with F* type" range

  | Sugar.SlpropDefn { id; binders; body; range } ->
    let! env, bs, bvs = desugar_binders env binders in
    let! body = desugar_term env body in
    let! qbs = map2 faux bs bvs in
    return (slprop_defn range id qbs body)

  | _ ->
    fail "Unexpected Pulse declaration" (Sugar.range_of_decl d)


let reinitialize_env (dsenv:D.env)
                     (curmod:Ident.lident)
                     (open_namespaces: list name)
                     (module_abbrevs: list (string & name))
  : ML env_t
  = let dsenv = D.set_current_module dsenv curmod in
    let dsenv =
      L.fold_right
        (fun ns env -> D.push_namespace env (Ident.lid_of_path ns r_) S.Unrestricted)
        open_namespaces
        dsenv
    in
    let dsenv = D.push_namespace dsenv curmod S.Unrestricted in
    let dsenv =
      L.fold_left
        (fun env (m, n) -> 
          D.push_module_abbrev env (Ident.id_of_text m) (Ident.lid_of_path n r_))
        dsenv
        module_abbrevs
    in
    { 
      dsenv;
      local_refs = []
    }
  
let mk_env dsenv = { dsenv; local_refs = [] }
