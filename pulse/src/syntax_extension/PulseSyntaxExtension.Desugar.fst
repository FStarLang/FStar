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
module SW = PulseSyntaxExtension.SyntaxWrapper
module A = FStarC.Parser.AST
module D = FStarC.Syntax.DsEnv
module ToSyntax = FStarC.ToSyntax.ToSyntax
module S = FStarC.Syntax.Syntax
module L = FStarC.List
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module R = FStarC.Range
module BU = FStarC.Util

open FStarC.Class.Show
open FStarC.Class.HasRange
open FStarC.Class.Monad
open FStarC.Ident
open FStar.List.Tot
open PulseSyntaxExtension.Err
open PulseSyntaxExtension.Env

let close_st_term_bvs (e:SW.st_term) (xs:list SW.bv) : SW.st_term = 
  SW.close_st_term_n e (L.map SW.index_of_bv xs)

let close_comp_bvs  (e:SW.comp) (xs:list SW.bv) : SW.comp = 
  SW.close_comp_n e (L.map SW.index_of_bv xs)


let rec fold_right1 (f : 'a -> 'a -> 'a) (l : list 'a) : 'a =
  match l with
  | [h] -> h
  | h::t -> f h (fold_right1 f t)

let sugar_app (r:Range.range) (f:A.term) (aa : list A.term) : A.term =
  List.fold_left  (fun f a ->
    A.mk_term (A.App (f, a, A.Nothing)) r A.Expr)
  f aa

let sugar_unit (r:Range.range) : A.term =
  A.mk_term (A.Var FStarC.Parser.Const.unit_lid) r A.Expr
let sugar_emp (r:Range.range) : A.term =
  A.mk_term (A.Var emp_lid) r A.Expr
let sugar_star (r:Range.range) : A.term =
  A.mk_term (A.Var star_lid) r A.Expr

let sugar_star_of_list (r:Range.range) (ts : list A.term) : A.term =
  match ts with
  | [] -> sugar_emp r
  | ts -> fold_right1 (fun a b -> sugar_app r (sugar_star r) [a; b]) ts

let parse_annots (r:Range.range) (cs : list Sugar.computation_annot) : err Sugar.parsed_annots =
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
  : SW.term
  = match t.n with
    | S.Tm_unknown ->
      SW.tm_unknown t.pos
    | _ -> 
      SW.tm_expr t t.pos

let desugar_const (c:FStarC.Const.sconst) : SW.constant =
  SW.inspect_const c

let comp_to_ast_term (c:Sugar.computation_type) : err A.term =
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


let faux (qb : option SW.qualifier & SW.binder) (bv : S.bv)
  : option SW.qualifier & SW.binder & SW.bv
   =
    let (q,b) = qb in
    let bv = SW.mk_bv bv.S.index
                      (Ident.string_of_id bv.S.ppname)
                      bv.S.sort.pos
    in
    (q,b,bv)

let app_lid lid (args:list S.term) (r:_)
  : S.term
  = let head_fv = S.lid_as_fv lid None in
    let head = S.fv_to_tm head_fv in
    let app = 
      L.fold_left 
        (fun head (arg:S.term) ->
          S.mk_Tm_app head [(arg, None)] arg.pos)
        head args
    in
    app


let ret (s:S.term) = SW.(tm_return (as_term s) s.pos)

type admit_or_return_t =
  | STTerm : SW.st_term -> admit_or_return_t
  | Return : S.term -> admit_or_return_t

let st_term_of_admit_or_return (t:admit_or_return_t) : SW.st_term =
  match t with
  | STTerm t -> t
  | Return t -> ret t

let admit_or_return (env:env_t) (s:S.term)
  : admit_or_return_t
  = let r = s.pos in
    let head, args = U.head_and_args_full s in
    match head.n, args with
    | S.Tm_fvar fv, [_] -> (
      if S.fv_eq_lid fv admit_lid
      then STTerm (SW.tm_admit r)
      else if S.fv_eq_lid fv unreachable_lid
      then STTerm (SW.tm_unreachable r) 
      else Return s
    )
    | _ -> Return s

let prepend_ctx_issue (c : Pprint.document) (i : Errors.issue) : Errors.issue =
  { i with issue_msg = c :: i.issue_msg }


let tosyntax' (env:env_t) (t:A.term)
  : err S.term
  = try 
      return (ToSyntax.desugar_term env.dsenv t)
    with 
      | e -> 
        match FStarC.Errors.issue_of_exn e with
        | Some i ->
          FStarC.Errors.add_issues [i];
          just_fail ()

        | None -> 
          fail (BU.format2 "Failed to desugar Pulse term %s\nUnexpected exception: %s\n"
                             (A.term_to_string t)
                             (SW.print_exn e))
                t.range

let tosyntax (env:env_t) (t:A.term)
  : err S.term
  = let! s = tosyntax' env t in
    return s

let desugar_term (env:env_t) (t:A.term)
  : err SW.term 
  = let! s = tosyntax env t in
    return (as_term s)
  
let desugar_term_opt (env:env_t) (t:option A.term)
  : err SW.term
  = match t with
    | None -> return (SW.tm_unknown FStarC.Range.dummyRange)
    | Some e -> desugar_term env e

//
// Only add undeclared tick names (e.g. 'x) as binders,
//   and with erased types
//
// Undeclared unticked names are errors
//
let idents_as_binders (env:env_t) (l:list ident)
  : err (env_t & list (option SW.qualifier & SW.binder) & list S.bv)
  = let non_tick_idents =
      l |> L.filter (fun i ->
                     i |> Ident.string_of_id
                       |> (fun s -> not (BU.starts_with s "'"))) in
    if L.length non_tick_idents <> 0
    then let s = non_tick_idents |> L.map Ident.string_of_id |> BU.concat_l ", " in
         fail
           (BU.format1 "Identifiers (%s) not found, consider adding them as binders" s)
           (non_tick_idents |> L.hd |> Ident.range_of_id)
    else begin
      let erased_tm = A.(mk_term (Var FStarC.Parser.Const.erased_lid) FStarC.Range.dummyRange Un) in
      let mk_ty i =
        let wild = A.(mk_term Wild (Ident.range_of_id i) Un) in
        A.(mkApp erased_tm [wild, A.Nothing] (Ident.range_of_id i)) in
      let rec aux env binders bvs l 
        : err (env_t & list (option SW.qualifier & SW.binder) & list S.bv)
        = match l with
          | [] -> return (env, L.rev binders, L.rev bvs)
          | i::l ->
            let env, bv = push_bv env i in
            let qual = SW.as_qual true in      
            let ty = mk_ty i in
            let! ty = desugar_term env ty in
            aux env ((qual, SW.mk_binder i ty)::binders) (bv::bvs) l
      in
      aux env [] [] l
    end

let desugar_slprop (env:env_t) (v:Sugar.slprop)
  : err SW.slprop
  = tosyntax env v

let desugar_computation_type (env:env_t) (c:Sugar.computation_type)
  : err SW.comp
  = //let! pres = map_err (desugar_slprop env) c.preconditions in
    //let pre = fold_right1 (fun a b -> SW.tm_star a b c.range) pres in
    let! annots = parse_annots c.range c.annots in
    let! pre = desugar_slprop env annots.Sugar.precondition in

    let! ret = desugar_term env annots.Sugar.return_type in

    let! opens =
      match annots.Sugar.opens with
      | Some t -> desugar_term env t
      | None -> return SW.tm_emp_inames
    in

    (* Should have return_name in scope I think *)
    // let! openss = map_err (desugar_term env) c.opens in
    // let opens = L.fold_right (fun i is -> SW.tm_add_inv i is c.range) openss SW.tm_emp_inames in

    let env1, bv = push_bv env annots.Sugar.return_name in
    // let! posts = map_err (desugar_slprop env1) c.postconditions in
    // let post = fold_right1 (fun a b -> SW.tm_star a b c.range) posts in
    let! post = desugar_slprop env1 annots.Sugar.postcondition in
    let post = SW.close_term post bv.index in

    match c.tag with
    | Sugar.ST ->
      if Some? annots.Sugar.opens then
        fail "STT computations are not indexed by invariants. Either remove the `opens` or make this function ghost/atomic."
             (Some?.v annots.Sugar.opens).range
      else return ();!
      return SW.(mk_comp pre (mk_binder annots.Sugar.return_name ret) post)
    | Sugar.STAtomic ->
      return SW.(atomic_comp opens pre (mk_binder annots.Sugar.return_name ret) post)
    | Sugar.STUnobservable ->
      return SW.(unobs_comp opens pre (mk_binder annots.Sugar.return_name ret) post)
    | Sugar.STGhost ->
      return SW.(ghost_comp opens pre (mk_binder annots.Sugar.return_name ret) post)

let mk_totbind b s1 s2 r : SW.st_term =
  SW.tm_totbind b s1 s2 r

let mk_bind b s1 s2 r : SW.st_term = 
  SW.tm_bind b s1 s2 r

let qual = option SW.qualifier

(* We open FStar.Tactics.V2 in the scope of every `by` as a convenience. *)
let desugar_tac_opt (env:env_t) (topt : option A.term) : err (option SW.term) =
  match topt with
  | None -> return None
  | Some t ->
    let tactics_module_lid = Ident.lid_of_str "FStar.Tactics.V2" in
    let env = push_namespace env tactics_module_lid in
    let! t = desugar_term env t in
    return (Some t)

let desugar_hint_type (env:env_t) (ht:Sugar.hint_type)
  : err SW.hint_type
  = let open Sugar in
    match ht with
    | ASSERT vp ->
      let! vp = desugar_slprop env vp in
      return (SW.mk_assert_hint_type vp)
    | UNFOLD (ns, vp) -> 
      let! vp = desugar_slprop env vp in
      let! ns = resolve_names env ns in
      let ns = BU.map_opt ns (L.map FStarC.Ident.string_of_lid) in
      return (SW.mk_unfold_hint_type ns vp)
    | FOLD (ns, vp) -> 
      let! vp = desugar_slprop env vp in
      let! ns = resolve_names env ns in
      let ns = BU.map_opt ns (L.map FStarC.Ident.string_of_lid) in
      return (SW.mk_fold_hint_type ns vp)
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
      return (SW.mk_rename_hint_type pairs goal tac_opt)
    | REWRITE (t1, t2, tac_opt) ->
      let! t1 = desugar_slprop env t1 in
      let! t2 = desugar_slprop env t2 in
      let! tac_opt = desugar_tac_opt env tac_opt in
      return (SW.mk_rewrite_hint_type t1 t2 tac_opt)
    | WILD ->
      return (SW.mk_wild_hint_type)
    | SHOW_PROOF_STATE r ->
      return (SW.mk_show_proof_state_hint_type r)

// FIXME
// should just mimic let resolve_lid
let desugar_datacon (env:env_t) (l:lid) : err SW.fv =
  let rng = Ident.range_of_lid l in
  let t = A.mk_term (A.Name l) rng A.Expr in
  let! tt = tosyntax env t in
  let! sfv =
    match (SS.compress tt).n with
    | S.Tm_fvar fv -> return fv
    | S.Tm_uinst ({n = S.Tm_fvar fv}, _) -> return fv
    | _ -> fail (BU.format1 "Not a datacon? %s" (Ident.string_of_lid l)) rng
  in
  return (SW.mk_fv (S.lid_of_fv sfv) rng)

let close_st_term_binders qbs body =
  let bvs = List.Tot.map (fun (_, _, b) -> b) qbs in
  close_st_term_bvs body bvs

let mk_abs_with_comp qbs comp body range =
  let _, abs =
    L.fold_right
      (fun (q,b,bv) (c, body) ->
        let body' = SW.close_st_term body (SW.index_of_bv bv) in
        let asc =
          match c with
          | None -> None
          | Some c -> Some  (SW.close_comp c (SW.index_of_bv bv)) in
        None, SW.tm_abs b q asc body' range)
      qbs (comp, body)
  in
  abs

(* s has already been transformed with explicit dereferences for r-values *)
let rec desugar_stmt' (env:env_t) (s:Sugar.stmt)
  : err SW.st_term
  = let open SW in
    let open Sugar in
    match s.s with
    | Expr { e } -> 
      let! tm = tosyntax env e in
      return (st_term_of_admit_or_return (admit_or_return env tm))

    | Assignment { lhs; value } ->
      let! lhs = tosyntax env lhs in
      let! rhs = tosyntax env value in
      let! assignment_lid = resolve_lid env (op_colon_equals_lid s.range) in
      let tm = (app_lid assignment_lid [lhs; rhs] s.range) in
      return (st_term_of_admit_or_return (admit_or_return env (app_lid assignment_lid [lhs; rhs] s.range)))

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
            fail (BU.format2
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
          | Some (Default_initializer e) -> return e
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
          mk_stmt (Match { head = A.(mk_term (Tvar id) lb.pat.prange Expr);
                          returns_annot = None;
                          branches = [(lb.norw, pat, s2)] }) s1range
                          with source = false }
        in
        let t_match =
          (* We only inject a variable when the rhs is a variable *)
          if not lb.norw &&
              (match init_expr.A.tm with
                | A.Tvar _ -> true
                | A.Var _ -> true
                | A.Name _ -> true
                | _ -> false)
          then
            let s_rw =
              mk_stmt (ProofHintWithBinders {
                    hint_type = RENAME ([(init_expr, A.mk_term (A.Tvar id) lb.pat.prange A.Expr)], None, None);
                    binders = []}) s1range
            in
            let s_rw = { s_rw with source=false } in
            seq s_rw t_match
          else t_match
        in
        let s'' =
          seq t_let t_match
        in
        // BU.print2 "GG Rewrote \n(%s)\n to \n(%s)\n\n" (show s) (show s'');
        desugar_stmt env s''
      end

    | ProofHintWithBinders _ ->
      desugar_proof_hint_with_binders env s None s.range

    | Sequence { s1; s2 } when ProofHintWithBinders? s1.s ->
      desugar_proof_hint_with_binders env s1 (Some s2) s1.range

    | Sequence { s1; s2 } -> 
      desugar_sequence env s1 s2 s.range
      
    | Block { stmt } ->
      desugar_stmt env stmt

    | If { head; join_slprop; then_; else_opt } -> 
      let! head = desugar_term env head in
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
      return (SW.tm_if head join_slprop then_ else_ s.range)

    | Match { head; returns_annot; branches } ->
      let! head = desugar_term env head in
      let! returns_annot = map_err_opt (fun (_, t, _opens) -> desugar_slprop env t) returns_annot in
      let! branches = branches |> mapM (desugar_branch env) in
      return (SW.tm_match head returns_annot branches s.range)

    | While { guard; id=Some id; invariant; body } ->
      let! guard = desugar_stmt env guard in
      let! invariant = 
        let env, bv = push_bv env id in
        let! inv = desugar_slprop env invariant in
        return (SW.close_term inv bv.index)
      in
      let! body = desugar_stmt env body in
      return (SW.tm_while guard (id, invariant) body s.range)

    | While { guard; id=None; invariant; body } ->
      let! guard = desugar_stmt env guard in
      let! invariant = desugar_slprop env invariant in
      let! body = desugar_stmt env body in
      return (SW.tm_nuwhile guard invariant body s.range)

    | Introduce { slprop; witnesses } -> (
      let! vp = desugar_slprop env slprop in
      let! witnesses = witnesses |> mapM (desugar_term env) in
      return (SW.tm_intro_exists vp witnesses s.range)
    )

    | Parallel { p1; p2; q1; q2; b1; b2 } ->
      let! p1 = desugar_slprop env p1 in
      let! p2 = desugar_slprop env p2 in
      let! q1 = desugar_slprop env q1 in
      let! q2 = desugar_slprop env q2 in      
      let! b1 = desugar_stmt env b1 in
      let! b2 = desugar_stmt env b2 in
      return (SW.tm_par p1 p2 q1 q2 b1 b2 s.range)

    | LetBinding _ -> 
      fail "Terminal let binding" s.range

    | WithInvariants { names=n1::names; body; returns_ } ->
      let! n1 = tosyntax env n1 in
      let! names = names |> mapM (tosyntax env) in
      let! body = desugar_stmt env body in
      let! returns_ =
        let opens_tm opens_opt : err SW.term =
          match opens_opt with
          | Some opens -> desugar_term env opens
          | None ->
            let all_names = n1::names in
            let opens_tm = L.fold_left (fun names n ->
              SW.tm_add_inv names (tm_expr n s.range) s.range) SW.tm_emp_inames all_names in
            return opens_tm in
        match returns_ with
        | None -> return None
        | Some (None, v, opens_opt) -> 
          let! v = desugar_slprop env v in
          let b = SW.mk_binder (Ident.id_of_text "_") (SW.tm_unknown s.range) in
          let! opens = opens_tm opens_opt in
          return (Some (b, v, opens))
        | Some (Some (x, t), v, opens_opt) ->
          let! t = desugar_term env t in
          let env, bv = push_bv env x in
          let! v = desugar_slprop env v in
          let v = SW.close_term v bv.index in
          let b = SW.mk_binder x t in
          let! opens = opens_tm opens_opt in
          return (Some (b, v, opens))
      in
      (* the returns_ goes only to the outermost with_inv *)
      let tt = L.fold_right (fun nm body -> let nm : term = tm_expr nm s.range in SW.tm_with_inv nm body None s.range) names body in
      let n1 : term = tm_expr n1 s.range in
      return (SW.tm_with_inv n1 tt returns_ s.range)

and desugar_stmt (env:env_t) (s:Sugar.stmt) : err SW.st_term =
  let! r = desugar_stmt' env s in
  if not s.source then
    return (SW.mark_not_source r)
  else
    return r

and desugar_branch (env:env_t) (br: bool & A.pattern & Sugar.stmt)
  : err SW.branch
  = let (norw, p, e) = br in
    let! (p, vs) = desugar_pat env p in
    let env, bvs = push_bvs env vs in
    let! e = desugar_stmt env e in
    let e = SW.close_st_term_n e (L.map (fun (v:S.bv) -> v.index <: nat) bvs) in
    return (SW.mk_branch p e norw)

and desugar_pat (env:env_t) (p:A.pattern)
  : err (SW.pattern & list ident)
  = let r = p.prange in
    match p.pat with
    | A.PatVar (id, _, _) ->
      return (SW.pat_var (Ident.string_of_id id) r, [id])
    | A.PatWild _ ->
      let id = Ident.mk_ident ("_", r) in
      return (SW.pat_var "_" r, [id])
    | A.PatConst c ->
      let c = desugar_const c in
      return (SW.pat_constant c r, [])
    | A.PatName lid ->
      let! fv = desugar_datacon env lid in
      return (SW.pat_cons fv [] r, [])
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
      let pats = L.map (fun s -> SW.pat_var s r) strs in
      return (SW.pat_cons fv pats r, idents)

    | A.PatList ps ->
      let! ps = ps |> mapM (fun p -> desugar_pat env p) in
      let pats, idents = L.unzip ps in
      let cons = SW.mk_fv Parser.Const.cons_lid r in
      let nil  = SW.mk_fv Parser.Const.nil_lid r in
      let pat = FStarC.List.fold_right (fun p acc -> SW.pat_cons cons [p;acc] r) pats (SW.pat_cons nil [] r) in
      return (pat, L.flatten idents)

    | A.PatTuple (ps, dep) ->
      let! ps = ps |> mapM (fun p -> desugar_pat env p) in
      let pats, idents = L.unzip ps in
      let ctor = SW.mk_fv (Parser.Const.Tuples.mk_tuple_data_lid (L.length pats) r) r in
      let pat = SW.pat_cons ctor pats r in
      return (pat, L.flatten idents)

    | A.PatRest ->
      fail "Invalid pattern: `..` can only appear applied to a constructor" r

    | _ ->
      fail "invalid pattern" r

and desugar_bind (env:env_t) (lb:_) (s2:Sugar.stmt) (r:R.range)
  : err SW.st_term
  = let open Sugar in
    let! annot = desugar_term_opt env lb.typ in
    let id = 
      match lb.pat.pat with
      | A.PatWild _ -> Ident.mk_ident ("_", r)
      | A.PatVar (id, _, _) -> id
    in
    let b = SW.mk_binder id annot in
    let! s2 =
      let env, bv = push_bv env id in
      let! s2 = desugar_stmt env s2 in
      return (SW.close_st_term s2 bv.index)
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
            | None -> return (SW.mk_tot (SW.tm_unknown range))
            | Some t -> let! t = desugar_term env t in return (SW.mk_tot t)
          in
          let! body = desugar_lambda env body in
          let! qbs = map2 faux bs bvs in
          let abs = mk_abs_with_comp qbs (Some comp) body range in
          return <| mk_bind b abs s2 r

        | Sugar.Lambda_initializer _ ->
          fail "Nested functions are not yet fully supported" r

        | Default_initializer e1 ->
          let! s1 = tosyntax env e1 in
          let t =
            match admit_or_return env s1 with
            | STTerm s1 ->
              mk_bind b s1 s2 r
            | Return s1 ->
              mk_totbind b (as_term s1) s2 r
          in
          return t

        | Stmt_initializer e ->
          let! s = desugar_stmt env e in
          return (mk_bind b s s2 r)
      )
      | Some MUT //these are handled the same for now
      | Some REF ->
        let b = SW.mk_binder id annot in
        match e1 with
        | Sugar.Array_initializer {init; len} ->
          let! init = desugar_term env init in
          let! len = desugar_term env len in
          return (SW.tm_let_mut_array b init len s2 r)
        | Sugar.Default_initializer e1 ->
          let! e1 = desugar_term env e1 in
          return (SW.tm_let_mut b e1 s2 r)
    )

and desugar_sequence (env:env_t) (s1 s2:Sugar.stmt) r
  : err SW.st_term
  = let semicolon = not (Sugar.LetBinding? s1.s) in
    let! s1 = desugar_stmt env s1 in
    let s1 =
      if semicolon
      then SW.mark_statement_sequence s1
      else s1
    in
    let! s2 = desugar_stmt env s2 in
    let annot = SW.mk_binder (Ident.id_of_text "_") (SW.tm_unknown r) in
    return (mk_bind annot s1 s2 r)

and desugar_proof_hint_with_binders (env:env_t) (s1:Sugar.stmt) (k:option Sugar.stmt) r
  : err SW.st_term
  = match s1.s with
    | Sugar.ProofHintWithBinders { hint_type = Sugar.ASSUME p; binders=[] } ->
      let assume_fv = SW.(mk_fv assume_lid r) in
      let assume_ : SW.term = SW.(tm_fvar assume_fv) in
      let! p = desugar_slprop env p in
      let s1 = SW.tm_st_app assume_ None p r in
      let! s2 =
        match k with
        | None -> return (SW.tm_ghost_return (SW.tm_expr S.unit_const r) r)
        | Some s2 -> desugar_stmt env s2 in
     let annot = SW.mk_binder (Ident.id_of_text "_") (SW.tm_unknown r) in
     return (mk_bind annot s1 s2 r)

    | Sugar.ProofHintWithBinders { hint_type = Sugar.ASSUME _; binders=b1::_ } ->
      fail "'assume' cannot have binders" b1.brange

    | Sugar.ProofHintWithBinders { hint_type; binders=bs } -> //; slprop=v } ->
      let! env, binders, bvs = desugar_binders env bs in
      let vars = L.map #_ #nat (fun bv -> bv.S.index) bvs in
      let! ht = desugar_hint_type env hint_type in
      let! s2 = 
        match k with
        | None -> return (SW.tm_ghost_return (SW.tm_expr S.unit_const r) r)
        | Some s2 -> desugar_stmt env s2 in
      let binders = L.map snd binders in
      let sub = SW.bvs_as_subst vars in
      let s2 = SW.subst_st_term sub s2 in
      let ht = SW.subst_proof_hint sub ht in
      return (SW.tm_proof_hint_with_binders ht (SW.close_binders binders vars) s2 r)
    | _ -> fail "Expected ProofHintWithBinders" s1.range

and desugar_binders (env:env_t) (bs:Sugar.binders)
  : err (env_t & list (option SW.qualifier & SW.binder) & list S.bv)
  = let rec aux env bs 
      : err (env_t & list (qual & ident & SW.term & list SW.term) & list S.bv)
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
    return (env, L.map (fun (aq, b, t, attrs) -> aq, SW.mk_binder_with_attrs b t attrs) bs, bvs)

and desugar_lambda (env:env_t) (l:Sugar.lambda)
  : err SW.st_term
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
    let! body = desugar_stmt env body in
    let! qbs = map2 faux bs bvs in
    let abs = mk_abs_with_comp qbs comp body range in
    return abs

and desugar_decl (env:env_t)
                 (d:Sugar.decl)
: err SW.decl
= let mk_knot_arr
        (env:env_t) 
        (meas : option A.term)
        (bs:Sugar.binders)
        (res:Sugar.computation_type)
  : err A.term
  = // can we just use a unknown type here?
    let! annots = parse_annots res.range res.annots in
    let r = range_of_id annots.Sugar.return_name in
    let! env, bs', _ = desugar_binders env bs in
    let! res_t = comp_to_ast_term res in
    let bs'' = bs |> L.map (fun b ->
      let (q, x, ty, _) = destruct_binder b in
      A.mk_binder (A.Annotated (x, ty)) r A.Expr q)
    in
    let last = L.last bs'' in
    let init = L.init bs'' in
    let bs'' = init @ [last] in
    return (A.mk_term (A.Product (bs'', res_t)) r A.Expr)
  in
  match d with
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
        let! ty = mk_knot_arr env measure binders ascription in
        let! ty = desugar_term env ty in
        let env, bv = push_bv env id in
        let b = SW.mk_binder id ty in
        return (env, bs@[(None, b)], bvs@[bv])
      else
        return (env, bs, bvs)
    in
    let! body = desugar_stmt env body in
    let! qbs = map2 faux bs bvs in
    let body = close_st_term_binders qbs body in
    return (SW.fn_defn range id is_rec us qbs comp meas body)

  | Sugar.FnDefn { id; is_rec=false; us; binders; ascription=Inr ascription; measure=None; body=Inr body; range } ->
    let! env, bs, bvs = desugar_binders env binders in
    let! comp = 
      match ascription with
      | None -> return (SW.mk_tot (SW.tm_unknown range))
      | Some t -> let! t = desugar_term env t in return (SW.mk_tot t)
    in
    let! body = desugar_lambda env body in
    let! qbs = map2 faux bs bvs in
    let body = close_st_term_binders qbs body in
    return (SW.fn_defn range id false us qbs comp None body)

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
    return (SW.fn_decl range id us qbs comp)

and as_qual (env:env_t) (q:A.aqual) rng : err qual =
  match q with
  | Some A.Implicit -> return <| SW.as_qual true
  | Some A.TypeClassArg -> return <| SW.tc_qual
  | Some (A.Meta t) ->
    let! t = desugar_term env t in
    return <| SW.meta_qual t
  | Some A.Equality ->
    fail "Pulse does not yet support equality arguments" rng
  | None -> return <| SW.as_qual false


let reinitialize_env (dsenv:D.env)
                     (curmod:Ident.lident)
                     (open_namespaces: list name)
                     (module_abbrevs: list (string & name))
  : env_t
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
