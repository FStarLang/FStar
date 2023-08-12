module PulseDesugar
open FStar.Compiler.Effect
module Sugar = PulseSugar
module SW = PulseSyntaxWrapper
module A = FStar.Parser.AST
module D = FStar.Syntax.DsEnv
module ToSyntax = FStar.ToSyntax.ToSyntax
open FStar.Ident
module S = FStar.Syntax.Syntax
module L = FStar.Compiler.List
module U = FStar.Syntax.Util
module TcEnv = FStar.TypeChecker.Env
module SS = FStar.Syntax.Subst
module R = FStar.Compiler.Range
module BU = FStar.Compiler.Util
module P =  FStar.Syntax.Print
type error = string & R.range

let err a = either a error

let (let?) (f:err 'a) (g: 'a -> ML (err 'b)) =
  match f with
  | Inl a -> g a
  | Inr e -> Inr e

let return (x:'a) : err 'a = Inl x

let fail #a (message:string) (range:R.range) : err a =
  Inr (message, range)

let rec map_err (f:'a -> err 'b) (l:list 'a)
  : err (list 'b)
  = match l with
    | [] -> return []
    | hd::tl ->
      let? hd = f hd in
      let? tl = map_err f tl in
      return (hd :: tl)

let map_err_opt (f : 'a -> err 'b) (o:option 'a) : err (option 'b) =
  match o with
  | None -> return None
  | Some v -> let? v' = f v in return (Some v')

let as_term (t:S.term)
  : SW.term
  = match t.n with
    | S.Tm_unknown ->
      SW.tm_unknown t.pos
    | _ -> 
      SW.tm_expr t t.pos

type env_t = { 
  tcenv: TcEnv.env;
  local_refs: list ident
}


let push_bv env x =
  let dsenv, bv = D.push_bv env.tcenv.dsenv x in
  let tcenv = { env.tcenv with dsenv = dsenv } in
  let env = { env with tcenv } in
  env, bv

let rec push_bvs env xs =
  match xs with
  | [] -> env, []
  | x::xs ->
    let env, bv = push_bv env x in
    let env, bvs = push_bvs env xs in
    env, bv::bvs

let push_namespace env lid =
  let dsenv = D.push_namespace env.tcenv.dsenv lid in
  let tcenv = { env.tcenv with dsenv } in
  let env = {env with tcenv} in
  env
  
let desugar_const (c:FStar.Const.sconst) : SW.constant =
  SW.inspect_const c

let r_ = FStar.Compiler.Range.dummyRange
let admit_lid = Ident.lid_of_path ["Prims"; "admit"] r_
open FStar.List.Tot
let pulse_lib_core_lid l = Ident.lid_of_path (["Pulse"; "Lib"; "Core"]@[l]) r_
let pulse_lib_ref_lid l = Ident.lid_of_path (["Pulse"; "Lib"; "Reference"]@[l]) r_
let star_lid = pulse_lib_core_lid "op_Star_Star"
let emp_lid = pulse_lib_core_lid "emp"
let pure_lid = pulse_lib_core_lid "pure"
let stt_lid = pulse_lib_core_lid "stt"
let assign_lid = pulse_lib_ref_lid "op_Colon_Equals"
let stt_ghost_lid = pulse_lib_core_lid "stt_ghost"
let stt_atomic_lid = pulse_lib_core_lid "stt_atomic"
let op_colon_equals_lid r = Ident.lid_of_path ["op_Colon_Equals"] r
let stapp_assignment assign_lid (lhs rhs:S.term) (r:_)
  : SW.st_term
  = let head_fv = S.lid_as_fv assign_lid None in
    let head = S.fv_to_tm head_fv in
    let app = S.mk_Tm_app head [(lhs, None)] lhs.pos in
    SW.(tm_st_app (tm_expr app r) None (as_term rhs) r)

let resolve_lid (env:env_t) (lid:lident)
  : err lident
  = match D.try_lookup_lid env.tcenv.dsenv lid with
    | None -> fail (BU.format1 "Name %s not found" (Ident.string_of_lid lid)) (Ident.range_of_lid lid)
    | Some t ->
      match (SS.compress t).n with
      | S.Tm_fvar fv -> return (S.lid_of_fv fv)
      | _ -> fail (BU.format2 "Name %s resolved unexpectedly to %s" (Ident.string_of_lid lid) (P.term_to_string t))
                  (Ident.range_of_lid lid)

let pulse_arrow_formals (t:S.term) =
    let formals, comp = U.arrow_formals_comp_ln t in
    if U.is_total_comp comp
    then (
      let res = U.comp_result comp in        
      let head, _ = U.head_and_args_full res in
      match (SS.compress head).n with
      | S.Tm_fvar fv
      | S.Tm_uinst ({n=S.Tm_fvar fv}, _) ->
        if L.existsML (S.fv_eq_lid fv) [stt_lid; stt_ghost_lid; stt_atomic_lid]
        then Some formals
        else None
      | _ -> None
    )
    else None

let ret (s:S.term) = SW.(tm_return (as_term s) s.pos)

type stapp_or_return_t =
  | STTerm : SW.st_term -> stapp_or_return_t
  | Return : S.term -> stapp_or_return_t

let st_term_of_stapp_or_return (t:stapp_or_return_t) : SW.st_term =
  match t with
  | STTerm t -> t
  | Return t -> ret t

let stapp_or_return (env:env_t) (s:S.term)
  : stapp_or_return_t
  = let r = s.pos in
    let head, args = U.head_and_args_full s in
    match head.n with
    | S.Tm_fvar fv -> (
      if S.fv_eq_lid fv admit_lid
      then STTerm (SW.tm_admit r) 
      else
      match TcEnv.try_lookup_lid env.tcenv fv.fv_name.v with
      | None -> Return s
      | Some ((_, t), _) ->
        match pulse_arrow_formals t with
        | None -> Return s
        | Some formals ->
          let is_binder_implicit (b:S.binder) =
            match b.binder_qual with
            | Some (S.Implicit _) -> true
            | _ -> false
          in
          let is_arg_implicit (aq:S.arg) =
            match snd aq with
            | Some {aqual_implicit=b} -> b
            | _ -> false
          in
          let rec uninst_formals formals args =
            match formals, args with
            | _, [] ->
              Some formals

            | [], _ -> //too many args, ill-typed
              None

            | f::formals, a::args ->
              if is_binder_implicit f
              then (
                if is_arg_implicit a
                then uninst_formals formals args
                else uninst_formals formals (a::args)
              )
              else if is_arg_implicit a
              then // this looks ill-typed
                   None
              else //both explicit
                   uninst_formals formals args
          in
          match uninst_formals formals args with
          | None -> //likely ill-typed; leave as is
            Return s

          | Some formals ->
            if L.for_all is_binder_implicit formals
            then ( //this is an st app
              let head = S.mk_Tm_app head (L.init args) s.pos in
              let last, q = L.last args in
              STTerm SW.(tm_st_app (tm_expr head head.pos) q (as_term last) r)
            )
            else (
              //partial app of a stateful function
              Return s
            )
      )
    | _ -> Return s


let tosyntax' (env:env_t) (t:A.term)
  : err S.term
  = try 
      return (ToSyntax.desugar_term env.tcenv.dsenv t)
    with 
      | e -> 
        match FStar.Errors.issue_of_exn e with
        | Some i -> 
          FStar.Errors.add_issues [i];
          fail "Failed to desugar Pulse term" t.range
        | None -> 
          fail (BU.format2 "Failed to desugar Pulse term %s\nUnexpected exception: %s\n"
                             (A.term_to_string t)
                             (SW.print_exn e))
                t.range

let tosyntax (env:env_t) (t:A.term)
  : err S.term
  = let? s = tosyntax' env t in
    return s

let desugar_term (env:env_t) (t:A.term)
  : err SW.term 
  = let? s = tosyntax env t in
    return (as_term s)
  
let desugar_term_opt (env:env_t) (t:option A.term)
  : err SW.term
  = match t with
    | None -> return (SW.tm_unknown FStar.Compiler.Range.dummyRange)
    | Some e -> desugar_term env e

let interpret_vprop_constructors (env:env_t) (v:S.term)
  : SW.term
  = let head, args = U.head_and_args_full v in
    match head.n, args with
    | S.Tm_fvar fv, [(l, _)]
      when S.fv_eq_lid fv pure_lid ->
      let res = SW.tm_pure (as_term l) v.pos in
      res
      

    | S.Tm_fvar fv, []
      when S.fv_eq_lid fv emp_lid ->
      SW.tm_emp v.pos
      
    | _ -> as_term v
  
let rec desugar_vprop (env:env_t) (v:Sugar.vprop)
  : err SW.vprop
  = match v.v with
    | Sugar.VPropTerm t -> 
      let? t = tosyntax env t in
      return (interpret_vprop_constructors env t)
    | Sugar.VPropStar (v1, v2) ->
      let? v1 = desugar_vprop env v1 in
      let? v2 = desugar_vprop env v2 in
      return (SW.tm_star v1 v2 v.vrange)
    | Sugar.VPropExists { binders; body } ->
      let rec aux env binders
        : err SW.vprop =
        match binders with
        | [] -> 
          desugar_vprop env body
        | (_, i, t)::bs ->
          let? t = desugar_term env t in
          let env, bv = push_bv env i in
          let? body = aux env bs in
          let body = SW.close_term body bv.index in
          let b = SW.mk_binder i t in
          return (SW.tm_exists b body v.vrange)
      in
      aux env binders

let mk_totbind b s1 s2 r : SW.st_term =
  SW.tm_totbind b s1 s2 r

let mk_bind b s1 s2 r : SW.st_term = 
  SW.tm_bind b s1 s2 r

let explicit_rvalues (env:env_t) (s:Sugar.stmt)
  : Sugar.stmt
  = s

let qual = option SW.qualifier
let as_qual (q:A.aqual) : qual =
  match q with
  | Some A.Implicit -> SW.as_qual true
  | _ -> SW.as_qual false

let resolve_names (env:env_t) (ns:option (list lident)) 
  : err (option (list lident))
  = match ns with
    | None -> return None
    | Some ns -> let? ns = map_err (resolve_lid env) ns in return (Some ns)

let resolve_hint_type (env:env_t) (ht:Sugar.hint_type)
  : err Sugar.hint_type
  = let open Sugar in
    match ht with
    | ASSERT -> return ASSERT
    | UNFOLD ns -> 
      let? ns = resolve_names env ns in
      return (UNFOLD ns)
    | FOLD ns -> 
      let? ns = resolve_names env ns in
      return (FOLD ns)

// FIXME
// should just mimic let resolve_lid
let desugar_datacon (env:env_t) (l:lid) : err SW.fv =
  let rng = Ident.range_of_lid l in
  let t = A.mk_term (A.Name l) rng A.Expr in
  let? tt = tosyntax env t in
  let? sfv =
    match (SS.compress tt).n with
    | S.Tm_fvar fv -> Inl fv
    | S.Tm_uinst ({n = S.Tm_fvar fv}, _) -> Inl fv
    | _ -> fail (BU.format1 "Not a datacon? %s" (Ident.string_of_lid l)) rng
  in
  Inl (SW.mk_fv (S.lid_of_fv sfv) rng)

(* s has already been transformed with explicit dereferences for r-values *)
let rec desugar_stmt (env:env_t) (s:Sugar.stmt)
  : err SW.st_term
  = let open SW in
    let open Sugar in
    match s.s with
    | Expr { e } -> 
      let? tm = tosyntax env e in
      return (st_term_of_stapp_or_return (stapp_or_return env tm))

    | Assignment { lhs; value } ->
      let? lhs = tosyntax env lhs in
      let? rhs = tosyntax env value in
      let? assignment_lid = resolve_lid env (op_colon_equals_lid s.range) in
      return (stapp_assignment assignment_lid lhs rhs s.range)
    
    | Sequence { s1={s=Open l}; s2 } ->
      let env = push_namespace env l in
      desugar_stmt env s2

    | Sequence { s1={s=LetBinding lb}; s2 } ->
      desugar_bind env lb s2 s.range

    | ProofHintWithBinders _ ->
      desugar_assert_with_binders env s None s.range

    | Sequence { s1; s2 } when ProofHintWithBinders? s1.s ->
      desugar_assert_with_binders env s1 (Some s2) s.range

    | Sequence { s1; s2 } -> 
      desugar_sequence env s1 s2 s.range
      
    | Block { stmt } ->
      desugar_stmt env stmt

    | If { head; join_vprop; then_; else_opt } -> 
      let? head = desugar_term env head in
      let? join_vprop =
        match join_vprop with
        | None -> return None
        | Some t -> 
          let? vp = desugar_vprop env t in
          return (Some vp)
      in
      let? then_ = desugar_stmt env then_ in
      let? else_ = 
        match else_opt with
        | None -> 
          return (tm_return (tm_expr S.unit_const R.dummyRange) R.dummyRange)
        | Some e -> 
          desugar_stmt env e
      in
      return (SW.tm_if head join_vprop then_ else_ s.range)

    | Match { head; returns_annot; branches } ->
      let? head = desugar_term env head in
      let? returns_annot = map_err_opt (desugar_vprop env) returns_annot in
      let? branches = map_err (desugar_branch env) branches in
      return (SW.tm_match head returns_annot branches s.range)

    | While { guard; id; invariant; body } ->
      let? guard = desugar_stmt env guard in
      let? invariant = 
        let env, bv = push_bv env id in
        let? inv = desugar_vprop env invariant in
        return (SW.close_term inv bv.index)
      in
      let? body = desugar_stmt env body in
      return (SW.tm_while guard (id, invariant) body s.range)

    | Introduce { vprop; witnesses } -> (
      match vprop.v with
      | VPropTerm _ ->
        fail "introduce expects an existential formula" s.range
      | VPropExists _ ->
        let? vp = desugar_vprop env vprop in
        let? witnesses = map_err (desugar_term env) witnesses in
        return (SW.tm_intro_exists vp witnesses s.range)
    )


    | Parallel { p1; p2; q1; q2; b1; b2 } ->
      let? p1 = desugar_vprop env p1 in
      let? p2 = desugar_vprop env p2 in
      let? q1 = desugar_vprop env q1 in
      let? q2 = desugar_vprop env q2 in      
      let? b1 = desugar_stmt env b1 in
      let? b2 = desugar_stmt env b2 in
      return (SW.tm_par p1 p2 q1 q2 b1 b2 s.range)

    | Rewrite { p1; p2 } ->
      let? p1 = desugar_vprop env p1 in
      let? p2 = desugar_vprop env p2 in
      return (SW.tm_rewrite p1 p2 s.range)

    | LetBinding _ -> 
      fail "Terminal let binding" s.range

and desugar_branch (env:env_t) (br:A.pattern & Sugar.stmt)
  : err SW.branch
  = let (p, e) = br in
    let? (p, vs) = desugar_pat env p in
    let env, bvs = push_bvs env vs in
    let? e = desugar_stmt env e in
    let e = SW.close_st_term_n e (L.map (fun (v:S.bv) -> v.index) bvs) in
    return (p,e)

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
      let? fv = desugar_datacon env lid in
      return (SW.pat_cons fv [] r, [])
    | A.PatApp ({pat=A.PatName lid}, args) ->
      let? fv = desugar_datacon env lid in
      let? idents = map_err (fun (p:A.pattern) ->
          match p.pat with
          | A.PatVar (id, _, _) -> return id
          | A.PatWild _ -> return (Ident.mk_ident ("_", r))
          | _ -> fail "invalid pattern: no deep patterns allowed" r
      ) args
      in
      let strs = L.map Ident.string_of_id idents in
      let pats = L.map (fun s -> SW.pat_var s r) strs in
      return (SW.pat_cons fv pats r, idents)

    | _ ->
      fail "invalid pattern" r

and desugar_bind (env:env_t) (lb:_) (s2:Sugar.stmt) (r:R.range)
  : err SW.st_term
  = let open Sugar in
    let? annot = desugar_term_opt env lb.typ in
    let? s2 = 
      let env, bv = push_bv env lb.id in        
      let? s2 = desugar_stmt env s2 in
      return (SW.close_st_term s2  bv.index)
    in        
    match lb.init with
    | None ->
      failwith "Uninitialized variables are not yet handled"

    | Some e1 -> (
      match lb.qualifier with
      | None -> //just a regular bind
        let? s1 = tosyntax env e1 in
        let b = SW.mk_binder lb.id annot in
        let t =
          match stapp_or_return env s1 with
          | STTerm s1 ->
            mk_bind b s1 s2 r
          | Return s1 ->
            mk_totbind b (as_term s1) s2 r
        in
        return t
      | Some MUT //these are handled the same for now
      | Some REF -> 
        let? e1 = desugar_term env e1 in 
        let b = SW.mk_binder lb.id annot in
        return (SW.tm_let_mut b e1 s2 r)
    )

and desugar_sequence (env:env_t) (s1 s2:Sugar.stmt) r
  : err SW.st_term
  = let? s1 = desugar_stmt env s1 in
    let? s2 = desugar_stmt env s2 in
    let annot = SW.mk_binder (Ident.id_of_text "_") (SW.tm_unknown r) in
    return (mk_bind annot s1 s2 r)

and desugar_assert_with_binders (env:env_t) (s1:Sugar.stmt) (k:option Sugar.stmt) r
  : err SW.st_term
  = match s1.s with
    | Sugar.ProofHintWithBinders { hint_type; binders=bs; vprop=v } ->
      let? env, binders, bvs = desugar_binders env bs in
      let vars = L.map (fun bv -> bv.S.index) bvs in
      let? v = desugar_vprop env v in
      let? s2 = 
        match k with
        | None -> return (SW.tm_ghost_return (SW.tm_expr S.unit_const r) r)
        | Some s2 -> desugar_stmt env s2 in
      let binders = L.map snd binders in
      let sub = SW.bvs_as_subst vars in
      let s2 = SW.subst_st_term sub s2 in
      let v = SW.subst_term sub v in
      let? ht = resolve_hint_type env hint_type in
      return (SW.tm_proof_hint_with_binders ht (SW.close_binders binders vars) v s2 r)
    | _ -> fail "Expected ProofHintWithBinders" s1.range

and desugar_binders (env:env_t) (bs:Sugar.binders)
  : err (env_t & list (option SW.qualifier & SW.binder) & list S.bv)
  = let rec aux env bs 
      : err (env_t & list (qual & ident & SW.term) & list S.bv)
      = match bs with
        | [] -> return (env, [], [])
        | (aq, b, t)::bs ->
          let? t = desugar_term env t in
          let env, bv = push_bv env b in
          let? env, bs, bvs = aux env bs in
          return (env, (as_qual aq, b, t)::bs, bv::bvs)
    in
    let? env, bs, bvs = aux env bs in
    return (env, L.map (fun (aq, b, t) -> aq, SW.mk_binder b t) bs, bvs)

and desugar_computation_type (env:env_t) (c:Sugar.computation_type)
  : err SW.comp
  = let? pre = desugar_vprop env c.precondition in
    let? ret = desugar_term env c.return_type in
    let env1, bv = push_bv env c.return_name in
    let? post = desugar_vprop env1 c.postcondition in
    let post = SW.close_term post bv.index in
    match c.tag with
    | Sugar.ST -> return SW.(mk_comp pre (mk_binder c.return_name ret) post)
    | Sugar.STAtomic _ -> // For now, we only support empty inames ->
      // let? inames = desugar_term env inames in
      let inames = SW.tm_emp_inames in
      return SW.(atomic_comp inames pre (mk_binder c.return_name ret) post)
    | Sugar.STGhost _ -> // For now, we only support empty inames ->
      // let? inames = desugar_term env inames in
      let inames = SW.tm_emp_inames in
      return SW.(ghost_comp inames pre (mk_binder c.return_name ret) post)      


let desugar_decl (env:env_t)
                 (p:Sugar.decl)
  : err SW.st_term 
  = let? env, bs, bvs = desugar_binders env p.binders in
    let? body = desugar_stmt env p.body in
    let? comp = desugar_computation_type env p.ascription in
    let rec aux (bs:list (option SW.qualifier & SW.binder)) (bvs:list S.bv) =
      match bs, bvs with
      | [(q, last)], [last_bv] -> 
        let body = SW.close_st_term body last_bv.S.index in
        let comp = SW.close_comp comp last_bv.S.index in
        return (SW.tm_abs last q comp
                          body
                          p.range)
      | (q, b)::bs, bv::bvs ->
        let? body = aux bs bvs in
        let body = SW.close_st_term body bv.index in
        let comp = SW.mk_tot (SW.tm_unknown r_) in
        return (SW.tm_abs b q comp body p.range)
      | _ -> fail "Unexpected empty binders in decl" r_
    in
    aux bs bvs

let name = list string

let initialize_env (env:TcEnv.env)
                   (open_namespaces: list name)
                   (module_abbrevs: list (string & name))
  : env_t
  = let dsenv = env.dsenv in
    let dsenv = D.set_current_module dsenv (TcEnv.current_module env) in
    let dsenv =
      L.fold_right
        (fun ns env -> D.push_namespace env (Ident.lid_of_path ns r_))
        open_namespaces
        dsenv
    in
    let dsenv = D.push_namespace dsenv (TcEnv.current_module env) in
    let dsenv =
      L.fold_left
        (fun env (m, n) -> 
          D.push_module_abbrev env (Ident.id_of_text m) (Ident.lid_of_path n r_))
        dsenv
        module_abbrevs
    in
    let env = { env with dsenv } in
    { 
      tcenv = env;
      local_refs = []
    }
