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

let push_namespace env lid =
  let dsenv = D.push_namespace env.tcenv.dsenv lid in
  let tcenv = { env.tcenv with dsenv } in
  let env = {env with tcenv} in
  env
  
let r_ = FStar.Compiler.Range.dummyRange
let admit_lid = Ident.lid_of_path ["Prims"; "admit"] r_
let star_lid = Ident.lid_of_path ["Steel"; "Effect"; "Common"; "star"] r_
let emp_lid = Ident.lid_of_path ["Steel"; "Effect"; "Common"; "emp"] r_
let pure_lid = Ident.lid_of_path ["Steel"; "ST"; "Util"; "pure"] r_
let stt_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt"] r_
let assign_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "write"] r_
let stt_ghost_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt_ghost"] r_
let stt_atomic_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt_atomic"] r_
let stapp_assignment (lhs rhs:S.term) (r:_)
  : SW.st_term
  = let head_fv = S.lid_as_fv assign_lid None in
    let head = S.fv_to_tm head_fv in
    let app = S.mk_Tm_app head [(lhs, None)] lhs.pos in
    SW.(tm_st_app (tm_expr app r) None (as_term rhs) r)


let resolve_name (env:env_t) (id:ident)
  : err S.term
  = match D.try_lookup_id env.tcenv.dsenv id with
    | None -> fail "Name not found" (Ident.range_of_id id)
    | Some t -> return t

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
  if SW.is_tm_intro_exists s1
  then SW.tm_bind b (SW.tm_protect s1) (SW.tm_protect s2) r
  else SW.tm_bind b s1 s2 r

let explicit_rvalues (env:env_t) (s:Sugar.stmt)
  : Sugar.stmt
  = s

let qual = option SW.qualifier
let as_qual (q:A.aqual) : qual =
  match q with
  | Some A.Implicit -> SW.as_qual true
  | _ -> SW.as_qual false

(* s has already been transformed with explicit dereferences for r-values *)
let rec desugar_stmt (env:env_t) (s:Sugar.stmt)
  : err SW.st_term
  = let open SW in
    let open Sugar in
    match s.s with
    | Expr { e } -> 
      let? tm = tosyntax env e in
      return (st_term_of_stapp_or_return (stapp_or_return env tm))

    | Assignment { id; value } ->
      let? lhs = resolve_name env id in
      let? value = tosyntax env value in
      return (stapp_assignment lhs value s.range)
    
    | Sequence { s1={s=Open l}; s2 } ->
      let env = push_namespace env l in
      desugar_stmt env s2

    | Sequence { s1={s=LetBinding lb}; s2 } ->
      desugar_bind env lb s2 s.range

    | Sequence { s1; s2 } when AssertWithBinders? s1.s ->
      desugar_assert_with_binders env s1 s2 s.range

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
      failwith "Match is not yet handled"

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
        return (SW.tm_intro_exists false vp witnesses s.range)
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

and desugar_assert_with_binders (env:env_t) (s1 s2:Sugar.stmt) r
  : err SW.st_term
  = match s1.s with
    | Sugar.AssertWithBinders { binders=bs; vprop=v } ->
      let? env, binders, bvs = desugar_binders env bs in
      let vars = L.map (fun bv -> bv.S.index) bvs in
      let? v = desugar_vprop env v in
      let? s2 = desugar_stmt env s2 in
      let binders = L.map snd binders in
      let sub = SW.bvs_as_subst vars in
      let s2 = SW.subst_st_term sub s2 in
      let v = SW.subst_term sub v in
      return (SW.tm_assert_with_binders (SW.close_binders binders vars) v s2 r)
    | _ -> fail "Expected AssertWithBinders" s1.range

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

let desugar_computation_type (env:env_t) (c:Sugar.computation_type)
  : err SW.comp
  = let? pre = desugar_vprop env c.precondition in
    let? ret = desugar_term env c.return_type in
    let env1, bv = push_bv env c.return_name in
    let? post = desugar_vprop env1 c.postcondition in
    let post = SW.close_term post bv.index in
    match c.tag with
    | Sugar.ST -> return SW.(mk_comp pre (mk_binder c.return_name ret) post)
    | Sugar.STAtomic inames ->
      let? inames = desugar_term env inames in
      return SW.(atomic_comp inames pre (mk_binder c.return_name ret) post)
    | Sugar.STGhost inames ->
      let? inames = desugar_term env inames in
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
        return (SW.tm_abs last q
                          (SW.comp_pre comp)
                          body
                          (Some (SW.comp_res comp))
                          (Some (SW.comp_post comp))
                          p.range)
      | (q, b)::bs, bv::bvs ->
        let? body = aux bs bvs in
        let body = SW.close_st_term body bv.index in
        return (SW.tm_abs b q (SW.tm_emp p.range) body None None p.range)
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

