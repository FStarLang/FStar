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
type env = { 
  tcenv: TcEnv.env;
  dsenv: D.env;
  local_refs: list ident
}

let push_bv env x =
  let dsenv, bv = D.push_bv env.dsenv x in
  let env = { env with dsenv } in
  env, bv

let r_ = FStar.Compiler.Range.dummyRange
let star_lid = Ident.lid_of_path ["Steel"; "Effect"; "Common"; "star"] r_
let emp_lid = Ident.lid_of_path ["Steel"; "Effect"; "Common"; "emp"] r_
let pure_lid = Ident.lid_of_path ["Steel"; "Effect"; "Common"; "pure"] r_
let stt_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt"] r_
let assign_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "write"] r_
let stt_ghost_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt_ghost"] r_
let stt_atomic_lid = Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt_atomic"] r_
let stapp_assignment (lhs rhs:S.term) 
  : SW.st_term
  = let head_fv = S.lid_as_fv assign_lid S.delta_equational None in
    let head = S.fv_to_tm head_fv in
    let app = S.mk_Tm_app head [(lhs, None)] lhs.pos in
    SW.(tm_st_app (tm_expr app) None (tm_expr rhs))


let resolve_name (env:env) (id:ident) : S.term = 
    match D.try_lookup_id env.dsenv id with
    | None -> failwith "Name not found"
    | Some t -> t

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

let stapp_or_return (env:env) (s:S.term) 
  : SW.st_term
  = let ret s = SW.(tm_return (tm_expr s)) in
    let head, args = U.head_and_args_full s in
    match head.n with
    | S.Tm_fvar fv -> (
      match TcEnv.try_lookup_lid env.tcenv fv.fv_name.v with
      | None -> ret s
      | Some ((_, t), _) ->
        match pulse_arrow_formals t with
        | None -> ret s
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
            ret s

          | Some formals ->
            if L.for_all is_binder_implicit formals
            then ( //this is an st app
              let head = S.mk_Tm_app head (L.init args) s.pos in
              let last, q = L.last args in
              SW.(tm_st_app (tm_expr head) q (tm_expr last))
            )
            else (
              //partial app of a stateful function
              ret s
            )
      )
    | _ -> ret s


let desugar_term (env:env) (t:A.term)
  : SW.term 
  = SW.tm_expr (ToSyntax.desugar_term env.dsenv t)
  
let desugar_term_opt (env:env) (t:option A.term)
  : SW.term
  = match t with
    | None -> SW.tm_unknown
    | Some e -> desugar_term env e


let rec interpret_vprop_constructors (env:env) (v:S.term)
  : SW.term
  = let head, args = U.head_and_args_full v in
    match head.n, args with
    | S.Tm_fvar fv, [(l, _); (r, _)] 
      when S.fv_eq_lid fv star_lid ->
      SW.tm_star (interpret_vprop_constructors env l)
                 (interpret_vprop_constructors env r)

    | S.Tm_fvar fv, [(l, _)]
      when S.fv_eq_lid fv pure_lid ->
      SW.tm_pure (SW.tm_expr l)

    | S.Tm_fvar fv, []
      when S.fv_eq_lid fv emp_lid ->
      SW.tm_emp
      
    | _ -> SW.tm_expr v
  
let rec desugar_vprop (env:env) (v:Sugar.vprop)
  : SW.vprop
  = match v with
    | Sugar.VPropTerm t -> 
      let t = ToSyntax.desugar_term env.dsenv t in
      interpret_vprop_constructors env t
    | Sugar.VPropExists { binders; body } ->
      let rec aux env binders =
        match binders with
        | [] -> desugar_vprop env body
        | (_, i, t)::bs ->
          let t = desugar_term env t in
          let env, bv = push_bv env i in
          let body = SW.close_term (aux env bs) bv.index in
          let b = SW.mk_binder i t in
          SW.tm_exists b body
      in
      aux env binders
  
(* s has already been transformed with explicit dereferences for r-values *)
let rec desugar_stmt (env:env) (s:Sugar.stmt)
  : SW.st_term
  = let open SW in
    let open Sugar in
    match s.s with
    | Expr { e } -> 
      let tm = ToSyntax.desugar_term env.dsenv e in
      tm_return (tm_expr tm)

    | Assignment { id; value } ->
      let lhs = resolve_name env id in
      let value = ToSyntax.desugar_term env.dsenv value in
      stapp_assignment lhs value

    | Sequence { s1={s=LetBinding lb}; s2 } ->
      desugar_bind env lb s2

    | Sequence { s1; s2 } -> 
      desugar_sequence env s1 s2
      
    | Block { stmt } ->
      desugar_stmt env stmt

    | If { head; join_vprop; then_; else_opt } -> 
      let head = desugar_term env head in
      let join_vprop =
        match join_vprop with
        | None -> None
        | Some t -> 
          Some (desugar_vprop env t)
      in
      let then_ = desugar_stmt env then_ in
      let else_ = 
        match else_opt with
        | None -> 
          tm_return (tm_expr S.unit_const)
      in
      SW.tm_if head join_vprop then_ else_

    | Match { head; returns_annot; branches } ->
      failwith "Match is not yet handled"

    | While { head; id; invariant; body } ->
      let head = stapp_or_return env (ToSyntax.desugar_term env.dsenv head) in
      let invariant = 
        let env, bv = push_bv env id in
        SW.close_term (desugar_vprop env invariant) bv.index
      in
      let body = desugar_stmt env body in
      SW.tm_while head (id, invariant) body
      
    | LetBinding _ -> 
      failwith "Terminal let binding"

and desugar_bind (env:env) (lb:_) (s2:Sugar.stmt) 
  : SW.st_term
  = let open Sugar in
    let annot = desugar_term_opt env lb.typ in
    let s2 = 
      let env, bv = push_bv env lb.id in        
      SW.close_st_term (desugar_stmt env s2) bv.index
    in        
    match lb.init with
    | None ->
      failwith "Uninitialized variables are not yet handled"

    | Some e1 -> (
      match lb.qualifier with
      | None -> //just a regular bind
        let s1 = stapp_or_return env (ToSyntax.desugar_term env.dsenv e1) in
        SW.tm_bind (Some (lb.id, annot)) s1 s2
      
      | Some MUT //these are handled the same for now
      | Some REF -> 
        let e1 = desugar_term env e1 in 
        SW.tm_let_mut lb.id annot e1 s2
    )

and desugar_sequence (env:env) (s1 s2:Sugar.stmt)
  : SW.st_term
  = let s1 = desugar_stmt env s1 in
    let s2 = desugar_stmt env s2 in
    SW.tm_bind None s1 s2

let explicit_rvalues (env:env) (s:Sugar.stmt)
  : Sugar.stmt
  = s
  
let desugar_decl (env:env) (p:Sugar.decl)
  : ML SW.st_term
  = admit()
