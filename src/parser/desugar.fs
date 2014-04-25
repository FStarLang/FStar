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
#light "off"
module Microsoft.FStar.Parser.Desugar

open Microsoft.FStar
open Microsoft.FStar.Parser
open Microsoft.FStar.Range
open Microsoft.FStar.Parser.AST
open Microsoft.FStar.Parser.DesugarEnv
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util

let tpos = function 
  | Typ_meta (Meta_pos(t,r)) -> r
  | Typ_btvar btv -> btv.v.ppname.idRange
  | Typ_const l -> range_of_lid l.v
  | _ -> failwith "Missing position info"

let kind_star r = mk_term (Name (lid_of_path ["Type"] r)) r Kind

let mk_app e args =
  List.fold_left
    (fun e -> function
      | Inl t, imp -> 
        if imp then raise (Error ("Type applications at the term level are implicit by default; remove the '#' qualifier here", tpos t))
        else ewithpos (Exp_tapp(e, t)) (Range.union_ranges e.p (tpos t))
      | Inr e', imp -> 
        ewithpos (Exp_app(e, e', imp)) (Range.union_ranges e.p e'.p))
    e args 
    
let mk_tapp t args =
  List.fold_left
    (fun t -> function
      | Inl t', imp -> 
        Typ_meta (Meta_pos(Typ_app(t, t',imp), Range.union_ranges (tpos t) (tpos t')))
      | Inr e, imp -> 
        Typ_meta (Meta_pos(Typ_dep(t, e, imp), Range.union_ranges (tpos t) e.p)))
    t args 

let op_as_vlid (env:env) arity r s =
  let r l = Some <| set_lid_range l r in
  match s, env.phase with
    | "=", _ ->    r Const.op_Eq
    | ":=", _ ->   r Const.op_ColonEq
    | "<", _ ->    r Const.op_LT
    | "<=", _ ->   r Const.op_LTE
    | ">", _ ->    r Const.op_GT
    | ">=", _ ->   r Const.op_GTE
    | "&&", _ ->   r Const.op_And
    | "||", _ ->   r Const.op_Or
    | "*", Expr -> r Const.op_Multiply
    | "*", _ ->    r Const.mul_lid
    | "+", Expr -> r Const.op_Addition
    | "+", _ ->    r Const.add_lid
    | "-", Expr when (arity=1) -> r Const.op_Minus
    | "-", _ when (arity=1) -> r Const.minus_lid
    | "-", Expr -> r Const.op_Subtraction
    | "-", _ ->    r Const.sub_lid
    | "/", Expr -> r Const.op_Division
    | "/", _ ->    r Const.div_lid
    | "%", Expr -> r Const.op_Modulus
    | "%", _ ->    r Const.modulo_lid
    | "!", _ ->    r Const.read_lid
    | "@", _ ->    r Const.list_append_lid
    | "^", _ ->    r Const.string_concat_lid
    | "|>", _ ->   r Const.pipe_right_lid
    | "<|", _ ->   r Const.pipe_left_lid
    | "<>", _ ->   r Const.op_notEq
    | _ -> None

let op_as_tylid r s =
  let r l = Some <| set_lid_range l r in
  match s with
    | "=" ->    r Const.eq2_lid
    | "<>" ->   r Const.neq2_lid
    | "<" ->    r Const.lt_lid
    | "<=" ->   r Const.lte_lid
    | ">" ->    r Const.gt_lid
    | ">=" ->   r Const.gte_lid
    | "/\\" ->  r Const.and_lid
    | "\\/" ->  r Const.or_lid
    | "==>" ->  r Const.implies_lid
    | "<==>" -> r Const.iff_lid
    | _ -> None

let rec is_type env (t:term) =
  if t.level = Type then true
  else match t.term with
    | Wild -> true
    | Op("*", hd::_)                    (* tuple constructor *)
    | Op("=", hd::_) -> is_type env hd  (* equality predicate *)
    | Op("<", _)
    | Op("<=", _)
    | Op(">", _)
    | Op(">=", _) -> env.phase = Formula
    | Op(s, _) -> (match op_as_tylid t.range s with
        | None -> false
        | _ -> true)
    | QForall _
    | QExists _
    | Sum _
    | Refine _
    | Tvar _ -> true
    | Var l
    | Name l
    | Construct(l, _) -> is_type_lid env l
    | Abs(_, t)
    | App(t, _, _)
    | Paren t
    | Ascribed(t, _)
    | Product(_, t)  -> is_type env t
    | _ -> false

let rec is_kind (t:term) : bool =
  if t.level = Kind
  then true
  else match t.term with
    | Name {str="Type"} -> true
    | Product(_, t) -> is_kind t
    | Paren t -> is_kind t
    | _ -> false

let rec is_type_binder env b =
  if b.level = Formula
  then match b.binder with
    | Variable _
    | Annotated _ -> false
    | TAnnotated _
    | TVariable _ -> true
    | NoName t -> is_kind  t
  else match b.binder with
    | Variable _ -> raise (Error("Unexpected binder without annotation", b.range))
    | TVariable _ -> false
    | TAnnotated _ -> true
    | Annotated (_, t)
    | NoName t -> is_kind t

let sort_ftv ftv =
  Util.sort_with (fun x y -> String.compare x.idText y.idText) <|
      Util.remove_dups (fun x y -> x.idText = y.idText) ftv

let rec free_type_vars_b env binder = match binder.binder with
  | Variable x -> env, []
  | TVariable x ->
    let env, _ = push_local_tbinding env x in
    (env, [x])
  | Annotated(id, term) ->
    (env, free_type_vars env term)
  | TAnnotated(id, term) ->
    let env, _ = push_local_tbinding env id in
    (env, [])
  | NoName t ->
    (env, free_type_vars env t)
and free_type_vars env t = match t.term with
  | Tvar a ->
    (match DesugarEnv.try_lookup_typ_var env a with
      | None -> [a]
      | _ -> [])

  | Wild
  | Const _
  | Var  _
  | Name _  -> []

  | Paren t
  | Ascribed(t, _) -> free_type_vars env t

  | Construct(_, ts) -> List.collect (fun (t, _) -> free_type_vars env t) ts

  | Op(_, ts) -> List.collect (free_type_vars env) ts

  | App(t1,t2,_) -> free_type_vars env t1@free_type_vars env t2

  | Refine (b, t) ->
    let env, f = free_type_vars_b env b in
    f@free_type_vars env t
      
  | Product(binders, body)
  | Sum(binders, body) ->
    let env, free = List.fold_left (fun (env, free) binder ->
      let env, f = free_type_vars_b env binder in
      env, f@free) (env, []) binders in
    free@free_type_vars env body

  | Abs _  (* not closing implicitly over free vars in type-level functions *)
  | If _
  | QForall _
  | QExists _ -> [] (* not closing implicitly over free vars in formulas *)
  | Let _
  | Affine _
  | Project  _
  | Record _
  | Match _
  | TryWith _
  | Seq _ -> error "Unexpected type in free_type_vars computation" t t.range
    
let close env t =
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, kind_star x.idRange)) x.idRange Type false) in
       let result = mk_term (Product(binders, t)) t.range t.level in
       result
         
let rec is_app_pattern p = match p.pattern with
  | PatAscribed(p,_) -> is_app_pattern p
  | PatApp({pattern=PatVar id}, _) -> true
  | _ -> false

let rec destruct_app_pattern env is_top_level p = match p.pattern with
  | PatAscribed(p,t) ->
    let (name, args, _) = destruct_app_pattern env is_top_level p in
    (name, args, Some t)
  | PatApp({pattern=PatVar id}, args) when is_top_level ->
    (Inr (qualify env id), args, None)
  | PatApp({pattern=PatVar id}, args) ->
    (Inl id, args, None)
  | _ ->
    failwith "Not an app pattern"

type bnd = 
  | TBinder of btvdef * kind
  | VBinder of bvvdef * typ
  | LetBinder of lident * typ

let rec desugar_data_pat env (p:pattern) : (env * bnd * Syntax.pat) =
  match p.pattern with
    | PatOr [] -> failwith "impossible"
    | PatOr (p::ps) ->
      let env0 = env in
      let q = p in
      let env, var, p = desugar_data_pat env p in
      let ps = List.map (fun p ->
        let _, _, p = desugar_data_pat env0 p in
        p) ps in
      let pat = Pat_disj (p::ps) in
      ignore (check_pat_vars q.range pat);
      env, var, pat

    | PatAscribed(p, t) ->
      let (env, binder, p) = desugar_data_pat env p in
      let binder = match binder with
        | LetBinder _ -> failwith "impossible"
        | TBinder (x, _) -> TBinder(x, desugar_kind env t)
        | VBinder (x, _) -> VBinder(x, desugar_typ env t) in
      (env, binder, p)

    | PatTvar a ->
      if a.idText = "'_"
      then (env, TBinder(new_bvd (Some p.range), Kind_unknown), Pat_twild)
      else let env, abvd = push_local_tbinding env a in
           (env, TBinder(abvd, Kind_unknown), Pat_tvar abvd)

    | PatWild ->
      let x = new_bvd (Some p.range) in
      (env, VBinder(x, Typ_unknown), Pat_wild)
        
    | PatConst c ->
      let x = new_bvd (Some p.range) in
      (env, VBinder(x, Typ_unknown), Pat_constant c)

    | PatVar x ->
      let env, xbvd = push_local_vbinding env x in
      (env, VBinder(xbvd, Typ_unknown), Pat_var xbvd)

    | PatName l ->
      let _ = fail_or (try_lookup_datacon env) l in
      let x = new_bvd (Some p.range) in
      (env, VBinder(x, Typ_unknown), Pat_cons(l, []))

    | PatApp({pattern=PatName l}, args) ->
      let (env, args) = List.fold_right (fun arg (env,args) ->
        let (env, _, arg) = desugar_data_pat env arg in
        (env, arg::args)) args (env, []) in
      let _ = fail_or (try_lookup_datacon env) l in
      let x = new_bvd (Some p.range) in
      (env, VBinder(x, Typ_unknown), Pat_cons(l, args))

    | PatApp _ -> raise (Error ("Unexpected pattern", p.range))

    | PatList pats ->
      let (env,pats) = List.fold_right (fun pat (env, pats) ->
        let (env,_,pat) = desugar_data_pat env pat in
        (env, pat::pats)) pats (env, []) in
      let pat = List.fold_right (fun hd tl -> Pat_cons(Const.cons_lid, [hd;tl])) pats (Pat_cons(Const.nil_lid, [])) in
      let x = new_bvd (Some p.range) in
      (env, VBinder(x, Typ_unknown), pat)
        
    | PatTuple(args) ->
      let env, args = List.fold_left (fun (env, pats) p ->
        let env, _, pat = desugar_data_pat env p in
        (env, pat::pats)) (env,[]) args in
      let args = List.rev args in
      let constr = fail_or (DesugarEnv.try_lookup_lid env) (lid_of_path [Util.strcat "MkTuple" (Util.string_of_int <| List.length args)] p.range) in
      let l = match constr.v with
        | Exp_fvar (v, _) -> v.v
        | _ -> failwith "impossible" in
      let x = new_bvd (Some p.range) in
      (env, VBinder(x, Typ_unknown), Pat_cons(l, args))

    | PatRecord ([]) -> 
      raise (Error ("Unexpected pattern", p.range))
        
    | PatRecord (fields) -> 
      let (f, _) = List.hd fields in 
      let record, _ = fail_or (try_lookup_record_by_field_name env) f in
      let fields = fields |> List.map (fun (f, p) -> 
        (fail_or (qualify_field_to_record env record) f, p)) in
      let args = record.fields |> List.map (fun (f, _) -> 
        match fields |> List.tryFind (fun (g, _) -> lid_equals f g) with 
          | None -> mk_pattern PatWild p.range
          | Some (_, p) -> p) in 
      let app = mk_pattern (PatApp(mk_pattern (PatName record.constrname) p.range, args)) p.range in
      desugar_data_pat env app
         
and desugar_binding_pat_maybe_top top env pat : (env * bnd * option<pat>) =
  if top 
  then match pat.pattern with 
    | PatVar x -> (env, LetBinder(qualify env x, Typ_unknown), None)
    | PatAscribed({pattern=PatVar x}, t) -> 
      (env, LetBinder(qualify env x, desugar_typ env t), None)
    | _ -> raise (Error("Unexpected pattern at the top-level", pat.range)) 
  else
    let (env, binder, pat) = desugar_data_pat env pat in
    let pat = match pat with
      | Pat_var _
      | Pat_tvar _ -> None
      | _ -> Some pat in
    (env, binder, pat)

and desugar_binding_pat env = desugar_binding_pat_maybe_top false env

and desugar_match_pat_maybe_top top env pat =
  let (env, binder, pat) = desugar_data_pat env pat in
  (env, pat)

and desugar_match_pat env = desugar_match_pat_maybe_top false env 

and desugar_typ_or_exp (env:env) (t:term) : either<typ,exp> =
  if is_type env t
  then Inl <| desugar_typ env t
  else Inr <| desugar_exp env t

and desugar_exp env e = desugar_exp_maybe_top false env e 

and desugar_exp_maybe_top (top_level:bool) (env:env) (top:term) : exp =
  let pos e = ewithpos e top.range in
  begin match top.term with
    | Const c -> pos <| Exp_constant c

    | Op(s, args) ->
      begin match op_as_vlid env (List.length args) top.range s with
        | None -> raise (Error("Unexpected operator: " ^ s, top.range))
        | Some l ->
          let op = fvar l (range_of_lid l) in
          let args = args |> List.map (fun t -> desugar_typ_or_exp env t, false) in
          mk_app op args
      end

    | Var l
    | Name l -> fail_or (DesugarEnv.try_lookup_lid env) l

    | Construct(l, args) ->
      let dt = pos <| Exp_fvar(fail_or (DesugarEnv.try_lookup_datacon env) l, true) in
      let args = List.map (fun (t, imp) -> desugar_typ_or_exp env t, imp) args in
      mk_app dt args 

    | Abs(binders, body) ->
      let ftv = List.fold_left (fun ftvs pat ->
        match pat.pattern with
          | PatAscribed(_, t) -> free_type_vars env t@ftvs
          | _ -> ftvs) [] binders in
      let ftv = sort_ftv ftv in
      let binders = (ftv |> List.map (fun a -> mk_pattern (PatTvar a) top.range))@binders in
      let rec desugar_abs env a = match a.term with
        | Abs((p::q::qtl), body) ->
          let rest = q::qtl in
          desugar_abs env
            (mk_term (Abs([p], mk_term (Abs(rest, body)) (Range.union_ranges q.range body.range) Expr))
               top.range Expr)
            
        | Abs([p], body) ->
          let env, binder, pat = desugar_binding_pat env p in
          begin match binder with
            | LetBinder _ -> failwith "impossible"
            | TBinder (a, k) ->
              let body = desugar_abs env body in
              pos <| Exp_tabs(a, k, body)
            | VBinder (x, t) ->
              let body = desugar_exp env body in
              let body = match pat with
                | None -> body
                | Some pat -> ewithpos (Exp_match(bvd_to_exp x t, [(pat, None, body)])) body.p in
              pos <| Exp_abs(x, t, body)
          end

        | _ -> desugar_exp env a
      in
      desugar_abs env (mk_term (Abs(binders, body)) top.range top.level)
        
    | App({term=Var a}, arg, _) when (lid_equals a Const.assert_lid
                                   || lid_equals a Const.assume_lid) ->
      let phi = desugar_formula env arg in
      pos <| Exp_app(pos <| Exp_tapp(fvar a (range_of_lid a), phi),
                     pos <| Exp_constant(Const_unit), false)

    | App(e, t, imp) ->
      let e = desugar_exp env e in
      let t = desugar_typ_or_exp env t in
      mk_app e [(t,imp)]
        
    | Seq(t1, t2) ->
      desugar_exp env (mk_term (Let(false, [(mk_pattern PatWild t1.range,t1)], t2)) top.range Expr)
        
    | Let(b, ((pat, _snd)::_tl), body) when is_app_pattern pat ->
      let bindings = (pat, _snd)::_tl in
      let funs = bindings |> List.map (fun (p, def) ->
        if not <| is_app_pattern p
        then raise (Error("Only functions may be defined recursively", p.range))
        else (destruct_app_pattern env top_level p, def)) in
      let env', fnames =
        List.fold_left (fun (env, fnames) ((f, _, _), _) ->
          let env, lbname = match f with
            | Inl x -> 
              let env, xx = push_local_vbinding env x in
              env, Inl xx
            | Inr l -> 
              push_rec_binding env (Binding_let l), Inr l in
          env, (lbname::fnames)) (env, []) funs in
      let fnames = List.rev fnames in
      let desugar_one_def env ((_, args, result_t), def) =
        let def = match result_t with
          | None -> def
          | Some t -> mk_term (Ascribed(def, t)) (Range.union_ranges t.range def.range) Expr in
        let def = mk_term (Abs(args, def)) top.range top.level in
        desugar_exp env def in
      let defs = funs |> List.map (desugar_one_def (if b then env' else env)) in
      let lbs = List.map2 (fun lbname def -> (lbname, Typ_unknown, def)) fnames defs in
      let body = desugar_exp env' body in
      pos <| Exp_let((b, lbs), body)
    
    | Let(false, [(pat, t1)], t2) ->
      let t1 = desugar_exp env t1 in
      let env, binder, pat = desugar_binding_pat_maybe_top top_level env pat in
      begin match binder with
        | TBinder _ -> failwith "Unexpected type binder in let"
        | LetBinder(l, t) -> 
          let body = desugar_exp env t2 in
          pos <| Exp_let((false, [(Inr l, t, t1)]), body)
        | VBinder (x,t) ->
          let body = desugar_exp env t2 in
          let body = match pat with
            | None -> body
            | Some pat -> ewithpos (Exp_match(bvd_to_exp x t, [(pat, None, body)])) body.p in
          pos <| Exp_let((false, [(Inl x, t, t1)]), body)
      end

    | If(t1, t2, t3) ->
      pos <| Exp_match(desugar_exp env t1,
                       [(Pat_constant (Const_bool true), None, desugar_exp env t2);
                        (Pat_constant (Const_bool false), None, desugar_exp env t3)])

    | TryWith(e, branches) -> 
      let r = top.range in 
      let handler = mk_function branches r r in 
      let body = mk_function [(mk_pattern (PatConst Const_unit) r, None, e)] r r in 
      let a1 = mk_term (App(mk_term (Var Const.try_with_lid) r top.level, body, false)) r  top.level in 
      let a2 = mk_term (App(a1, handler, false)) r top.level in 
      desugar_exp env a2

    | Match(e, branches) ->
      let desugar_branch (pat, wopt, b) =
        let env, pat = desugar_match_pat env pat in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some <| desugar_exp env e in
        let b = desugar_exp env b in
        (pat, wopt, b) in
      pos <| Exp_match(desugar_exp env e, List.map desugar_branch branches)

    | Ascribed(e, t) ->
      pos <| Exp_ascribed(desugar_exp env e, desugar_typ env t)

    | Record(eopt, []) ->
      raise (Error("Unexpected empty record", top.range))

    | Record(eopt, fields) ->
      let f, _ = List.hd fields in
      let record, _ = fail_or (try_lookup_record_by_field_name env) f in
      let get_field xopt f =
        let fn = f.ident in
        let found = fields |> Util.find_opt (fun (g, _) ->
          let gn = g.ident in
          fn.idText = fn.idText) in
        match found with
          | Some (_, e) -> e
          | None ->
            match xopt with
              | None ->
                raise (Error (Util.format1 "Field %s is missing" (text_of_lid f), top.range))
              | Some x ->
                mk_term (Project(x, f)) x.range x.level in
      let recterm = match eopt with
        | None ->
          Construct(record.constrname,
                    record.fields |> List.map (fun (f, _) ->
                      get_field None f, false))
            
        | Some e ->
          let x = genident (Some e.range) in
          let xterm = mk_term (Var (lid_of_ids [x])) x.idRange Expr in
          let record = Construct(record.constrname,
                                 record.fields |> List.map (fun (f, _) ->
                                    get_field (Some xterm) f, false)) in
          Let(false, [(mk_pattern (PatVar x) x.idRange, e)], mk_term record top.range top.level) in
      let recterm = mk_term recterm top.range top.level in
      desugar_exp env recterm
        
    | Project(e, f) ->
      (* let _ = Util.print_string (Util.format1 "Looking up field name %s\n" (Print.sli f)) in *)
      let _, fieldname = fail_or (try_lookup_record_by_field_name env) f in
      (* let _ = Util.print_string (Util.format2 "resolved %s as %s\n" (Print.sli f) (Print.sli fieldname)) in *)
      let proj = mk_term (App(mk_term (Var fieldname) (range_of_lid f) Expr, e, false)) top.range top.level in
      desugar_exp env proj

    | Paren e ->
      desugar_exp env e

    | _ ->
      error "Unexpected term" top top.range
  end
  
and desugar_typ env (top:term) : typ =
  let pos t = Typ_meta (Meta_pos(t, top.range)) in
  match top.term with
    | Wild -> pos <| Typ_unknown

    | Op("*", [t1;t2]) when is_type env t1 ->
      desugar_typ env (mk_term (Sum([mk_binder (NoName t1) t1.range Type false], t2)) top.range top.level)
      
    | Op("<>", args) ->
      let t = desugar_typ env (mk_term (Op("=", args)) top.range top.level) in
      pos <| Typ_app(ftv <| set_lid_range Const.not_lid top.range, t, false)

    | Op(s, args) ->
      begin match op_as_tylid top.range s with
        | None -> raise (Error("Unrecognized type operator: " ^ s, top.range))
        | Some l ->
          let args = List.map (fun t -> desugar_typ_or_exp env t, false) args in
          mk_tapp (ftv l) args
      end

    | Tvar a ->
      pos <| fail_or2 (try_lookup_typ_var env) a
          
    | Var l
    | Name l ->
      pos <| fail_or (try_lookup_typ_name env) l
      
    | Construct(l, args) ->
      let t = fail_or (try_lookup_typ_name env) l in
      let args = List.map (fun (t, imp) -> desugar_typ_or_exp env t, imp) args in
      mk_tapp t args

    | Abs(p::(q::_rest), body) ->
      let rest = q::_rest in
      let body = mk_term (Abs(rest, body)) (Range.union_ranges q.range body.range) top.level in
      let t = mk_term (Abs([p], body)) top.range top.level in
      desugar_typ env t

    | Abs([p], body) ->
      let env, binder, pat = desugar_binding_pat env p in
      begin match pat with
        | Some _ -> raise (Error("Pattern matching at the type level is not supported", p.range))
        | None ->
          let body = desugar_typ env body in
          match binder with
            | LetBinder _ -> failwith "impossible"
            | TBinder (a,k) -> pos <| Typ_tlam(a, k, body)
            | VBinder (x,t) -> pos <| Typ_lam(x, t, body)
      end

    | App(t1, t2, imp) ->
      let t1 = desugar_typ env t1 in
      let t2 = desugar_typ_or_exp env t2 in
      mk_tapp t1 [(t2,imp)]
        
    | Product([], t) ->
      desugar_typ env t
      
    | Product(b::(_bs::_bstl), t) ->
      let bs = _bs::_bstl in
      desugar_typ env (mk_term (Product([b], mk_term (Product(bs, t)) top.range top.level)) top.range top.level)

    | Product([b], t) ->
      let tk = desugar_binder env b in
      let p = match tk with
        | Inl(None, k) ->
          let x = new_bvd (Some b.range) in
          Typ_univ(x, k, desugar_typ env t)

        | Inl(Some x, k) ->
          let env, x = push_local_tbinding env x in
          Typ_univ(x, k, desugar_typ env t)

        | Inr(None, t1) ->
          Typ_fun(None, t1, desugar_typ env t, b.implicit)

        | Inr(Some x, t1) ->
          let env, x = push_local_vbinding env x in
          Typ_fun(Some x, t1, desugar_typ env t, b.implicit) in
      pos p

    | Refine(b,f) ->
      begin match desugar_exp_binder env b with
        | (None, _) -> failwith "Missing binder in refinement"
        | (Some x, t) ->
          let env, x = push_local_vbinding env x in
          let f = desugar_formula env f in
          pos <| Typ_refine(x, t, f)
      end

    | Paren t ->
      desugar_typ env t

    | Ascribed(t,k) ->
      pos <| Typ_ascribed(desugar_typ env t, desugar_kind env k)

    | Sum(binders, t) ->
      let env, _, targs = List.fold_left (fun (env, tparams, typs) b ->
        let xopt, t = desugar_exp_binder env b in
        let env, x = match xopt with
          | None -> env, new_bvd (Some top.range)
          | Some x -> push_local_vbinding env x in
        (env, tparams@[Tparam_term(x, t)], typs@[close_with_lam tparams t]))
        (env, [], []) (binders@[mk_binder (NoName t) t.range Type false]) in
      let tup = fail_or (try_lookup_typ_name env) (lid_of_path [Util.strcat "Tuple" (Util.string_of_int <| List.length targs)] top.range) in
      pos <| List.fold_left (fun t1 t2 -> Typ_app(t1,t2,false)) tup targs
          
    | Record _ -> failwith "Unexpected record type"

    | _ -> error "Expected a type" top top.range

and desugar_kind env k : kind =
  match k.term with
    | Name {str="Type"} -> Kind_star
    | Wild           -> Kind_unknown
    | Product([b], t) ->
      let tk = desugar_binder env b in
      begin match tk with
        | Inl(None, k) ->
          Kind_tcon(None, k, desugar_kind env t, b.implicit)

        | Inl(Some a, k) ->
          let env, a = push_local_tbinding env a in
          Kind_tcon(Some a, k, desugar_kind env t, b.implicit)

        | Inr(None, t0) ->
          Kind_dcon(None, t0, desugar_kind env t, b.implicit)

        | Inr(Some x, t0) ->
          let env, x = push_local_vbinding env x in
          Kind_dcon(Some x, t0, desugar_kind env t, b.implicit)
      end
    | _ -> error "Unexpected term where kind was expected" k k.range

and desugar_formula' env (f:term) : typ =
  let connective s = match s with
    | "/\\"  -> Some Const.and_lid
    | "\\/"  -> Some Const.or_lid
    | "==>"  -> Some Const.implies_lid
    | "<==>" -> Some Const.iff_lid
    | _ -> None in
  let pos t = Typ_meta (Meta_pos(t, f.range)) in
  let desugar_quant (q:lident) (qt:lident) b pats body =
    let tk = desugar_binder env ({b with level=Formula}) in
    match tk with
      | Inl(Some a,k) ->
        let env, a = push_local_tbinding env a in
        let pats = List.map (desugar_typ_or_exp env) pats in
        let body = desugar_formula env body in
        let body = match pats with
          | [] -> body
          | _ -> Typ_meta (Meta_pattern(body, pats)) in
        let body = pos <| Typ_tlam(a, k, body) in
        pos <| mk_tapp (ftv (set_lid_range qt b.range)) [Inl body, false]
            
      | Inr(Some x,t) ->
        let env, x = push_local_vbinding env x in
        let pats = List.map (desugar_typ_or_exp env) pats in
        let body = desugar_formula env body in
        let body = match pats with
          | [] -> body
          | _ -> Typ_meta (Meta_pattern(body, pats)) in
        let body = pos <| Typ_lam(x, t, body) in
        pos <| mk_tapp (ftv (set_lid_range q b.range)) [Inl body, false]

      | _ -> failwith "impossible" in
            
  let push_quant q (binders:binder list) pats (body:term) = match binders with
    | b::(b'::_rest) ->
      let rest = b'::_rest in
      let body = mk_term (q(rest, pats, body)) (Range.union_ranges b'.range body.range) Formula in
      mk_term (q([b], [], body)) f.range Formula
    | _ -> failwith "impossible" in

  match f.term with
    | Op("=", ((hd::_args))) ->
      let args = hd::_args in
      let args = List.map (fun t -> desugar_typ_or_exp env t, false) args in
      let eq =
        if is_type env hd
        then ftv (set_lid_range Const.eqTyp_lid f.range)
        else ftv (set_lid_range Const.eq2_lid f.range) in
      mk_tapp eq args

    | Op(s, args) ->
      begin match connective s, args with
        | Some conn, [_;_] ->
          mk_tapp
            (ftv (set_lid_range conn f.range))
            (List.map (fun x -> Inl <| desugar_formula env x, false) args)
        | _ -> desugar_typ env f
      end

    | App({term=Var l}, arg, imp) when (l.str = "not") ->
      let arg = desugar_formula env arg in
      mk_tapp (ftv (set_lid_range Const.not_lid f.range)) [Inl arg, imp]
        
    | If(f1, f2, f3) ->
      mk_tapp
        (ftv (set_lid_range Const.ite_lid f.range))
        (List.map (fun x -> Inl <| desugar_typ env x, false) [f1;f2;f3])

    | QForall((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant QForall binders pats body)

    | QExists((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant QExists binders pats body)
        
    | QForall([b], pats, body) ->
      desugar_quant Const.forall_lid Const.allTyp_lid b pats body

    | QExists([b], pats, body) ->
      desugar_quant Const.exists_lid Const.allTyp_lid b pats body

    | Paren f ->
      desugar_formula env f

    | _ when is_type env f ->
      desugar_typ env f

    | _ ->
      error "Expected a formula" f f.range

and desugar_formula env t =
  desugar_formula' ({env with phase=Formula}) t

and desugar_binder env b =
  if is_type_binder env b
  then Inl (desugar_type_binder env b)
  else Inr (desugar_exp_binder env b)

and typars_of_binders env bs =
    let env, tpars = List.fold_left (fun (env, out) b ->
        let tk = desugar_binder env ({b with level=Formula}) in  (* typars follow the same binding conventions as formulas *)
        match tk with
            | Inl(Some a,k) ->
                let env, a = push_local_tbinding env a in
                (env, Tparam_typ(a,k)::out)
            | Inr(Some x,t) ->
                let env, x = push_local_vbinding env x in
                (env, Tparam_term(x,t)::out)
            | _ -> raise (Error ("Unexpected binder", b.range))) (env, []) bs in
    env, List.rev tpars

and desugar_exp_binder env b = match b.binder with
  | Annotated(x, t) -> Some x, desugar_typ env t
  | TVariable t -> None, fail_or2 (try_lookup_typ_var env) t
  | NoName t -> None, desugar_typ env t
  | Variable x -> Some x, Typ_unknown
  | _ -> raise (Error("Unexpected domain of an arrow or sum (expected a type)", b.range))
    
and desugar_type_binder env b = match b.binder with
  | TAnnotated(x, t) -> Some x, desugar_kind env t
  | NoName t -> None, desugar_kind env t
  | TVariable x -> Some x, Kind_star
  | _ -> raise (Error("Unexpected domain of an arrow or sum (expected a kind)", b.range))

let logic_tag = function
  | LogicTag l -> [l]
  | _ -> []

let logic_tags q = List.collect logic_tag q

let mk_data_ops env = function
  | Sig_datacon(lid, t, _) ->
    let args, tconstr = collect_formals t in
    //Printf.printf "Collecting formals from type %s; got %s with args %d\n" (Print.typ_to_string t) (Print.typ_to_string tconstr) (List.length args);
    let argpats = args |> List.map (function
      | Inr(Some x,_) -> Pat_var x
      | Inr(None,targ) -> Pat_var (new_bvd (Some (range_of_lid lid)))
      | Inl(a,_) -> Pat_tvar a) in
    let freetv, freexv  = freevars_typ tconstr in
    let freevars = args |> List.filter (function
      | Inl(a,k) -> freetv |> Util.for_some (fun b -> Util.bvd_eq a b.v)
      | Inr(Some x,t) -> freexv |> Util.for_some (fun y -> Util.bvd_eq x y.v)
      | _ -> false) in
    //Printf.printf "Got %d free vars\n" (List.length freevars);
    let freeterms = freevars |> List.map (function 
      | Inl (a, k) -> Inl (Util.bvd_to_typ a k), false
      | Inr (Some x, t) -> Inr (Util.bvd_to_exp x t), false
      | _ -> failwith "impossible") in
    let formal = new_bvd (Some <| range_of_lid lid) in
    let formal_exp = bvd_to_exp formal tconstr in
    let rec build_exp freevars e = match freevars with
      | Inl (a,k)::rest -> ewithpos (Exp_tabs(a, k, build_exp rest e)) e.p
      | Inr (Some x, t)::rest -> ewithpos (Exp_abs(x, t, build_exp rest e)) e.p
      | _::rest -> failwith "impossible"
      | [] -> ewithpos (Exp_abs(formal, tconstr, e)) e.p in
    let rec build_typ freevars t = match freevars with
      | Inl (a,k)::rest -> Typ_univ(a, k, build_typ rest t)
      | Inr (xopt,tt)::rest -> Typ_fun(xopt, tt, build_typ rest t, false)
      | [] -> Typ_fun(Some formal, tconstr, t, false) in
    let rec build_kind freevars k = match freevars with
      | Inl (a,kk)::rest -> Kind_tcon(Some a, kk, build_kind rest k, false)
      | Inr (xopt,t)::rest -> Kind_dcon(xopt, t, build_kind rest k, false)
      | [] -> Kind_dcon(Some formal, tconstr, k, false) in
    let build_exp  = build_exp freevars in
    let build_typ  = build_typ freevars in
    let build_kind = build_kind freevars in
    let subst_to_string s = 
      List.map (function 
        | Inl (a, t) -> Util.format2 "(%s -> %s)" (Print.strBvd a) (Print.typ_to_string t)  
        | Inr (x, e) -> Util.format2 "(%s -> %s)" (Print.strBvd x) (Print.exp_to_string e)) s 
      |> String.concat ", " in  
    let subst_typ s t =
      //Printf.printf "Substituting [%s] in type\n%s\n" (subst_to_string s) (Print.typ_to_string t);
      let res = subst_typ s t in  res in
      //Printf.printf "Got\n%s\n" (Print.typ_to_string res); flush stdout; res in
    let rec aux fields t = match compress_typ t with
      | Typ_fun(Some x, t1, t2, _) ->
        let field_name = lid_of_ids (ids_of_lid lid @ [x.ppname]) in
        let t = build_typ t1 in
        let body = ewithpos (Exp_match(formal_exp, [(Pat_cons(lid, argpats), None, bvd_to_exp x t1)])) x.ppname.idRange in
        let sigs =
          [Sig_val_decl(field_name, t, Some Assumption)
           //;Sig_let((false, [(Inr field_name, t, build_exp body)]))
          ] in
        //let _ = Util.print_string (Util.format2 "adding value projector %s at type %s\n" field_name.str (Print.typ_to_string t)) in 
        let t2 = 
          if freexv |> Util.for_some (fun y -> Util.bvd_eq x y.v)
          then t2
          else 
            let subst = [Inr(x, mk_app (fvar field_name (range_of_lid field_name)) (freeterms@[Inr formal_exp, false]))] in
            subst_typ subst t2 in
        aux (fields@sigs) t2
          
      | Typ_univ(a, k, t2) ->
        let field_name = lid_of_ids (ids_of_lid lid @ [a.ppname]) in
        let kk = build_kind k in
        let sigs = Sig_tycon(field_name, [], kk, [], [], [Logic_projector]) in
        //let _ = Util.print_string (Util.format2 "adding type projector %s at type %s\n" field_name.str (Print.kind_to_string kk)) in 
        let t2 = 
          if freetv |> Util.for_some (fun b -> Util.bvd_eq b.v a)
          then t2
          else let subst = [Inl(a, mk_tapp (ftv field_name) (freeterms@[Inr formal_exp, false]))] in
               subst_typ subst t2 in
        aux (fields@[sigs]) t2

      | _ -> fields in
    
    aux [] t
  | _ -> []

let rec desugar_tycon env quals tcs : (env * sigelts) =
  let tycon_id = function
    | TyconAbstract(id, _, _)
    | TyconAbbrev(id, _, _, _)
    | TyconRecord(id, _, _, _)
    | TyconVariant(id, _, _, _) -> id in
  let binder_to_term b = match b.binder with
    | Annotated (x, _)
    | Variable x -> mk_term (Var (lid_of_ids [x])) x.idRange Expr
    | TAnnotated(a, _)
    | TVariable a -> mk_term (Tvar a) a.idRange Type
    | NoName t -> t in
  let apply_binders t binders =
    List.fold_left (fun out b -> mk_term (App(out, binder_to_term b, false)) out.range out.level)
      t binders in
  let tycon_record_as_variant = function
    | TyconRecord(id, parms, kopt, fields) ->
      let constrName = mk_ident("Mk" ^ id.idText, id.idRange) in
      let fields = List.map (fun (x,t) -> mk_binder (Annotated(x,t)) x.idRange Expr false) fields in
      let result = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type) parms in
      let constrTyp = mk_term (Product(fields, result)) id.idRange Type in
      (* let _ = Util.print_string (Util.format2 "Translated record %s to constructor %s\n" (id.idText) (term_to_string constrTyp)) in *)
      TyconVariant(id, parms, kopt, [(constrName, constrTyp, false)])
    | _ -> failwith "impossible" in
  let desugar_abstract_tc quals env mutuals = function
    | TyconAbstract(id, binders, kopt) ->
      let env', typars = typars_of_binders env binders in
      let k = match kopt with
        | None -> Kind_unknown
        | Some k -> desugar_kind env' k in
      let tconstr = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type) binders in
      let qlid = qualify env id in
      let se = Sig_tycon(qlid, typars, k, mutuals, [], logic_tags quals) in
      let env = push_rec_binding env (Binding_tycon qlid) in
      let env' = push_rec_binding env' (Binding_tycon qlid) in
      env, (env', typars), se, tconstr
    | _ -> failwith "Unexpected tycon" in
  let push_tparam env = function
    | Tparam_term(x,_) -> push_bvvdef env x
    | Tparam_typ(a,_) -> push_btvdef env a in
  let push_tparams = List.fold_left push_tparam in
  match tcs with
    | [TyconAbstract _] ->
        let tc = List.hd tcs in
        let _, _, se, _ = desugar_abstract_tc quals env [] tc in
        let env = push_sigelt env se in
        (* let _ = pr "Pushed %s\n" (text_of_lid (qualify env (tycon_id tc))) in *)
        env, [se]

    | [TyconAbbrev(id, binders, kopt, t)] ->
        let env', typars = typars_of_binders env binders in
        let k = match kopt with
            | None -> Kind_unknown
            | Some k -> desugar_kind env' k in
        let t = desugar_typ env' t in
        let se = Sig_typ_abbrev(qualify env id, typars, k, t) in
        let env = push_sigelt env se in
        env, [se]

    | [TyconRecord _] ->
      let trec = List.hd tcs in
      desugar_tycon env (LogicTag Logic_record::quals) [tycon_record_as_variant trec]

    |  _::_ ->
      let env0 = env in
      let mutuals = List.map (fun x -> qualify env <| tycon_id x) tcs in
      let rec collect_tcs (env, tcs, quals) tc = match tc with
        | TyconRecord _ ->
          let trec = tc in
          collect_tcs (env, tcs, LogicTag Logic_record::quals) (tycon_record_as_variant trec)
        | TyconVariant(id, binders, kopt, constructors) ->
          let env, (_, tps), se, tconstr = desugar_abstract_tc quals env mutuals (TyconAbstract(id, binders, kopt)) in
          env, Inl(se, tps, constructors, tconstr)::tcs, quals
        | TyconAbbrev(id, binders, kopt, t) ->
          let env, (_, tps), se, tconstr = desugar_abstract_tc quals env mutuals (TyconAbstract(id, binders, kopt)) in
          env, Inr(se, tps, t)::tcs, quals
        | _ -> failwith "Unrecognized mutual type definition" in
      let env, tcs, quals = List.fold_left collect_tcs (env, [], quals) tcs in
      let tcs = List.rev tcs in
      let sigelts = tcs |> List.collect (function
        | Inr(Sig_tycon(id, tpars, k, _, _, _), tps, t) ->
          let env_tps = push_tparams env tps in
          let t = desugar_typ env_tps t in
          [Sig_typ_abbrev(id, tpars, k, t)]
            
        | Inl (Sig_tycon(tname, tpars, k, mutuals, _, tags), tps, constrs, tconstr) ->
          let env_tps = push_tparams env tps in
          let constrNames, constrs = List.split <|
              (constrs |> List.map (fun (id, t, of_notation) ->
                let t =
                  if of_notation
                  then mk_term (Product([mk_binder (NoName t) t.range t.level false], tconstr)) t.range t.level
                  else t in
                let t = desugar_typ env_tps (close env_tps t) in
                let name = qualify env id in
                (name, Sig_datacon(name, close_typ tps t, tname)))) in
              Sig_tycon(tname, tpars, k, mutuals, constrNames, tags)::constrs
        | _ -> failwith "impossible") in
      let bundle = Sig_bundle sigelts in
      let env = push_sigelt env0 bundle in
      let data_ops =
        if logic_tags quals |> Util.for_some (function
          | Logic_data
          | Logic_record -> true
          | _ -> false)
        then sigelts |> List.collect (mk_data_ops env)
        else [] in
      let env = List.fold_left push_sigelt env data_ops in
      env, [bundle]@data_ops

    | [] -> failwith "impossible"
           
let desugar_decl env (d:decl) : (env * sigelts) = match d.decl with
  | Open lid ->
    let env = DesugarEnv.push_namespace env lid in
    env, []
  
  | Tycon(qual, tcs) ->
    desugar_tycon env [qual] tcs
          
  | ToplevelLet(isrec, lets) ->
    begin match desugar_exp_maybe_top true env (mk_term (Let(isrec, lets, mk_term (Const Const_unit) d.range Expr)) d.range Expr) with
        | {v=Exp_let(lbs, _)} ->
          let s = Sig_let lbs in
          let env = push_sigelt env s in
          env, [s]
        | _ -> failwith "Desugaring a let did not produce a let"
    end

  | Main t ->
    let e = desugar_exp env t in
    let se = Sig_main e in
    env, [se]

  | Assume(atag, id, t) ->
    let f = desugar_formula env t in
    env, [Sig_assume(qualify env id, f, Public, Assumption)]

  | Val(LogicTag Logic_val, id, t) ->
    let t = desugar_typ env (close env t) in
    let se = Sig_logic_function(qualify env id, t, []) in
    let env = push_sigelt env se in
    env, [se]

  | Val(AST.Assumption, id, t) -> 
    let t = desugar_typ env (close env t) in
    let se = Sig_val_decl(qualify env id, t, Some Assumption) in
    let env = push_sigelt env se in
    env, [se]

  | Val(NoQual, id, t) ->
    let t = desugar_typ env (close env t) in
    let se = Sig_val_decl(qualify env id, t, None) in
    let env = push_sigelt env se in
    env, [se]
        
  | Exception(id, term) ->
    let t = desugar_typ env term in
    let t = Typ_fun(None, t, fail_or (try_lookup_typ_name env) Const.exn_lid, false) in
    let se = Sig_datacon(qualify env id, t, Const.exn_lid) in
    let env = push_sigelt env se in
    env, [se]

  | _ -> raise (Error("Unexpected declaration", d.range))
        
let desugar_modul env (m:AST.modul) : env * Syntax.modul = match m with
  | Module(mname, decls) ->
    let env = DesugarEnv.prepare_module env mname in
    let env, sigelts = List.fold_left (fun (env, sigelts) d ->
      let env, se = desugar_decl env d in
      env, sigelts@se) (env, []) decls in
    let modul = {
      name = mname;
      declarations = sigelts;
      exports = []
    } in
    let env = DesugarEnv.finish_module env modul in
    env, modul
  
let desugar_file env (pragmas, ms) =
  let env, mods = List.fold_left (fun (env, mods) m ->
    let env, m = desugar_modul env m in
    finish_module env m, m::mods) (env, []) ms in
  env, List.rev mods
