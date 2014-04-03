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

let kind_star r = mk_term (Name (lid_of_path ["S"] r)) r Kind

let mk_app e args =
  List.fold_left
    (fun e -> function
      | Inl t -> 
        ewithpos (Exp_tapp(e, t)) (Range.union_ranges e.p (tpos t))
      | Inr e' -> 
        ewithpos (Exp_app(e, e')) (Range.union_ranges e.p e'.p))
    e args 
     
let mk_tapp t args =
  List.fold_left
    (fun t -> function
      | Inl t' -> 
        Typ_meta (Meta_pos(Typ_app(t, t'), Range.union_ranges (tpos t) (tpos t')))
      | Inr e -> 
        Typ_meta (Meta_pos(Typ_dep(t, e), Range.union_ranges (tpos t) e.p)))
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
    | Op(s, _) -> (match op_as_tylid t.range s with None -> false | _ -> true)
    | QForall _
    | QExists _
    | Sum _
    | Refine _
    | Tvar _ -> true
    | Var l
    | Name l 
    | Construct(l, _) -> is_type_lid env l
    | Abs(_, t)
    | App(t, _) 
    | Paren t 
    | Ascribed(t, _) 
    | Product(_, t)  -> is_type env t
    | _ -> false

let rec is_kind (t:term) : bool = 
  if t.level = Kind 
  then true
  else match t.term with 
    | Name {str="P"}
    | Name {str="S"}
    | Name {str="E"} -> true
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

  | Construct(_, ts) 
  | Op(_, ts) -> List.collect (free_type_vars env) ts

  | App(t1,t2) -> free_type_vars env t1@free_type_vars env t2

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
  | Seq _ -> error "Unexpected type in free_type_vars computation" t t.range 
    
let close env t = 
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0 
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, kind_star x.idRange)) x.idRange Type) in 
       let result = mk_term (Product(binders, t)) t.range t.level in 
    (* let _ = pr "Implicitly closed type at %s to %s\n" (Range.string_of_range result.range) (term_to_string result) in *)
       result
  
let rec is_app_pattern p = match p.pattern with
  | PatAscribed(p,_) -> is_app_pattern p
  | PatApp({pattern=PatVar id}, _) -> true
  | _ -> false

let rec destruct_app_pattern p = match p.pattern with
  | PatAscribed(p,t) -> 
    let (name, args, _) = destruct_app_pattern p in 
    (name, args, Some t)
  | PatApp({pattern=PatVar id}, args) -> 
    (id, args, None)
  | _ -> 
    failwith "Not an app pattern"

let rec desugar_data_pat env (p:pattern) : (env * either<(btvdef*kind), (bvvdef*typ)> * Syntax.pat) = 
  match p.pattern with
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
        | Inl (x, _) -> Inl(x, desugar_kind env t)
        | Inr (x, _) -> Inr(x, desugar_typ env t) in
      (env, binder, p)

    | PatTvar a ->
      if a.idText = "'_"  
      then (env, Inl(new_bvd (Some p.range), Kind_unknown), Pat_twild)
      else let env, abvd = push_local_tbinding env a in
           (env, Inl(abvd, Kind_unknown), Pat_tvar abvd)

    | PatWild -> 
      let x = new_bvd (Some p.range) in
      (env, Inr(x, Typ_unknown), Pat_wild)
        
    | PatConst c -> 
      let x = new_bvd (Some p.range) in
      (env, Inr(x, Typ_unknown), Pat_constant c)

    | PatVar x -> 
      let env, xbvd = push_local_vbinding env x in 
      (env, Inr(xbvd, Typ_unknown), Pat_var xbvd)

    | PatName l -> 
      let _ = fail_or (try_lookup_datacon env) l in
      let x = new_bvd (Some p.range) in
      (env, Inr(x, Typ_unknown), Pat_cons(l, []))

    | PatApp({pattern=PatName l}, args) ->
      let (env, args) = List.fold_right (fun arg (env,args) -> 
        let (env, _, arg) = desugar_data_pat env arg in 
        (env, arg::args)) args (env, []) in 
      let _ = fail_or (try_lookup_datacon env) l in
      let x = new_bvd (Some p.range) in
      (env, Inr(x, Typ_unknown), Pat_cons(l, args))

    | PatApp _ -> raise (Error ("Unexpected pattern", p.range))

    | PatList pats -> 
      let (env,pats) = List.fold_right (fun pat (env, pats) -> 
        let (env,_,pat) = desugar_data_pat env pat in
        (env, pat::pats)) pats (env, []) in
      let pat = List.fold_right (fun hd tl -> Pat_cons(Const.cons_lid, [hd;tl])) pats (Pat_cons(Const.nil_lid, [])) in
      let x = new_bvd (Some p.range) in 
      (env, Inr(x, Typ_unknown), pat)
      
    | PatTuple(args) -> 
      let env, args = List.fold_left (fun (env, pats) p -> 
        let env, _, pat = desugar_data_pat env p in 
        (env, pat::pats)) (env,[]) args in 
      let args = List.rev args in 
      let constr = fail_or (DesugarEnv.try_lookup_lid env) (lid_of_path [Util.strcat "MkTuple" (Util.string_of_int <| List.length args)] p.range) in 
      let l = match constr.v with 
        | Exp_fvar v -> v.v 
        | _ -> raise Impos in 
      let x = new_bvd (Some p.range) in 
      (env, Inr(x, Typ_unknown), Pat_cons(l, args))

    | PatRecord _ -> failwith "NYI" 

and desugar_binding_pat env pat = 
  let (env, binder, pat) = desugar_data_pat env pat in 
  let pat = match pat with 
    | Pat_var _
    | Pat_tvar _ -> None
    | _ -> Some pat in 
  (env, binder, pat)

and desugar_match_pat env pat = 
  let (env, binder, pat) = desugar_data_pat env pat in 
  (env, pat)

and desugar_typ_or_exp (env:env) (t:term) : either<typ,exp> =
  if is_type env t
  then Inl <| desugar_typ env t
  else Inr <| desugar_exp env t

and desugar_exp (env:env) (top:term) : exp = 
  let pos e = ewithpos e top.range in
  begin match top.term with
    | Const c -> pos <| Exp_constant c

    | Op("Tuple", args) -> failwith "NYI"

    | Op(s, args) ->
      begin match op_as_vlid env (List.length args) top.range s with
        | None -> raise (Error("Unexpected operator: " ^ s, top.range))
        | Some l ->
          let op = fvar l (range_of_lid l) in
          let args = args |> List.map (desugar_typ_or_exp env) in
          mk_app op args
      end

    | Var l  
    | Name l -> fail_or (DesugarEnv.try_lookup_lid env) l

    | Construct(l, args) ->
      let dt = fail_or (DesugarEnv.try_lookup_datacon env) l in
      let args = List.map (desugar_typ_or_exp env) args in
      pos <| Exp_constr_app(dt, args)

    | Abs(binders, body) -> 
      let ftv = List.fold_left (fun ftvs pat -> 
        match pat.pattern with
          | PatAscribed(_, t) -> free_type_vars env t@ftvs
          | _ -> ftvs) [] binders in 
      let ftv = sort_ftv ftv in 
      let binders = (ftv |> List.map (fun a -> mk_pattern (PatTvar a) top.range))@binders in 
      let rec desugar_abs env a = match a.term with
        | Abs(p::(q::_ as rest), body) ->
          desugar_abs env  
            (mk_term (Abs([p], mk_term (Abs(rest, body)) (Range.union_ranges q.range body.range) Expr))
               top.range Expr)
        
        | Abs([p], body) ->
          let env, binder, pat = desugar_binding_pat env p in 
          begin match binder with 
            | Inl (a, k) -> 
              let body = desugar_abs env body in 
              pos <| Exp_tabs(a, k, body)
            | Inr (x, t) -> 
              let body = desugar_exp env body in 
              let body = match pat with 
                | None -> body
                | Some pat -> ewithpos (Exp_match(bvd_to_exp x t, [(pat, None, body)])) body.p in
              pos <| Exp_abs(x, t, body)
          end

        | _ -> desugar_exp env a
      in 
      desugar_abs env (mk_term (Abs(binders, body)) top.range top.level)
        
    | App({term=Var a}, arg) when (lid_equals a Const.assert_lid
                                   || lid_equals a Const.assume_lid) ->
      let phi = desugar_formula env arg in
      pos <| Exp_app(pos <| Exp_tapp(fvar a (range_of_lid a), phi),  
                     pos <| Exp_constant(Const_unit))

    | App(e, t) ->
      let e = desugar_exp env e in
      let t = desugar_typ_or_exp env t in
      mk_app e [t]
        
    | Seq(t1, t2) ->
      desugar_exp env (mk_term (Let(false, [(mk_pattern PatWild t1.range,t1)], t2)) top.range Expr)
        
    | Let(b, ((pat, _)::_ as bindings), body) when is_app_pattern pat ->
      let funs = bindings |> List.map (fun (p, def) -> 
        if not <| is_app_pattern p
        then raise (Error("Only functions may be defined recursively", p.range))
        else (destruct_app_pattern p, def)) in 
      let env', fnames = 
        List.fold_left (fun (env, fnames) ((f, _, _), _) -> 
          let env, fbvd = push_local_vbinding env f in
          env, (fbvd::fnames)) (env, []) funs in 
      let fnames = List.rev fnames in
      let desugar_one_def env ((_, args, result_t), def) = 
        let def = match result_t with 
          | None -> def 
          | Some t -> mk_term (Ascribed(def, t)) (Range.union_ranges t.range def.range) Expr in
        let def = mk_term (Abs(args, def)) top.range top.level in
        desugar_exp env def in
      let defs = funs |> List.map (desugar_one_def (if b then env' else env)) in 
      let lbs = List.map2 (fun fbvd def -> (fbvd, Typ_unknown, def)) fnames defs in
      let body = desugar_exp env' body in 
      pos <| Exp_let(b, lbs, body)
          
    | Let(false, [(pat, t1)], t2) ->
      let t1 = desugar_exp env t1 in
      let env, binder, pat = desugar_binding_pat env pat in
        begin match binder with
          | Inl _ -> failwith "Unexpected type binder in let"
          | Inr (x,t) -> 
            let body = desugar_exp env t2 in
            let body = match pat with 
              | None -> body
              | Some pat -> ewithpos (Exp_match(bvd_to_exp x t, [(pat, None, body)])) body.p in
            pos <| Exp_let(false, [(x, t, t1)], body)
        end

    | If(t1, t2, t3) ->
      pos <| Exp_match(desugar_exp env t1,
                       [(Pat_constant (Const_bool true), None, desugar_exp env t2);
                        (Pat_constant (Const_bool false), None, desugar_exp env t3)])

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

    | Record(eopt, fields) -> 
      let f, _ = List.hd fields in 
      let record, _ = fail_or (try_lookup_record_by_field_name env) f in
      let get_field xopt f = 
        let _, fn = Util.prefix f.lid in
        let found = fields |> Util.find_opt (fun (g, _) -> 
          let _, gn = Util.prefix g.lid in 
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
                      get_field None f))
            
        | Some e -> 
          let x = genident (Some e.range) in 
          let xterm = mk_term (Var (lid_of_ids [x])) x.idRange Expr in
          let record = Construct(record.constrname, 
                                 record.fields |> List.map (fun (f, _) -> 
                                    get_field (Some xterm) f)) in
          Let(false, [(mk_pattern (PatVar x) x.idRange, e)], mk_term record top.range top.level) in
      let recterm = mk_term recterm top.range top.level in 
      desugar_exp env recterm
        
    | Project(e, f) -> 
      let _, fieldname = fail_or (try_lookup_record_by_field_name env) f in 
      let proj = mk_term (App(mk_term (Var fieldname) (range_of_lid f) Expr, e)) top.range top.level in 
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
      desugar_typ env (mk_term (Sum([mk_binder (NoName t1) t1.range Type], t2)) top.range top.level)
      
    | Op("<>", args) ->
      let t = desugar_typ env (mk_term (Op("=", args)) top.range top.level) in
      pos <| Typ_app(ftv <| set_lid_range Const.not_lid top.range, t)

    | Op(s, args) ->
      begin match op_as_tylid top.range s with
        | None -> raise (Error("Unrecognized type operator: " ^ s, top.range))
        | Some l ->
          let args = List.map (desugar_typ_or_exp env) args in
          mk_tapp (ftv l) args
      end

    | Tvar a -> 
      pos <| fail_or2 (try_lookup_typ_var env) a  
          
    | Var l
    | Name l -> 
      pos <| fail_or (try_lookup_typ_name env) l 
      
    | Construct(l, args) -> 
      let t = fail_or (try_lookup_typ_name env) l in 
      let args = List.map (desugar_typ_or_exp env) args in 
      mk_tapp t args

    | Abs(p::(q::_ as rest), body) -> 
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
            | Inl (a,k) -> pos <| Typ_tlam(a, k, body)
            | Inr (x,t) -> pos <| Typ_lam(x,t, body)
      end

    | App(t1, t2) -> 
      let t1 = desugar_typ env t1 in
      let t2 = desugar_typ_or_exp env t2 in
      mk_tapp t1 [t2]
        
    | Product([], t) -> 
      desugar_typ env t
      
    | Product(b::(_::_ as bs), t) ->
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
          Typ_fun(None, t1, desugar_typ env t)

        | Inr(Some x, t1) -> 
          let env, x = push_local_vbinding env x in
          Typ_fun(Some x, t1, desugar_typ env t) in
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
        (env, [], []) (binders@[mk_binder (NoName t) t.range Type]) in
      let tup = fail_or (try_lookup_typ_name env) (lid_of_path [Util.strcat "Tuple" (Util.string_of_int <| List.length targs)] top.range) in
      pos <| List.fold_left (fun t1 t2 -> Typ_app(t1,t2)) tup targs 
          
    | Record _ -> failwith "NYI: Records"

    | _ -> error "Expected a type" top top.range

and desugar_kind env k : kind = 
  match k.term with 
    | Name {str="P"} -> Kind_prop
    | Name {str="S"} -> Kind_star
    | Name {str="E"} -> Kind_erasable
    | Wild           -> Kind_unknown
    | Product([b], t) -> 
      let tk = desugar_binder env b in 
      begin match tk with 
        | Inl(None, k) -> 
          Kind_tcon(None, k, desugar_kind env t)

        | Inl(Some a, k) -> 
          let env, a = push_local_tbinding env a in
          Kind_tcon(Some a, k, desugar_kind env t)

        | Inr(None, t0) -> 
          Kind_dcon(None, t0, desugar_kind env t)

        | Inr(Some x, t0) -> 
          let env, x = push_local_vbinding env x in
          Kind_dcon(Some x, t0, desugar_kind env t)
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
    let tk = desugar_binder env {b with level=Formula} in
    match tk with 
      | Inl(Some a,k) -> 
        let env, a = push_local_tbinding env a in 
        let pats = List.map (desugar_typ_or_exp env) pats in
        let body = desugar_formula env body in 
        let body = match pats with 
          | [] -> body
          | _ -> Typ_meta (Meta_pattern(body, pats)) in
        let body = pos <| Typ_tlam(a, k, body) in 
        pos <| mk_tapp (ftv (set_lid_range qt b.range)) [Inl body]
            
      | Inr(Some x,t) -> 
        let env, x = push_local_vbinding env x in 
        let pats = List.map (desugar_typ_or_exp env) pats in
        let body = desugar_formula env body in 
        let body = match pats with 
          | [] -> body
          | _ -> Typ_meta (Meta_pattern(body, pats)) in
        let body = pos <| Typ_lam(x, t, body) in 
        pos <| mk_tapp (ftv (set_lid_range q b.range)) [Inl body] 

      | _ -> raise Impos in
            
  let push_quant q (binders:binder list) pats (body:term) = match binders with 
    | b::(b'::_ as rest) -> 
      let body = mk_term (q(rest, pats, body)) (Range.union_ranges b'.range body.range) Formula in 
      mk_term (q([b], [], body)) f.range Formula
    | _ -> raise Impos in

  match f.term with
    | Op("=", ((hd::_) as args)) ->
      let args = List.map (desugar_typ_or_exp env) args in
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
            (List.map (fun x -> Inl <| desugar_formula env x) args)
        | _ -> desugar_typ env f
      end

    | App({term=Var l}, arg) when l.str = "not" ->
      let arg = desugar_formula env arg in 
      mk_tapp (ftv (set_lid_range Const.not_lid f.range)) [Inl arg]
        
    | If(f1, f2, f3) ->
      mk_tapp 
        (ftv (set_lid_range Const.ite_lid f.range)) 
        (List.map (fun x -> Inl <| desugar_typ env x) [f1;f2;f3])

    | QForall((_::_::_ as binders), pats, body) ->
      desugar_formula env (push_quant QForall binders pats body)

    | QExists((_::_::_ as binders), pats, body) ->
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
  desugar_formula' {env with phase=Formula} t          

and desugar_binder env b = 
  if is_type_binder env b
  then Inl (desugar_type_binder env b)
  else Inr (desugar_exp_binder env b)

and typars_of_binders env bs = 
    let env, tpars = List.fold_left (fun (env, out) b -> 
        let tk = desugar_binder env {b with level=Formula} in  (* typars follow the same binding conventions as formulas *)
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
  | Sig_datacon(lid, t) -> 
    let args, tconstr = collect_formals t in
    let argpats = args |> List.map (function 
      | Inr(Some x,_) -> Pat_var x 
      | Inr(None,targ) -> Pat_var (new_bvd (Some (range_of_lid lid)))
      | Inl(a,_) -> Pat_tvar a) in
    let freetv, freexv  = freevars_typ tconstr in 
    let freevars = (List.map Inl freetv)@(List.map Inr freexv) in 
    let formal = new_bvd (Some <| range_of_lid lid) in
    let formal_exp = bvd_to_exp formal tconstr in
    let rec build_exp freevars e = match freevars with
      | Inl a::rest -> ewithpos (Exp_tabs(a.v, a.sort, build_exp rest e)) e.p
      | Inr x::rest -> ewithpos (Exp_abs(x.v, x.sort, build_exp rest e)) e.p
      | [] -> ewithpos (Exp_abs(formal, tconstr, e)) e.p in
    let rec build_typ freevars t = match freevars with
      | Inl a::rest -> Typ_univ(a.v, a.sort, build_typ rest t)
      | Inr x::rest -> Typ_fun(Some x.v, x.sort, build_typ rest t)
      | [] -> Typ_fun(Some formal, tconstr, t) in
    let rec build_kind freevars k = match freevars with
      | Inl a::rest -> Kind_tcon(Some a.v, a.sort, build_kind rest k)
      | Inr x::rest -> Kind_dcon(Some x.v, x.sort, build_kind rest k) 
      | [] -> Kind_dcon(Some formal, tconstr, k) in
    let build_exp  = build_exp freevars in 
    let build_typ  = build_typ freevars in 
    let build_kind = build_kind freevars in
    let rec aux subst fields t = match compress t with 
      | Typ_fun(Some x, t1, t2) -> 
        let field_name = lid_of_ids (lid.lid @ [x.ppname]) in
        let t = build_typ t1 in 
        let body = ewithpos (Exp_match(formal_exp, [(Pat_cons(lid, argpats), None, bvd_to_exp x t1)])) x.ppname.idRange in
        let sigs = 
          [Sig_val_decl(field_name, t);
           Sig_let([(field_name, t, build_exp body)], false)] in
        (* let _ = Util.print_string (Util.format1 "adding value projector %s\n" field_name.str) in *)
        let subst = Inr(x, mk_app (fvar field_name (range_of_lid field_name)) [Inr formal_exp])::subst in
        let t2 = subst_typ subst t2 in 
        aux subst (fields@sigs) t2
          
      | Typ_univ(a, k, t2) -> 
        let field_name = lid_of_ids (lid.lid @ [a.ppname]) in
        let sigs = Sig_tycon(field_name, [], build_kind k, [], [], [Logic_projector]) in
        (* let _ = Util.print_string (Util.format1 "adding type projector %s\n" field_name.str) in *)
        let subst = Inl(a, mk_tapp (ftv field_name) [Inr formal_exp])::subst in
        let t2 = subst_typ subst t2 in 
        aux subst (fields@[sigs]) t2

      | _ -> fields in 
    
    aux [] [] t 
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
    List.fold_left (fun out b -> mk_term (App(out, binder_to_term b)) out.range out.level)
      t binders in
  let tycon_record_as_variant = function
    | TyconRecord(id, parms, kopt, fields) ->
      let constrName = mk_ident("Mk" ^ id.idText, id.idRange) in
      let fields = List.map (fun (x,t) -> mk_binder (Annotated(x,t)) x.idRange Expr) fields in 
      let result = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type) parms in
      let constrTyp = mk_term (Product(fields, result)) id.idRange Type in 
      TyconVariant(id, parms, kopt, [(constrName, constrTyp, false)])
    | _ -> raise Impos in
  let desugar_abstract_tc env mutuals = function
    | TyconAbstract(id, binders, kopt) ->
      let env', typars = typars_of_binders env binders in 
      let k = match kopt with 
        | None -> Kind_star
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
    | [TyconAbstract _ as tc] ->
        let _, _, se, _ = desugar_abstract_tc env [] tc in
        let env = push_sigelt env se in 
        (* let _ = pr "Pushed %s\n" (text_of_lid (qualify env (tycon_id tc))) in *)
        env, [se]

    | [TyconAbbrev(id, binders, kopt, t)] ->
        let env', typars = typars_of_binders env binders in 
        let k = match kopt with 
            | None -> Kind_star
            | Some k -> desugar_kind env' k in
        let t = desugar_typ env' t in 
        let se = Sig_typ_abbrev(qualify env id, typars, k, t) in
        let env = push_sigelt env se in 
        env, [se]

    | [TyconRecord _ as trec] -> 
      desugar_tycon env (LogicTag Logic_record::quals) [tycon_record_as_variant trec]

    |  _::_ -> 
      let env0 = env in 
      let mutuals = List.map (fun x -> qualify env <| tycon_id x) tcs in 
      let rec collect_tcs (env, tcs) = function
        | TyconRecord _ as trec -> 
          collect_tcs (env, tcs) (tycon_record_as_variant trec)
        | TyconVariant(id, binders, kopt, constructors) -> 
          let env, (_, tps), se, tconstr = desugar_abstract_tc env mutuals (TyconAbstract(id, binders, kopt)) in
          env, Inl(se, tps, constructors, tconstr)::tcs
        | TyconAbbrev(id, binders, kopt, t) -> 
          let env, (_, tps), se, tconstr = desugar_abstract_tc env mutuals (TyconAbstract(id, binders, kopt)) in
          env, Inr(se, tps, t)::tcs
        | _ -> failwith "Unrecognized mutual type definition" in 
      let env, tcs = List.fold_left collect_tcs (env, []) tcs in 
      let tcs = List.rev tcs in 
      let sigelts = tcs |> List.collect (function
        | Inr(Sig_tycon(id, tpars, k, _, _, _), tps, t) -> 
          let env_tps = push_tparams env tps in
          let t = desugar_typ env_tps t in
          [Sig_typ_abbrev(id, tpars, k, t)]
            
        | Inl (Sig_tycon(id, tpars, k, mutuals, _, tags), tps, constrs, tconstr) -> 
          let env_tps = push_tparams env tps in
          let constrNames, constrs = List.split <|
              (constrs |> List.map (fun (id, t, of_notation) -> 
                let t = 
                  if of_notation
                  then mk_term (Product([mk_binder (NoName t) t.range t.level], tconstr)) t.range t.level
                  else t in 
                let t = desugar_typ env_tps (close env_tps t) in
                let name = qualify env id in 
                (name, Sig_datacon(name, close_typ tps t)))) in 
              Sig_tycon(id, tpars, k, mutuals, constrNames, tags)::constrs
        | _ -> raise Impos) in 
      let bundle = Sig_bundle sigelts in
      let env = push_sigelt env0 bundle in
      let data_ops = 
        if List.exists (function Logic_data | Logic_record -> true | _ -> false) (logic_tags quals) 
        then sigelts |> List.collect (mk_data_ops env)
        else [] in
      let env = List.fold_left push_sigelt env data_ops in
      env, [bundle]@data_ops

    | [] -> raise Impos
           
let desugar_decl env (d:decl) : (env * sigelts) = match d.decl with
  | Open lid -> 
    let env = DesugarEnv.push_namespace env lid in 
    env, []
  
  | Tycon(qual, tcs) ->
    desugar_tycon env [qual] tcs
          
  | ToplevelLet(isrec, lets) ->
    begin match desugar_exp env (mk_term (Let(isrec, lets, mk_term (Const Const_unit) d.range Expr)) d.range Expr) with 
        | {v=Exp_let(_, lbs, _)} -> 
          let lbs = List.map (fun (x, t, e) -> (qualify env x.ppname, t, e)) lbs in
          let s = Sig_let(lbs,isrec) in
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

  | Val(NoQual, id, t) ->
      let t = desugar_typ env (close env t) in 
      let se = Sig_val_decl(qualify env id, t) in 
      let env = push_sigelt env se in 
      env, [se]

  | Val(LogicTag Logic_val, id, t) ->
      let t = desugar_typ env (close env t) in 
      let se = Sig_logic_function(qualify env id, t, []) in 
      let env = push_sigelt env se in 
      env, [se]
        
  | Exception(id, term) -> 
    let t = desugar_typ env term in 
    let t = Typ_fun(None, t, fail_or (try_lookup_typ_name env) Const.exn_lid) in
    let se = Sig_datacon(qualify env id, t) in 
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
    env, m::mods) (env, []) ms in
  env, List.rev mods
            

