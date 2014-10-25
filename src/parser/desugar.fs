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
open Microsoft.FStar.Parser.AST
open Microsoft.FStar.Parser.DesugarEnv
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util

let withimp imp t = t, imp

let contains_binder binders = 
  binders |> Util.for_some (fun b -> match b.b with  
    | Annotated _ -> true
    | _ -> false)

let rec unparen t = match t.tm with 
  | Paren t -> unparen t
  | _ -> t
let rec unlabel t = match t.tm with 
  | Paren t -> unlabel t
  | Labeled(t, _, _) -> unlabel t
  | _ -> t

let kind_star r = mk_term (Name (lid_of_path ["Type"] r)) r Kind

let op_as_vlid env arity r s =
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
    | "*", _ ->    r Const.op_Multiply
    | "+", _ ->    r Const.op_Addition
    | "-", _  when 
      (arity=1) -> r Const.op_Minus
    | "-", _ ->    r Const.op_Subtraction
    | "/", _ ->    r Const.op_Division
    | "%", _ ->    r Const.op_Modulus
    | "!", _ ->    r Const.read_lid
    | "@", _ ->    r Const.list_append_lid
    | "^", _ ->    r Const.strcat_lid
    | "|>", _ ->   r Const.pipe_right_lid
    | "<|", _ ->   r Const.pipe_left_lid
    | "<>", _ ->   r Const.op_notEq
    | _ -> None

let op_as_tylid r s =
  let r l = Some <| set_lid_range l r in
  match s with
    | "~"   ->  r Const.not_lid
    | "=="  ->  r Const.eq2_lid
    | "=!=" ->  r Const.neq2_lid
    | "<" ->    r Const.lt_lid
    | "<=" ->   r Const.lte_lid
    | ">" ->    r Const.gt_lid
    | ">=" ->   r Const.gte_lid
    | "/\\" ->  r Const.and_lid
    | "\\/" ->  r Const.or_lid
    | "==>" ->  r Const.imp_lid
    | "<==>" -> r Const.iff_lid
    | _ -> None

let rec is_type env (t:term) =
  if t.level = Type then true
  else match (unlabel t).tm with
    | Wild -> true
    | Op("*", hd::_) -> is_type env hd     (* tuple constructor *)
    | Op("==", _)                          (* equality predicate *)
    | Op("=!=", _) 
    | Op("~", _)
    | Op("/\\", _)
    | Op("\\/", _)
    | Op("==>", _)
    | Op("<==>", _)  -> true               (* negation predicate *)
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
    | App(t, _, _)
    | Paren t
    | Ascribed(t, _)
    | Product(_, t)
    | Abs(_, t) -> is_type env t
    | If(t, t1, t2) -> is_type env t || is_type env t1 || is_type env t2 
    | _ -> false

let rec is_kind env (t:term) : bool =
  if t.level = Kind
  then true
  else match (unparen t).tm with
    | Name {str="Type"} -> true
    | Product(_, t) -> is_kind env t
    | Paren t -> is_kind env t
    | Construct(l, _) 
    | Name l -> DesugarEnv.is_kind_abbrev env (DesugarEnv.qualify_lid env l)
    | _ -> false

let rec is_type_binder env b =
  if b.blevel = Formula
  then match b.b with
    | Variable _
    | Annotated _ -> false
    | TAnnotated _
    | TVariable _ -> true
    | NoName t -> is_kind env t
  else match b.b with
    | Variable _ -> raise (Error("Unexpected binder without annotation", b.brange))
    | TVariable _ -> false
    | TAnnotated _ -> true
    | Annotated (_, t)
    | NoName t -> is_kind env t

let sort_ftv ftv =
  Util.sort_with (fun x y -> String.compare x.idText y.idText) <|
      Util.remove_dups (fun x y -> x.idText = y.idText) ftv

let rec free_type_vars_b env binder = match binder.b with
  | Variable _ -> env, []
  | TVariable x ->
    let env, _ = push_local_tbinding env x in
    (env, [x])
  | Annotated(_, term) ->
    (env, free_type_vars env term)
  | TAnnotated(id, _) ->
    let env, _ = push_local_tbinding env id in
    (env, [])
  | NoName t ->
    (env, free_type_vars env t)
and free_type_vars env t = match (unparen t).tm with
  | Tvar a ->
    (match DesugarEnv.try_lookup_typ_var env a with
      | None -> [a]
      | _ -> [])

  | Wild
  | Const _
  | Var  _
  | Name _  -> []

  | Requires (t, _)
  | Ensures (t, _)
  | Labeled(t, _, _)
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

let rec uncurry bs t = match t.tm with
    | Product(binders, t) -> uncurry (bs@binders) t 
    | _ -> bs, t
              
let rec is_app_pattern p = match p.pat with
  | PatAscribed(p,_) -> is_app_pattern p
  | PatApp({pat=PatVar _}, _) -> true
  | _ -> false

let rec destruct_app_pattern env is_top_level p = match p.pat with
  | PatAscribed(p,t) ->
    let (name, args, _) = destruct_app_pattern env is_top_level p in
    (name, args, Some t)
  | PatApp({pat=PatVar id}, args) when is_top_level ->
    (Inr (qualify env id), args, None)
  | PatApp({pat=PatVar id}, args) ->
    (Inl id, args, None)
  | _ ->
    failwith "Not an app pattern"

type bnd = 
  | TBinder of btvdef * knd
  | VBinder of bvvdef * typ
  | LetBinder of lident * typ
let binder_of_bnd = function 
  | TBinder (a, k) -> t_binder (Util.bvd_to_bvar_s a k)
  | VBinder (x, t) -> v_binder (Util.bvd_to_bvar_s x t)
  | _ -> failwith "Impossible"
let as_binder env imp = function
  | Inl(None, k) -> null_t_binder k, env
  | Inr(None, t) -> null_v_binder t, env
  | Inl(Some a, k) -> 
    let env, a = DesugarEnv.push_local_tbinding env a in
    (Inl <| bvd_to_bvar_s a k, imp), env
  | Inr(Some x, t) ->
    let env, x = DesugarEnv.push_local_vbinding env x in 
    (Inr <| bvd_to_bvar_s x t, imp), env
     
type env_t = DesugarEnv.env
type lenv_t = list<either<btvdef,bvvdef>>

let label_conjuncts tag polarity label_opt f = 
  let label f = 
    let msg = match label_opt with 
        | Some l -> l
        | _ -> 
          Util.format2 "%s at %s" tag (Range.string_of_range f.range) in
    mk_term (Labeled(f, msg, polarity)) f.range f.level  in

  let rec aux f = match f.tm with 
    | Paren g -> 
      mk_term (Paren(aux g)) f.range f.level

    | Op("/\\", [f1;f2]) ->  
      mk_term (Op("/\\", [aux f1; aux f2])) f.range f.level

    | If(f1, f2, f3) ->
      mk_term (If(f1, aux f2, aux f3)) f.range f.level

    | Abs(binders, g) -> 
      mk_term (Abs(binders, aux g)) f.range f.level
      
    | _ -> 
      label f in

  aux f

let rec desugar_data_pat env (p:pattern) : (env_t * bnd * Syntax.pat) =
  let resolvex (l:lenv_t) e x = 
    match l |> Util.find_opt (function Inr y -> y.ppname.idText=x.idText | _ -> false) with 
      | Some (Inr y) -> l, e, y
      | _ -> 
        let e, x = push_local_vbinding e x in
        (Inr x::l), e, x in
  let resolvea (l:lenv_t) e a = 
    match l |> Util.find_opt (function Inl b -> b.ppname.idText=a.idText | _ -> false) with 
      | Some (Inl b) -> l, e, b
      | _ -> 
        let e, a = push_local_tbinding e a in
        (Inl a::l), e, a in
  let rec aux (loc:lenv_t) env (p:pattern) =
    let pos q = Pat_meta(Meta_pat_pos(q, p.prange)) in 
    match p.pat with
      | PatOr [] -> failwith "impossible"
      | PatOr (p::ps) ->
        let q = p in
        let loc, env, var, p = aux loc env p in
        let loc, env, ps = List.fold_left (fun (loc, env, ps) p ->
          let loc, env, _, p = aux loc env p in
          loc, env, p::ps) (loc, env, []) ps in
        let pat = Pat_disj (p::List.rev ps) in
        ignore (pat_vars q.prange pat);
        loc, env, var, pos <| pat

      | PatAscribed(p, t) ->
        let loc, env', binder, p = aux loc env p in
        let binder = match binder with
          | LetBinder _ -> failwith "impossible"
          | TBinder(x, _) -> TBinder(x, desugar_kind env t)
          | VBinder(x, _) -> VBinder(x, desugar_typ env t) in
        loc, env', binder, p

      | PatTvar a ->
        if a.idText = "'_"
        then loc, env, TBinder(new_bvd <| Some p.prange, kun), Pat_twild
        else let loc, env, abvd = resolvea loc env a in
             loc, env, TBinder(abvd, kun), pos <| Pat_tvar abvd

      | PatWild ->
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun), pos <| Pat_wild
        
      | PatConst c ->
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun), pos <| Pat_constant c

      | PatVar x ->
        let loc, env, xbvd = resolvex loc env x in 
        loc, env, VBinder(xbvd, tun), pos <| Pat_var xbvd

      | PatName l ->
        let l = fail_or env (try_lookup_datacon env) l in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun), pos <| Pat_cons(l.v, [])

      | PatApp({pat=PatName l}, args) ->
        let loc, env, args = List.fold_right (fun arg (loc,env,args) ->
          let loc, env, _, arg = aux loc env arg in
          (loc, env, arg::args)) args (loc, env, []) in
        let l = fail_or env  (try_lookup_datacon env) l in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun), pos <| Pat_cons(l.v, args)

      | PatApp _ -> raise (Error ("Unexpected pattern", p.prange))

      | PatList pats ->
        let loc, env, pats = List.fold_right (fun pat (loc, env, pats) ->
          let loc,env,_,pat = aux loc env pat in
          loc, env, pat::pats) pats (loc, env, []) in
        let pat = List.fold_right (fun hd tl -> Pat_cons(Const.cons_lid, [hd;tl])) pats (Pat_cons(Const.nil_lid, [])) in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun), pos <| pat
        
      | PatTuple(args, dep) ->
        let loc, env, args = List.fold_left (fun (loc, env, pats) p ->
          let loc, env, _, pat = aux loc env p in
          loc, env, pat::pats) (loc,env,[]) args in
        let args = List.rev args in
        let l = if dep then Util.mk_dtuple_data_lid (List.length args) p.prange
                else Util.mk_tuple_data_lid (List.length args) p.prange in
        let constr = fail_or env  (DesugarEnv.try_lookup_lid env) l in
        let l = match constr.n with
          | Exp_fvar (v, _) -> v.v
          | _ -> failwith "impossible" in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun), pos <| Pat_cons(l, args)

      | PatRecord ([]) -> 
        raise (Error ("Unexpected pattern", p.prange))
        
      | PatRecord (fields) -> 
        let (f, _) = List.hd fields in 
        let record, _ = fail_or env  (try_lookup_record_by_field_name env) f in
        let fields = fields |> List.map (fun (f, p) -> 
          (fail_or env  (qualify_field_to_record env record) f, p)) in
        let args = record.fields |> List.map (fun (f, _) -> 
          match fields |> List.tryFind (fun (g, _) -> lid_equals f g) with 
            | None -> mk_pattern PatWild p.prange
            | Some (_, p) -> p) in 
        let app = mk_pattern (PatApp(mk_pattern (PatName record.constrname) p.prange, args)) p.prange in
        aux loc env app in
  let _, env, b, p = aux [] env p in
  env, b, p
         
and desugar_binding_pat_maybe_top top env p : (env_t * bnd * option<pat>) =
  if top 
  then match p.pat with 
    | PatVar x -> (env, LetBinder(qualify env x, tun), None)
    | PatAscribed({pat=PatVar x}, t) -> 
      (env, LetBinder(qualify env x, desugar_typ env t), None)
    | _ -> raise (Error("Unexpected pattern at the top-level", p.prange)) 
  else
    let (env, binder, p) = desugar_data_pat env p in
    let p = match p with
      | Pat_var _
      | Pat_tvar _ 
      | Pat_meta(Meta_pat_pos(Pat_var _, _))
      | Pat_meta(Meta_pat_pos(Pat_tvar _, _)) -> None
      | _ -> Some p in
    (env, binder, p)

and desugar_binding_pat env p = desugar_binding_pat_maybe_top false env p

and desugar_match_pat_maybe_top _ env pat =
  let (env, _, pat) = desugar_data_pat env pat in
  (env, pat)

and desugar_match_pat env p = desugar_match_pat_maybe_top false env p

and desugar_typ_or_exp (env:env_t) (t:term) : either<typ,exp> =
  if is_type env t
  then Inl <| desugar_typ env t
  else Inr <| desugar_exp env t

and desugar_exp env e = desugar_exp_maybe_top false env e 

and desugar_exp_maybe_top (top_level:bool) (env:env_t) (top:term) : exp =
  let pos e = e tun top.range in
  let setpos e = {e with pos=top.range} in
  begin match (unparen top).tm with
    | Const c -> pos <| mk_Exp_constant c

    | Op(s, args) ->
      begin match op_as_vlid env (List.length args) top.range s with
        | None -> raise (Error("Unexpected operator: " ^ s, top.range))
        | Some l ->
          let op = fvar l (range_of_lid l) in
          let args = args |> List.map (fun t -> desugar_typ_or_exp env t, false) in
          setpos <| mk_exp_app op args
      end

    | Var l
    | Name l -> 
      setpos <| fail_or env (DesugarEnv.try_lookup_lid env) l
      
    | Construct(l, args) ->
      let dt = pos <| mk_Exp_fvar(fail_or env (DesugarEnv.try_lookup_datacon env) l, true) in
      begin match args with 
        | [] -> dt
        | _ -> 
          let args = List.map (fun (t, imp) -> withimp imp <| desugar_typ_or_exp env t) args in
          setpos <| mk_Exp_meta(Meta_desugared(mk_exp_app dt args, Data_app)) 
      end

    | Abs(binders, body) ->
      let _, ftv = List.fold_left (fun (env, ftvs) pat ->
        match pat.pat with
          | PatAscribed ({pat=PatTvar a}, t) -> 
            let ftvs = free_type_vars env t@ftvs in 
            fst <| DesugarEnv.push_local_tbinding env a, ftvs
          | PatTvar a -> fst <| DesugarEnv.push_local_tbinding env a, ftvs
          | PatAscribed(_, t) -> env, free_type_vars env t@ftvs
          | _ -> env, ftvs) (env, []) binders in
      let ftv = sort_ftv ftv in
      let binders = (ftv |> List.map (fun a -> mk_pattern (PatTvar a) top.range))@binders in //close over the free type variables
     
      let rec aux env bs sc_pat_opt = function
            | [] -> 
              let body = desugar_exp env body in 
              let body = match sc_pat_opt with 
                | Some (sc, pat) -> mk_Exp_match(sc, [(pat, None, body)]) tun body.pos
                | None -> body in 
              mk_Exp_abs'(List.rev bs, body) tun top.range

            | p::rest -> 
              let env, b, pat = desugar_binding_pat env p in
              let b, sc_pat_opt = match b with
                | LetBinder _ -> failwith "Impossible"
                | TBinder (a,k) -> t_binder <| Util.bvd_to_bvar_s a k, sc_pat_opt
                | VBinder (x,t) -> 
                    let b = Util.bvd_to_bvar_s x t in
                    let sc_pat_opt = match pat, sc_pat_opt with 
                        | None, _ -> sc_pat_opt
                        | Some p, None -> Some (Util.bvar_to_exp b, p) 
                        | Some p, Some (sc, p') ->
                             begin match sc.n, p' with 
                                | Exp_bvar _, _ -> 
                                  let tup = Util.mk_tuple_data_lid 2 top.range in
                                  let sc = Syntax.mk_Exp_app(Util.fvar tup top.range, [varg sc; varg <| Util.bvar_to_exp b]) tun top.range in
                                  let p = Pat_cons(tup, [p';p]) in
                                  Some(sc, p)
                                | Exp_app(_, args), Pat_cons(_, pats) ->
                                  let tup = Util.mk_tuple_data_lid (1 + List.length args) top.range in
                                  let sc = Syntax.mk_Exp_app(Util.fvar tup top.range, args@[(varg <| Util.bvar_to_exp b)]) tun top.range in 
                                  let p = Pat_cons(tup, pats@[p]) in
                                  Some(sc, p)
                                | _ -> failwith "Impossible"
                              end in
                    v_binder b, sc_pat_opt in
                aux env (b::bs) sc_pat_opt rest 
       in
       aux env [] None binders

    | App({tm=Var a}, arg, _) when (lid_equals a Const.assert_lid
                                   || lid_equals a Const.assume_lid) ->
      let phi = desugar_formula env arg in
      pos <| mk_Exp_app(fvar a (range_of_lid a), 
                        [targ <| phi;
                         varg <| mk_Exp_constant(Const_unit) tun top.range])

    | App _ -> 
      let rec aux args e = match (unparen e).tm with
        | App(e, t, imp) -> 
          let arg = withimp imp <| desugar_typ_or_exp env t in
          aux (arg::args) e
        | _ -> 
          let head = desugar_exp env e in 
          pos <| mk_Exp_app(head, args) in
      aux [] top
             
    | Seq(t1, t2) ->
      setpos <| mk_Exp_meta(Meta_desugared(desugar_exp env (mk_term (Let(false, [(mk_pattern PatWild t1.range,t1)], t2)) top.range Expr), 
                              Sequence))
        
    | Let(b, ((pat, _snd)::_tl), body) -> 
      let ds_app_pat () = 
        let bindings = (pat, _snd)::_tl in
        let funs = bindings |> List.map (fun (p, def) ->
          let p, def = if is_app_pattern p
                       then p, def
                       else match un_function p def with 
                             | Some (p, def) -> p, def  
                             | _ -> raise (Error("Only functions may be defined recursively", p.prange)) in
          destruct_app_pattern env top_level p, def) in
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
          let def = mk_term (un_curry_abs args def) top.range top.level in
          //let _ = Util.fprint1 "Desugaring let binding: %s\n" (AST.term_to_string def) in
          desugar_exp env def in
        let defs = funs |> List.map (desugar_one_def (if b then env' else env)) in
        let lbs = List.map2 (fun lbname def -> (lbname, tun, def)) fnames defs in
        let body = desugar_exp env' body in
        pos <| mk_Exp_let((b, lbs), body) in

      let ds_non_rec pat t1 t2 =
        let t1 = desugar_exp env t1 in
        let env, binder, pat = desugar_binding_pat_maybe_top top_level env pat in
        begin match binder with
          | TBinder _ -> failwith "Unexpected type binder in let"
          | LetBinder(l, t) -> 
            let body = desugar_exp env t2 in
            pos <| mk_Exp_let((false, [(Inr l, t, t1)]), body)
          | VBinder (x,t) ->
            let body = desugar_exp env t2 in
            let body = match pat with
              | None 
              | Some Pat_wild -> body
              | Some pat -> mk_Exp_match(bvd_to_exp x t, [(pat, None, body)]) tun body.pos in
            pos <| mk_Exp_let((false, [(Inl x, t, t1)]), body)
        end in

      if is_app_pattern pat 
      then ds_app_pat ()
      else if not b 
      then ds_non_rec pat _snd body
      else error "Unexpected term" top top.range
      
    | If(t1, t2, t3) ->
      pos <| mk_Exp_match(desugar_exp env t1,
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
      pos <| mk_Exp_match(desugar_exp env e, List.map desugar_branch branches)

    | Ascribed(e, t) ->
      pos <| mk_Exp_ascribed'(desugar_exp env e, desugar_typ env t)

    | Record(_, []) ->
      raise (Error("Unexpected empty record", top.range))

    | Record(eopt, fields) ->
      let f, _ = List.hd fields in
      let record, _ = fail_or env  (try_lookup_record_by_field_name env) f in
      let get_field xopt f =
        let fn = f.ident in
        let found = fields |> Util.find_opt (fun (g, _) ->
          let gn = g.ident in
          fn.idText = gn.idText) in
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
     // let _ = Util.print_string (Util.format1 "Looking up field name %s\n" (Print.sli f)) in 
      let _, fieldname = fail_or env  (try_lookup_record_by_field_name env) f in
      //let _ = Util.print_string (Util.format2 "resolved %s as %s\n" (Print.sli f) (Print.sli fieldname)) in 
      let proj = mk_term (App(mk_term (Var fieldname) (range_of_lid f) Expr, e, false)) top.range top.level in
      desugar_exp env proj

    | Paren e ->
      desugar_exp env e

    | _ ->
      error "Unexpected term" top top.range
  end
  
and desugar_typ env (top:term) : typ =
  let pos (t:knd -> Range.range -> 'a) : 'a = t kun top.range in
  let setpos t = {t with pos=top.range} in
  let top = unparen top in  
  match top.tm with
    | Wild -> setpos tun

    | Requires (t, lopt) -> 
      let t = label_conjuncts "pre-condition" true lopt t in
      desugar_typ env t

    | Ensures (t, lopt) -> 
      let t = label_conjuncts "post-condition" false lopt t in
      desugar_typ env t

    | Op("*", [t1; _]) -> 
      if is_type env t1 
      then let rec flatten t = match t.tm with
            | Op("*", [t1;t2]) -> 
              let binders, final = flatten t2 in
              let b = mk_binder (NoName t1) t1.range Type false in
              b::binders, final
            | Sum(binders, final) -> binders, final 
            | _ -> [], t in 
          let binders, final = flatten top in
          let t = mk_term (Sum(binders, final)) top.range top.level in
          desugar_typ env t
      else raise (Error(Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" (term_to_string t1), top.range))
      
    | Op("=!=", args) ->
      desugar_typ env (mk_term(Op("~", [mk_term (Op("==", args)) top.range top.level])) top.range top.level)
      
    | Op(s, args) ->
      begin match op_as_tylid top.range s with
        | None -> raise (Error("Unrecognized type operator" ^ s, top.range))
        | Some l ->
          let args = List.map (fun t -> withimp false <| desugar_typ_or_exp env t) args in
          mk_typ_app (ftv l kun) args
      end

    | Tvar a ->
      setpos <| fail_or2 (try_lookup_typ_var env) a
          
    | Var l
    | Name l ->
      setpos <| fail_or env  (try_lookup_typ_name env) l
      
    | Construct(l, args) ->
      let t = fail_or env  (try_lookup_typ_name env) l in
      let args = List.map (fun (t, imp) -> withimp imp <| desugar_typ_or_exp env t) args in
      mk_typ_app t args

  
    | Abs(binders, body) -> 
      let rec aux env bs = function 
        | [] -> 
          let body = desugar_typ env body in 
          pos <| mk_Typ_lam(List.rev bs, body) 
        | hd::tl -> 
          let env, bnd, pat = desugar_binding_pat env hd in
          match pat with
            | Some q -> raise (Error(Util.format1 "Pattern matching at the type level is not supported; got %s\n" (Print.pat_to_string q), hd.prange))
            | None ->
              let b = binder_of_bnd bnd in 
              aux env (b::bs) tl in
      aux env [] binders

    | App _ -> 
      let rec aux args e = match (unparen e).tm with 
        | App(e, arg, imp) ->
          let arg = withimp imp <| desugar_typ_or_exp env arg in
          aux (arg::args) e
        | _ -> 
          let head = desugar_typ env e in
          pos <| mk_Typ_app(head, args) in
      aux [] top
       
    | Product([], t) -> 
      failwith "Impossible: product with no binders"
      
    | Product(binders, t) ->
      let bs, t = uncurry binders t in
      let rec aux env bs = function 
        | [] ->   
          let t = desugar_typ env t in 
          let head, args = Util.head_and_args t in 
          let cod = match (compress_typ head).n, args with 
              | Typ_const eff, (Inl result_typ, _)::rest -> 
                if DesugarEnv.is_effect_name env eff.v
                then if lid_equals eff.v Const.tot_effect_lid
                     then mk_Total result_typ
                     else let flags = if lid_equals eff.v Const.ml_effect_lid
                                      then [MLEFFECT] else [] in
                          mk_Comp ({effect_name=eff.v;
                                    result_typ=result_typ;
                                    effect_args=rest; 
                                    flags=flags})
                else env.default_result_effect t top.range 
              | _ -> env.default_result_effect t top.range in 
          pos <| mk_Typ_fun(List.rev bs, cod)
        | hd::tl -> 
          let b, env = desugar_binder (ml env) hd |> as_binder env hd.implicit in
          aux env (b::bs) tl in
      aux env [] bs

    | Refine(b,f) ->
      begin match desugar_exp_binder env b with
        | (None, _) -> failwith "Missing binder in refinement"
        | b -> 
          let b, env = match as_binder env false (Inr b) with 
            | (Inr x, _), env -> x, env
            | _ -> failwith "impossible" in
          let f = desugar_formula env f in
          pos <| mk_Typ_refine(b, f)
      end

    | Paren t ->
      desugar_typ env t

    | Ascribed(t,k) ->
      pos <| mk_Typ_ascribed'(desugar_typ env t, desugar_kind env k)

    | Sum(binders, t) -> 
      if contains_binder binders
      then let env, _, targs = List.fold_left (fun (env, tparams, typs) b ->
             let xopt, t = desugar_exp_binder env b in
             let env, x = match xopt with
                          | None -> env, new_bvd (Some top.range)
                          | Some x -> push_local_vbinding env x in
             (env, tparams@[Inr (bvd_to_bvar_s x t), false], typs@[targ <| close_with_lam tparams t]))
             (env, [], []) (binders@[mk_binder (NoName t) t.range Type false]) in
           let tup = fail_or env  (try_lookup_typ_name env) (Util.mk_dtuple_lid (List.length targs) top.range) in
           pos <| mk_Typ_app(tup, targs)
           
      else let env, targs = List.fold_left (fun (env, typs) b ->
              let xopt, t = desugar_exp_binder env b in
              let _ = match xopt with
                | None -> ()
                | Some _ -> failwith "Impossible" in
              (env, typs@[targ t]))
              (env, []) (binders@[mk_binder (NoName t) t.range Type false]) in
           let tup = fail_or env  (try_lookup_typ_name env) (Util.mk_tuple_lid (List.length targs) top.range) in
           pos <| mk_Typ_app(tup, targs)
   
    | Record _ -> failwith "Unexpected record type"

    | If _  
    | Labeled _ -> desugar_formula env top
    | _ when (top.level=Formula) -> desugar_formula env top

    | _ -> error "Expected a type" top top.range

and desugar_kind env k : knd =
  let pos f = f k.range in
  let setpos kk = {kk with pos=k.range} in
  let k = unparen k in
  match k.tm with
    | Name {str="Type"} -> setpos mk_Kind_type
    | Name l -> 
      begin match DesugarEnv.find_kind_abbrev env (DesugarEnv.qualify_lid env l) with 
        | Some (_, [], def) -> pos <| mk_Kind_abbrev((l, []), def)
        | _ -> error "Unexpected term where kind was expected" k k.range
       end
    | Wild           -> setpos kun
    | Product(bs, k) -> 
      let bs, k = uncurry bs k in
      let rec aux env bs = function 
        | [] ->   
          pos <| mk_Kind_arrow(List.rev bs, desugar_kind env k)
        | hd::tl -> 
          let b, env = desugar_binder (ml env) hd |> as_binder env hd.implicit in
          aux env (b::bs) tl in
      aux env [] bs

    | Construct(l, args) -> 
      begin match DesugarEnv.find_kind_abbrev env (DesugarEnv.qualify_lid env l) with 
        | None -> error "Unexpected term where kind was expected" k k.range
        | Some (_, binders, def) -> 
          if List.length binders <> List.length args
          then error "Not enough arguments to kind abberviation" k k.range
          else 
            let subst = List.map2 (fun ax (t, _) -> match ax with 
              | Inl a -> Inl(a, desugar_typ env t)
              | Inr x -> Inr(x, desugar_exp env t)) binders args in 
            let k = Util.subst_kind (mk_subst subst) def in 
            pos <| mk_Kind_abbrev((l, subst |> List.map (function Inl(_, t) -> targ t | Inr(_, e) -> varg e)), k)
      end
    | _ -> error "Unexpected term where kind was expected" k k.range

and desugar_formula' env (f:term) : typ =
  let connective s = match s with
    | "/\\"  -> Some Const.and_lid
    | "\\/"  -> Some Const.or_lid
    | "==>"  -> Some Const.imp_lid
    | "<==>" -> Some Const.iff_lid
    | "~"    -> Some Const.not_lid
    | _ -> None in
  let pos t = t kun f.range in
  let setpos t = {t with pos=f.range} in
  let desugar_quant (q:lident) (qt:lident) b pats body =
    let tk = desugar_binder env ({b with blevel=Formula}) in
    match tk with
      | Inl(Some a,k) ->
        let env, a = push_local_tbinding env a in
        let pats = List.map (fun e -> withimp false <| desugar_typ_or_exp env e) pats in
        let body = desugar_formula env body in
        let body = match pats with
          | [] -> body
          | _ -> setpos <| mk_Typ_meta (Meta_pattern(body, pats)) in
        let body = pos <| mk_Typ_lam([t_binder (bvd_to_bvar_s a k)], body) in
        setpos <| mk_typ_app (ftv (set_lid_range qt b.brange) kun) [targ body]
            
      | Inr(Some x,t) ->
        let env, x = push_local_vbinding env x in
        let pats = List.map (fun e -> withimp false <| desugar_typ_or_exp env e) pats in
        let body = desugar_formula env body in
        let body = match pats with
          | [] -> body
          | _ -> mk_Typ_meta (Meta_pattern(body, pats)) in
        let body = pos <| mk_Typ_lam([v_binder (bvd_to_bvar_s x t)], body) in
        setpos <| mk_typ_app (ftv (set_lid_range q b.brange) kun) [targ body]

      | _ -> failwith "impossible" in
            
  let push_quant q (binders:list<AST.binder>) pats (body:term) = match binders with
    | b::(b'::_rest) ->
      let rest = b'::_rest in
      let body = mk_term (q(rest, pats, body)) (Range.union_ranges b'.brange body.range) Formula in
      mk_term (q([b], [], body)) f.range Formula
    | _ -> failwith "impossible" in

  match (unparen f).tm with
    | Labeled(f, l, p) -> 
      let f = desugar_formula env f in
      mk_Typ_meta(Meta_labeled(f, l, p))

    | Op("==", ((hd::_args))) ->
      let args = hd::_args in
      let args = List.map (fun t -> withimp false <| desugar_typ_or_exp env t) args in
      let eq =
        if is_type env hd
        then ftv (set_lid_range Const.eqT_lid f.range) kun
        else ftv (set_lid_range Const.eq2_lid f.range) kun in
      mk_typ_app eq args

    | Op(s, args) ->
      begin match connective s, args with
        | Some conn, [_;_] ->
          mk_typ_app
            (ftv (set_lid_range conn f.range) kun)
            (List.map (fun x -> targ <| desugar_formula env x) args)
        | _ -> desugar_typ env f
      end
        
    | If(f1, f2, f3) ->
      mk_typ_app
        (ftv (set_lid_range Const.ite_lid f.range) kun)
        (List.map (fun x -> 
            match desugar_typ_or_exp env x with
                | Inl t -> targ t
                | Inr v -> targ <| (Util.b2t v)) //implicitly coerce a boolean to a type
         [f1;f2;f3])

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

    | _ -> 
      if is_type env f 
      then desugar_typ env f
      else Util.b2t <| desugar_exp env f //implicitly coerce a boolean to a type
and desugar_formula env t =
  desugar_formula' ({env with phase=Formula}) t

and desugar_binder env b =
  if is_type_binder env b
  then Inl (desugar_type_binder env b)
  else Inr (desugar_exp_binder env b)

and typars_of_binders env bs =
    let env, tpars = List.fold_left (fun (env, out) b ->
        let tk = desugar_binder env ({b with blevel=Formula}) in  (* typars follow the same binding conventions as formulas *)
        match tk with
            | Inl(Some a, k) -> 
                let env, a = push_local_tbinding env a in
                (env, (Inl(bvd_to_bvar_s a k), false)::out)
            | Inr(Some x,t) ->
                let env, x = push_local_vbinding env x in
                (env, (Inr(bvd_to_bvar_s x t), false)::out)
            | _ -> raise (Error ("Unexpected binder", b.brange))) (env, []) bs in
    env, List.rev tpars

and desugar_exp_binder env b = match b.b with
  | Annotated(x, t) -> Some x, desugar_typ env t
  | TVariable t -> None, fail_or2 (try_lookup_typ_var env) t
  | NoName t -> None, desugar_typ env t
  | Variable x -> Some x, tun
  | _ -> raise (Error("Unexpected domain of an arrow or sum (expected a type)", b.brange))
    
and desugar_type_binder env b = match b.b with
  | TAnnotated(x, t) -> Some x, desugar_kind env t
  | NoName t -> None, desugar_kind env t
  | TVariable x -> Some x, {mk_Kind_type with pos=b.brange}
  | _ -> raise (Error("Unexpected domain of an arrow or sum (expected a kind)", b.brange))

let mk_data_ops env = function
  | Sig_datacon(lid, t, _, _, _) when (not env.iface && not (lid_equals lid Const.lexpair_lid)) ->
    let formals, tconstr = match Util.function_formals t with
        | Some(args, cod) -> args, Util.comp_result cod
        | _ -> [], t in
    //Printf.printf "Collecting formals from type %s; got %s with args %s\n" (Print.typ_to_string t) (Print.typ_to_string tconstr) (Print.binders_to_string ", " formals);
    let argpats = formals |> List.map (fun b -> match b with
      | Inr x, _ -> if is_null_binder b 
                    then Pat_var (new_bvd (Some (range_of_lid lid)))
                    else Pat_var x.v
      | Inl a, _ -> Pat_tvar a.v) in
    let freevs = freevars_typ tconstr in
    let freevars = formals |> List.filter (function
      | Inl a, _ -> Util.set_mem a freevs.ftvs
      | Inr x, _ -> Util.set_mem x freevs.fxvs
      | _ -> false) in
    //Printf.printf "Got %d free vars\n" (List.length freevars);
    let freeterms = freevars |> List.map (function 
      | Inl a, _ -> targ <| btvar_to_typ a
      | Inr x, _ -> varg <| bvar_to_exp x) in
    let r = range_of_lid lid in
    let formal = Util.gen_bvar_p r tconstr in
    let formal_exp = bvar_to_exp formal in
    let binders = freevars@[v_binder formal] in
    let rec build_typ t = mk_Typ_fun'(binders, mk_Total t) kun r in
    let rec build_kind k = mk_Kind_arrow'(binders, k) k.pos in
//    let subst_to_string s = 
//      List.map (function 
//        | Inl (a, t) -> Util.format2 "(%s -> %s)" (Print.strBvd a) (Print.typ_to_string t)  
//        | Inr (x, e) -> Util.format2 "(%s -> %s)" (Print.strBvd x) (Print.exp_to_string e)) s 
//      |> String.concat ", " in  
//    let subst_typ s t =
//      //Printf.printf "Substituting [%s] in type\n%s\n" (subst_to_string s) (Print.typ_to_string t);
//      let res = subst_typ s t in  res in
//      //Printf.printf "Got\n%s\n" (Print.typ_to_string res); flush stdout; res in
    let rec projectors data_ops subst formals = match formals with 
      | [] -> data_ops
      | b::rest -> 
        if is_null_binder b then projectors data_ops subst rest else
        let proj, subst = match fst b with
           | Inr x ->
                let y = {x.v with ppname=unmangle_field_name x.v.ppname} in
                let field_name = lid_of_ids (ids_of_lid lid @ [y.ppname]) in
                let t = build_typ (Util.subst_typ subst x.sort) in
                let sigs = [Sig_val_decl(field_name, t, [Assumption; Logic; Projector(lid, Inr y)], range_of_lid field_name)] in
                let subst = if Util.set_mem x freevs.fxvs
                            then subst
                            else Inr(x.v, mk_exp_app (fvar field_name (range_of_lid field_name)) (freeterms@[varg <| formal_exp]))::subst in
                sigs, subst
        
            | Inl a -> 
                let field_name = lid_of_ids (ids_of_lid lid @ [a.v.ppname]) in
                let kk = build_kind (Util.subst_kind subst a.sort) in
                let sigs = [Sig_tycon(field_name, [], kk, [], [], [Logic; Projector(lid, Inl a.v)], range_of_lid field_name)] in
                //let _ = Util.print_string (Util.format2 "adding type projector %s at type %s\n" field_name.str (Print.kind_to_string kk)) in 
                let subst = if Util.set_mem a freevs.ftvs
                            then subst
                            else Inl(a.v, mk_typ_app (ftv field_name kun) (freeterms@[varg <| formal_exp]))::subst in
                sigs, subst in
         projectors (data_ops@proj) subst rest in
       
    let disc_name = Util.mk_discriminator lid in
    let disc = Sig_val_decl(disc_name, build_typ (Util.ftv Const.bool_lid ktype), [Assumption; Logic; Discriminator lid], range_of_lid disc_name) in
    projectors [disc] [] formals

  | _ -> []

let rec desugar_tycon env rng quals tcs : (env_t * sigelts) =
  let tycon_id = function
    | TyconAbstract(id, _, _)
    | TyconAbbrev(id, _, _, _)
    | TyconRecord(id, _, _, _)
    | TyconVariant(id, _, _, _) -> id in
  let binder_to_term b = match b.b with
    | Annotated (x, _)
    | Variable x -> mk_term (Var (lid_of_ids [x])) x.idRange Expr
    | TAnnotated(a, _)
    | TVariable a -> mk_term (Tvar a) a.idRange Type
    | NoName t -> t in
  let tot = mk_term (Name (Const.p2l ["PURE"; "Tot"])) rng Expr in 
  let with_constructor_effect t = mk_term (App(tot, t, false)) t.range t.level in
  let add_constructor_effect t = match (unparen t).tm with
    | Product _ -> 
      let rec aux t = match t.tm with 
        | Product(binders, s) ->  mk_term (Product(binders, aux s)) t.range t.level
        | Paren s -> mk_term (Paren(aux s)) s.range s.level
        | _ -> with_constructor_effect t in
      aux t
    | _ -> t in
  let apply_binders t binders =
    List.fold_left (fun out b -> mk_term (App(out, binder_to_term b, false)) out.range out.level)
      t binders in
  let tycon_record_as_variant = function
    | TyconRecord(id, parms, kopt, fields) ->
      let constrName = mk_ident("Mk" ^ id.idText, id.idRange) in
      let mfields = List.map (fun (x,t) -> mk_binder (Annotated(mangle_field_name x,t)) x.idRange Expr false) fields in
      let result = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type) parms in
      let constrTyp = mk_term (Product(mfields, with_constructor_effect result)) id.idRange Type in
      //let _ = Util.print_string (Util.format2 "Translated record %s to constructor %s\n" (id.idText) (term_to_string constrTyp)) in 
      TyconVariant(id, parms, kopt, [(constrName, Some constrTyp, false)]), fields |> List.map fst
    | _ -> failwith "impossible" in
  let desugar_abstract_tc quals _env mutuals = function
    | TyconAbstract(id, binders, kopt) ->
      let _env', typars = typars_of_binders _env binders in
      let k = match kopt with
        | None -> kun
        | Some k -> desugar_kind _env' k in
      let tconstr = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type) binders in
      let qlid = qualify _env id in
      let se = Sig_tycon(qlid, typars, k, mutuals, [], quals, rng) in
      let _env = push_rec_binding _env (Binding_tycon qlid) in
      let _env2 = push_rec_binding _env' (Binding_tycon qlid) in
      _env, (_env2, typars), se, tconstr
    | _ -> failwith "Unexpected tycon" in
  let push_tparam env = function
    | Inr x, _ -> push_bvvdef env x.v
    | Inl a, _ -> push_btvdef env a.v in
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
            | None -> 
              if Util.for_some (function Effect -> true | _ -> false) quals
              then mk_Kind_effect
              else kun
            | Some k -> desugar_kind env' k in
        let t = desugar_typ env' t in
        let se = Sig_typ_abbrev(qualify env id, typars, k, t, quals, rng) in
        let env = push_sigelt env se in
        env, [se]

    | [TyconRecord _] ->
      let trec = List.hd tcs in
      let t, fs = tycon_record_as_variant trec in
      desugar_tycon env rng (RecordType fs::quals) [t]

    |  _::_ ->
      let env0 = env in
      let mutuals = List.map (fun x -> qualify env <| tycon_id x) tcs in
      let rec collect_tcs etq tc = 
        let (env, tcs, quals) = etq in
        match tc with
          | TyconRecord _ ->
            let trec = tc in
            let t, fs = tycon_record_as_variant trec in
            collect_tcs (env, tcs, RecordType fs::quals) t
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
        | Inr(Sig_tycon(id, tpars, k, _, _, _, _), tps, t) ->
          let env_tps = push_tparams env tps in
          let t = desugar_typ env_tps t in
          [Sig_typ_abbrev(id, tpars, k, t, [], rng)]
            
        | Inl (Sig_tycon(tname, tpars, k, mutuals, _, tags, _), tps, constrs, tconstr) ->
          let env_tps = push_tparams env tps in
          let constrNames, constrs = List.split <|
              (constrs |> List.map (fun (id, topt, of_notation) ->
                let t =
                  if of_notation
                  then match topt with 
                    | Some t -> mk_term (Product([mk_binder (NoName t) t.range t.level false], tconstr)) t.range t.level
                    | None -> tconstr 
                  else match topt with 
                    | None -> failwith "Impossible"
                    | Some t -> t in
                let t = desugar_typ (total env_tps) (close env_tps t) in
                let name = qualify env id in
                let quals = tags |> List.collect (function 
                    | RecordType fns -> [RecordConstructor fns]
                    | _ -> []) in
                (name, Sig_datacon(name, close_typ tps t, tname, quals, rng)))) in
              Sig_tycon(tname, tpars, k, mutuals, constrNames, tags, rng)::constrs
        | _ -> failwith "impossible") in
      let bundle = Sig_bundle(sigelts, rng, List.collect Util.lids_of_sigelt sigelts) in
      let env = push_sigelt env0 bundle in
      let data_ops = sigelts |> List.collect (mk_data_ops env) in
      let env = List.fold_left push_sigelt env data_ops in
      env, [bundle]@data_ops

    | [] -> failwith "impossible"

let desugar_kind_abbrev r env id binders k = 
  let env_k, binders = List.fold_left (fun (env,binders) b -> 
    match desugar_binder env b with
      | Inl(Some a, k) -> 
        let env, ax = DesugarEnv.push_local_binding env (DesugarEnv.Binding_typ_var a) in
        env, ax::binders
      | Inr(Some x, t) -> 
        let env, ax = DesugarEnv.push_local_binding env (DesugarEnv.Binding_var x) in 
        env, ax::binders
      | _ -> raise (Error("Missing name in binder for kind abbreviation", r))) (env, []) binders in 
  let k = desugar_kind env_k k in 
  let name = DesugarEnv.qualify env id in
  let binders = List.rev binders in
  let env = DesugarEnv.push_kind_abbrev env (name, binders, k) in
  env, (name, binders, k)
           
let rec desugar_decl env (d:decl) : (env_t * sigelts) = match d.d with
  | Open lid ->
    let env = DesugarEnv.push_namespace env lid in
    env, []
  
  | Tycon(qual, tcs) ->
    desugar_tycon env d.drange qual tcs
          
  | ToplevelLet(isrec, lets) ->
    begin match (compress_exp <| desugar_exp_maybe_top true env (mk_term (Let(isrec, lets, mk_term (Const Const_unit) d.drange Expr)) d.drange Expr)).n with
        | Exp_let(lbs, _) ->
          let lids = snd lbs |> List.map (function 
            | (Inr l, _, _) -> l
            | _ -> failwith "impossible") in
          let s = Sig_let(lbs, d.drange, lids) in
          let env = push_sigelt env s in
          env, [s]
        | _ -> failwith "Desugaring a let did not produce a let"
    end

  | Main t ->
    let e = desugar_exp env t in
    let se = Sig_main(e, d.drange) in
    env, [se]

  | Assume(atag, id, t) ->
    let f = desugar_formula env t in
    env, [Sig_assume(qualify env id, f, [Public; Assumption], d.drange)]

  | Val(quals, id, t) -> 
    let t = desugar_typ env (close env t) in
    let se = Sig_val_decl(qualify env id, t, quals, d.drange) in
    let env = push_sigelt env se in
    env, [se]

  | Exception(id, None) ->
    let t = fail_or env  (try_lookup_typ_name env) Const.exn_lid in
    let l = qualify env id in
    let se = Sig_datacon(l, t, Const.exn_lid, [ExceptionConstructor], d.drange) in
    let se' = Sig_bundle([se], d.drange, [l]) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_ops env se in
    let env = List.fold_left push_sigelt env data_ops in
    env, se'::data_ops
        
  | Exception(id, Some term) ->
    let t = desugar_typ env term in
    let t = mk_Typ_fun([null_v_binder t], mk_Total (fail_or env (try_lookup_typ_name env) Const.exn_lid)) kun d.drange in
    let l = qualify env id in
    let se = Sig_datacon(l, t, Const.exn_lid, [ExceptionConstructor], d.drange) in
    let se' = Sig_bundle([se], d.drange, [l]) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_ops env se in
    let env = List.fold_left push_sigelt env data_ops in
    env, se'::data_ops
   
  | KindAbbrev(id, binders, k) ->
    let env, _ = desugar_kind_abbrev d.drange env id binders k in 
    env, []

  | MonadLat(monads, lifts) -> 
    let desugar_monad_sig env0 (m:AST.monad_sig) = 
      let menv = DesugarEnv.enter_monad_scope env0 m.mon_name in
      let menv, kabbrevs, kmon = List.fold_left (fun (menv, kabbrevs, kmon) d -> 
        match d.d with 
          | KindAbbrev(id, binders, k) when (id.idText="WP") -> 
            let menv, (lid, binders, kwp) = desugar_kind_abbrev d.drange menv id binders k in 
            let args = binders |> List.map (function
              | Inl a -> targ <| Util.bvd_to_typ a mk_Kind_type
              | Inr x -> varg <| Util.bvd_to_exp x tun)  in
            let kwp = mk_Kind_abbrev((lid, args), kwp) d.drange in
            let kmon = match binders with 
              | [Inl a] -> 
                mk_Kind_arrow([t_binder <| bvd_to_bvar_s a ktype;
                               null_t_binder kwp;
                               null_t_binder kwp],
                              keffect) d.drange
              | _ -> raise (Error("Unexpected binders in the signature of WP (expected a single type parameter)", d.drange)) in
            menv, (lid, binders, kwp)::kabbrevs, Some kmon
          | KindAbbrev(id, binders, k) -> 
            let menv, kabr = desugar_kind_abbrev d.drange menv id binders k in
            menv, kabr::kabbrevs, kmon
          | _ -> 
            let menv, _ = desugar_decl menv d in 
            menv, kabbrevs, kmon) (menv, [], None) m.mon_decls in
      let kmon = match kmon with
        | None -> raise (Error("Monad " ^m.mon_name.idText^ " expects WP to be defined", d.drange))
        | Some k -> k in
      let lookup s = match DesugarEnv.try_resolve_typ_abbrev menv (DesugarEnv.qualify menv (Syntax.mk_ident(s, d.drange))) with
        | None -> raise (Error("Monad " ^m.mon_name.idText^ " expects definition of "^s, d.drange))
        | Some t -> t in
      let m_decl = Sig_tycon(qualify env0 m.mon_name, [], kmon, [], [], [], d.drange) in
      let menv = DesugarEnv.push_sigelt menv m_decl in
      let menv, abbrevs = m.mon_abbrevs |> List.fold_left (fun (menv, out) (id, binders, t) -> 
          let menv, ses = desugar_tycon menv d.drange [Effect] [TyconAbbrev(id, binders, None, t)] in
          menv, List.hd ses::out) (menv, []) in
      let m_abbrevs = List.rev abbrevs in
      let msig = {mname=qualify env m.mon_name;
         total=m.mon_total;
         signature=kmon;
         ret=lookup "return";
         bind_wp=lookup "bind_wp";
         bind_wlp=lookup "bind_wlp";
         ite_wp=lookup "ite_wp";
         ite_wlp=lookup "ite_wlp";
         wp_binop=lookup "wp_binop";
         wp_as_type=lookup "wp_as_type";
         close_wp=lookup "close_wp";
         close_wp_t=lookup "close_wp_t";
         assert_p=lookup "assert_p";
         assume_p=lookup "assume_p";
         null_wp=lookup "null_wp";
         trivial=lookup "trivial";
         abbrevs=m_abbrevs} in
      let env = DesugarEnv.exit_monad_scope env0 menv in 
      env, msig in
    let env, msigs = List.fold_left (fun (env, msigs) m -> 
      let env, msig = desugar_monad_sig env m in
      env, msig::msigs) (env, []) monads in
    let order = lifts |> List.map (fun l -> 
      let t = desugar_typ env (l.lift_op) in
      {source=qualify env (l.msource);
       target=qualify env (l.mdest);
       lift=t}) in
    let lids = msigs |> List.map (fun m -> m.mname) in
    let se = Sig_monads(List.rev msigs, order, d.drange, lids) in
    push_sigelt env se, [se]
   

  | _ -> raise (Error("Unexpected declaration", d.drange))
        
let desugar_modul env (m:AST.modul) : env_t * Syntax.modul = 
  let open_ns (mname:lident) d = 
    if List.length mname.ns <> 0 
    then (AST.mk_decl (AST.Open (Syntax.lid_of_ids mname.ns)) (Syntax.range_of_lid mname))  :: d
    else d in
  let env, mname, decls, intf = match m with
    | Interface(mname, decls) -> DesugarEnv.prepare_module_or_interface true env mname, mname, open_ns mname decls, true
    | Module(mname, decls) -> DesugarEnv.prepare_module_or_interface false env mname, mname, open_ns mname decls, false in
  let env, sigelts = List.fold_left (fun (env, sigelts) d ->
    let env, se = desugar_decl env d in
    env, sigelts@se) (env, []) decls in
  let modul = {
    name = mname;
    declarations = sigelts;
    exports = [];
    is_interface=intf
  } in
  let env = DesugarEnv.finish_module_or_interface env modul in
  env, modul
  
let desugar_file env (f:file) =
  let pragmas, ms = f in
  let env, mods = List.fold_left (fun (env, mods) m ->
    let env, m = desugar_modul env m in
    env, m::mods) (env, []) ms in
  env, List.rev mods
