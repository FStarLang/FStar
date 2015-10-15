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
module FStar.Parser.Desugar

open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.DesugarEnv
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Util
open FStar.Util

let as_imp = function
    | Hash
    | FsTypApp -> Some Implicit
    | _ -> None
let arg_withimp_e imp t =
    t, as_imp imp
let arg_withimp_t imp t =
    match imp with
        | Hash -> t, Some Implicit
        | _ -> t, None

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


let compile_op arity s =
    let name_of_char = function
            |'&' -> "Amp"
            |'@'  -> "At"
            |'+' -> "Plus"
            |'-' when (arity=1) -> "Minus"
            |'-' -> "Subtraction"
            |'/' -> "Slash"
            |'<' -> "Less"
            |'=' -> "Equals"
            |'>' -> "Greater"
            |'_' -> "Underscore"
            |'|' -> "Bar"
            |'!' -> "Bang"
            |'^' -> "Hat"
            |'%' -> "Percent"
            |'*' -> "Star"
            |'?' -> "Question"
            |':' -> "Colon"
            | _ -> "UNKNOWN" in
    let rec aux i =
        if i = String.length s
        then []
        else name_of_char (Util.char_at s i) :: aux (i + 1) in
    "op_"^ (String.concat "_" (aux 0))

let compile_op_lid n s r = [Syntax.mk_ident(compile_op n s, r)] |> Syntax.lid_of_ids

let     op_as_vlid env arity rng s =
  let r l = Some (set_lid_range l rng) in
  let fallback () =
      match s with
        | "=" ->    r Const.op_Eq
        | ":=" ->   r Const.op_ColonEq
        | "<" ->    r Const.op_LT
        | "<=" ->   r Const.op_LTE
        | ">" ->    r Const.op_GT
        | ">=" ->   r Const.op_GTE
        | "&&" ->   r Const.op_And
        | "||" ->   r Const.op_Or
        | "*" ->    r Const.op_Multiply
        | "+" ->    r Const.op_Addition
        | "-" when (arity=1) -> r Const.op_Minus
        | "-" ->    r Const.op_Subtraction
        | "/" ->    r Const.op_Division
        | "%" ->    r Const.op_Modulus
        | "!" ->    r Const.read_lid
        | "@" ->    r Const.list_append_lid
        | "^" ->    r Const.strcat_lid
        | "|>" ->   r Const.pipe_right_lid
        | "<|" ->   r Const.pipe_left_lid
        | "<>" ->   r Const.op_notEq
        | _ -> None in
   begin match DesugarEnv.try_lookup_lid env (compile_op_lid arity s rng) with
        | Some ({n=Exp_fvar(fv, _)}) -> Some fv.v
        | _ -> fallback()
   end

let op_as_tylid env arity rng s =
  let r l = Some (set_lid_range l rng) in
  match s with
    | "~"   ->  r Const.not_lid
    | "=="  ->  r Const.eq2_lid
    | "=!=" ->  r Const.neq2_lid
    | "<<" ->   r Const.precedes_lid
    | "/\\" ->  r Const.and_lid
    | "\\/" ->  r Const.or_lid
    | "==>" ->  r Const.imp_lid
    | "<==>" -> r Const.iff_lid
    | s ->
      begin match DesugarEnv.try_lookup_typ_name env (compile_op_lid arity s rng) with
        | Some ({n=Typ_const ftv}) -> Some ftv.v
        | _ -> None
      end

let rec is_type env (t:term) =
  if t.level = Type then true
  else match (unparen t).tm with
    | Wild -> true
    | Labeled _ -> true
    | Op("*", hd::_) -> is_type env hd     (* tuple constructor *)
    | Op("==", _)                          (* equality predicate *)
    | Op("=!=", _)
    | Op("~", _)
    | Op("/\\", _)
    | Op("\\/", _)
    | Op("==>", _)
    | Op("<==>", _)
    | Op("<<", _) -> true
    | Op(s, args) -> (match op_as_tylid env (List.length args) t.range s with
        | None -> false
        | _ -> true)
    | QForall _
    | QExists _
    | Sum _
    | Refine _
    | Tvar _
    | NamedTyp _ -> true
    | Var l
    | Name l when (List.length l.ns = 0) ->
      begin match DesugarEnv.try_lookup_typ_var env l.ident with
        | Some _ -> true
        | _ -> is_type_lid env l
      end
    | Var l
    | Name l
    | Construct(l, _) -> is_type_lid env l
    | App({tm=Var l}, arg, Nothing)
    | App({tm=Name l}, arg, Nothing) when (l.str = "ref") ->
      is_type env arg
    | App(t, _, _)
    | Paren t
    | Ascribed(t, _) -> is_type env t
    | Product(_, t) -> not (is_kind env t)
    | If(t, t1, t2) -> is_type env t || is_type env t1 || is_type env t2
    | Abs(pats, t) ->
       let rec aux env pats = match pats with
        | [] -> is_type env t
        | hd::pats ->
          begin match hd.pat with
            | PatWild
            | PatVar _ -> aux env pats  //these do not help in identifying a type
            | PatTvar (id, _) ->
              let env, _ = DesugarEnv.push_local_tbinding env id in
              aux env pats
            | PatAscribed (p, tm) ->
              let env = if is_kind env tm
                        then match p.pat with
                                | PatVar (id, _)
                                | PatTvar (id, _) -> DesugarEnv.push_local_tbinding env id |> fst
                                | _ -> env
                        else env in
              aux env pats
            | _ -> false //no other patterns are permitted in type functions
         end in
       aux env pats
    | _ -> false

and is_kind env (t:term) : bool =
  if t.level = Kind
  then true
  else match (unparen t).tm with
    | Name {str="Type"} -> true
    | Product(_, t) -> is_kind env t
    | Paren t -> is_kind env t
    | Construct(l, _)
    | Name l -> DesugarEnv.is_kind_abbrev env l//(DesugarEnv.qualify_lid env l)
    | _ -> false

let rec is_type_binder env b =
  if b.blevel = Formula
  then match b.b with
    | Variable _ -> false
    | TAnnotated _
    | TVariable _ -> true
    | Annotated(_, t)
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
  | NamedTyp(_, t)
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

  | Project(t, _) -> free_type_vars env t


  | Abs _  (* not closing implicitly over free vars in type-level functions *)
  | If _
  | QForall _
  | QExists _ -> [] (* not closing implicitly over free vars in formulas *)
  | Let _
  | Record _
  | Match _
  | TryWith _
  | Seq _ -> error "Unexpected type in free_type_vars computation" t t.range

let head_and_args t =
    let rec aux args t = match (unparen t).tm with
        | App(t, arg, imp) -> aux ((arg,imp)::args) t
        | Construct(l, args') -> {tm=Name l; range=t.range; level=t.level}, args'@args
        | _ -> t, args in
    aux [] t

let close env t =
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, kind_star x.idRange)) x.idRange Type (Some Implicit)) in
       let result = mk_term (Product(binders, t)) t.range t.level in
       result

let close_fun env t =
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, kind_star x.idRange)) x.idRange Type (Some Implicit)) in
       let t = match (unlabel t).tm with
        | Product _ -> t
        | _ -> mk_term (App(mk_term (Name Const.effect_Tot_lid) t.range t.level, t, Nothing)) t.range t.level in
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
  | PatApp({pat=PatVar (id, _)}, args) when is_top_level ->
    (Inr (qualify env id), args, None)
  | PatApp({pat=PatVar (id, _)}, args) ->
    (Inl id, args, None)
  | _ ->
    failwith "Not an app pattern"

type bnd =
  | TBinder   of btvdef * knd * Syntax.aqual
  | VBinder   of bvvdef * typ * Syntax.aqual
  | LetBinder of lident * typ
let binder_of_bnd = function
  | TBinder (a, k, aq) -> Inl (Util.bvd_to_bvar_s a k), aq
  | VBinder (x, t, aq) -> Inr (Util.bvd_to_bvar_s x t), aq
  | _ -> failwith "Impossible"
let as_binder env imp = function
  | Inl(None, k) -> null_t_binder k, env
  | Inr(None, t) -> null_v_binder t, env
  | Inl(Some a, k) ->
    let env, a = DesugarEnv.push_local_tbinding env a in
    (Inl (bvd_to_bvar_s a k), imp), env
  | Inr(Some x, t) ->
    let env, x = DesugarEnv.push_local_vbinding env x in
    (Inr (bvd_to_bvar_s x t), imp), env

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

let mk_lb (n, t, e) = {lbname=n; lbeff=Const.effect_ALL_lid; lbtyp=t; lbdef=e}

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
    let pos q = Syntax.withinfo q None p.prange in
    let pos_r r q = Syntax.withinfo q  None r in
    match p.pat with
      | PatOr [] -> failwith "impossible"
      | PatOr (p::ps) ->
        let loc, env, var, p, _ = aux loc env p in
        let loc, env, ps = List.fold_left (fun (loc, env, ps) p ->
          let loc, env, _, p, _ = aux loc env p in
          loc, env, p::ps) (loc, env, []) ps in
        let pat = pos <| Pat_disj (p::List.rev ps) in
        ignore (pat_vars pat);
        loc, env, var, pat, false

      | PatAscribed(p, t) ->
        let p = if is_kind env t
                then match p.pat with
                        | PatTvar _ -> p
                        | PatVar (x, imp) -> {p with pat=PatTvar (x, imp)}
                        | _ -> raise (Error ("Unexpected pattern", p.prange))
                else p in
        let loc, env', binder, p, imp = aux loc env p in
        let binder = match binder with
            | LetBinder _ -> failwith "impossible"
            | TBinder(x, _, aq) -> TBinder(x, desugar_kind env t, aq)
            | VBinder(x, _, aq) ->
                let t = close_fun env t in
                VBinder(x, desugar_typ env t, aq) in
        loc, env', binder, p, imp

      | PatTvar (a, imp) ->
        let aq = if imp then Some Implicit else None in
        if a.idText = "'_"
        then let a = new_bvd <| Some p.prange in
             loc, env, TBinder(a, kun, aq), pos <| Pat_twild (bvd_to_bvar_s a kun), imp
        else let loc, env, abvd = resolvea loc env a in
             loc, env, TBinder(abvd, kun, aq), pos <| Pat_tvar (bvd_to_bvar_s abvd kun), imp

      | PatWild ->
        let x = new_bvd (Some p.prange) in
        let y = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun, None), pos <| Pat_wild (bvd_to_bvar_s y tun), false

      | PatConst c ->
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun, None), pos <| Pat_constant c, false

      | PatVar (x, imp) ->
        let aq = if imp then Some Implicit else None in
        let loc, env, xbvd = resolvex loc env x in
        loc, env, VBinder(xbvd, tun, aq), pos <| Pat_var (bvd_to_bvar_s xbvd tun), imp

      | PatName l ->
        let l = fail_or env (try_lookup_datacon env) l in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun, None), pos <| Pat_cons(l, Some Data_ctor, []), false

      | PatApp({pat=PatName l}, args) ->
        let loc, env, args = List.fold_right (fun arg (loc,env,args) ->
          let loc, env, _, arg, imp = aux loc env arg in
          (loc, env, (arg, imp)::args)) args (loc, env, []) in
        let l = fail_or env  (try_lookup_datacon env) l in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun, None), pos <| Pat_cons(l, Some Data_ctor, args), false

      | PatApp _ -> raise (Error ("Unexpected pattern", p.prange))

      | PatList pats ->
        let loc, env, pats = List.fold_right (fun pat (loc, env, pats) ->
          let loc,env,_,pat, _ = aux loc env pat in
          loc, env, pat::pats) pats (loc, env, []) in
        let pat = List.fold_right (fun hd tl ->
            let r = Range.union_ranges hd.p tl.p in
            pos_r r <| Pat_cons(Util.fv Const.cons_lid, Some Data_ctor, [(hd, false);(tl, false)])) pats
                        (pos_r (Range.end_range p.prange) <| Pat_cons(Util.fv Const.nil_lid, Some Data_ctor, [])) in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun, None), pat, false

      | PatTuple(args, dep) ->
        let loc, env, args = List.fold_left (fun (loc, env, pats) p ->
          let loc, env, _, pat, _ = aux loc env p in
          loc, env, (pat, false)::pats) (loc,env,[]) args in
        let args = List.rev args in
        let l = if dep then Util.mk_dtuple_data_lid (List.length args) p.prange
                else Util.mk_tuple_data_lid (List.length args) p.prange in
        let constr = fail_or env  (DesugarEnv.try_lookup_lid env) l in
        let l = match constr.n with
          | Exp_fvar (v, _) -> v
          | _ -> failwith "impossible" in
        let x = new_bvd (Some p.prange) in
        loc, env, VBinder(x, tun, None), pos <| Pat_cons(l, Some Data_ctor, args), false

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
        let env, e, b, p, _ = aux loc env app in
        let p = match p.v with
            | Pat_cons(fv, _, args) -> pos <| Pat_cons(fv, Some (Record_ctor (record.typename, record.fields |> List.map fst)), args)
            | _ -> p in
        env, e, b, p, false in

  let _, env, b, p, _ = aux [] env p in
  env, b, p

and desugar_binding_pat_maybe_top top env p : (env_t * bnd * option<pat>) =
  if top
  then match p.pat with
    | PatVar (x, _) -> (env, LetBinder(qualify env x, tun), None)
    | PatAscribed({pat=PatVar (x, _)}, t) ->
      (env, LetBinder(qualify env x, desugar_typ env t), None)
    | _ -> raise (Error("Unexpected pattern at the top-level", p.prange))
  else
    let (env, binder, p) = desugar_data_pat env p in
    let p = match p.v with
      | Pat_var _
      | Pat_tvar _
      | Pat_wild _ -> None
      | _ -> Some p in
    (env, binder, p)

and desugar_binding_pat env p = desugar_binding_pat_maybe_top false env p

and desugar_match_pat_maybe_top _ env pat =
  let (env, _, pat) = desugar_data_pat env pat in
  (env, pat)

and desugar_match_pat env p = desugar_match_pat_maybe_top false env p

and desugar_typ_or_exp (env:env_t) (t:term) : either<typ,exp> =
  if is_type env t
  then Inl (desugar_typ env t)
  else Inr (desugar_exp env t)

and desugar_exp env e = desugar_exp_maybe_top false env e

and desugar_exp_maybe_top (top_level:bool) (env:env_t) (top:term) : exp =
  let pos e = e None top.range in
  let setpos e = {e with pos=top.range} in
  begin match (unparen top).tm with
    | Const c -> pos <| mk_Exp_constant c

    | Op(s, args) ->
      begin match op_as_vlid env (List.length args) top.range s with
        | None -> raise (Error("Unexpected operator: " ^ s, top.range))
        | Some l ->
          let op = fvar None l (range_of_lid l) in
          let args = args |> List.map (fun t -> desugar_typ_or_exp env t, None) in
          setpos <| mk_exp_app op args
      end


    | Var l
    | Name l ->
      if l.str = "ref"
      then begin match DesugarEnv.try_lookup_lid env Const.alloc_lid with
            | None -> raise (Error ("Identifier 'ref' not found; include lib/st.fst in your path", range_of_lid l))
            | Some e -> setpos e
           end
      else setpos <| fail_or env (DesugarEnv.try_lookup_lid env) l

    | Construct(l, args) ->
      let dt = pos <| mk_Exp_fvar(fail_or env (DesugarEnv.try_lookup_datacon env) l, Some Data_ctor) in
      begin match args with
        | [] -> dt
        | _ ->
          let args = List.map (fun (t, imp) ->
            let te = desugar_typ_or_exp env t in
            arg_withimp_e imp te) args in
          setpos <| mk_Exp_meta(Meta_desugared(mk_exp_app dt args, Data_app))
      end

    | Abs(binders, body) ->
      let _, ftv = List.fold_left (fun (env, ftvs) pat ->
        match pat.pat with
          | PatAscribed ({pat=PatTvar (a, imp)}, t) ->
            let ftvs = free_type_vars env t@ftvs in
            fst <| DesugarEnv.push_local_tbinding env a, ftvs
          | PatTvar(a, _) -> fst <| DesugarEnv.push_local_tbinding env a, ftvs
          | PatAscribed(_, t) -> env, free_type_vars env t@ftvs
          | _ -> env, ftvs) (env, []) binders in
      let ftv = sort_ftv ftv in
      let binders = (ftv |> List.map (fun a -> mk_pattern (PatTvar(a, true)) top.range))@binders in //close over the free type variables

      let rec aux env bs sc_pat_opt = function
            | [] ->
              let body = desugar_exp env body in
              let body = match sc_pat_opt with
                | Some (sc, pat) -> mk_Exp_match(sc, [(pat, None, body)]) None body.pos
                | None -> body in
              mk_Exp_abs'(List.rev bs, body) None top.range

            | p::rest ->
              let env, b, pat = desugar_binding_pat env p in
              let b, sc_pat_opt = match b with
                | LetBinder _ -> failwith "Impossible"
                | TBinder (a,k,aq) -> binder_of_bnd b, sc_pat_opt
                | VBinder (x,t,aq) ->
                    let b = Util.bvd_to_bvar_s x t in
                    let sc_pat_opt = match pat, sc_pat_opt with
                        | None, _ -> sc_pat_opt
                        | Some p, None -> Some (Util.bvar_to_exp b, p)
                        | Some p, Some (sc, p') ->
                             begin match sc.n, p'.v with
                                | Exp_bvar _, _ ->
                                  let tup = Util.mk_tuple_data_lid 2 top.range in
                                  let sc = Syntax.mk_Exp_app(Util.fvar (Some Data_ctor) tup top.range, [varg sc; varg <| Util.bvar_to_exp b]) None top.range in
                                  let p = withinfo (Pat_cons(Util.fv tup, Some Data_ctor, [(p', false);(p, false)])) None (Range.union_ranges p'.p p.p) in
                                  Some(sc, p)
                                | Exp_app(_, args), Pat_cons(_, _, pats) ->
                                  let tup = Util.mk_tuple_data_lid (1 + List.length args) top.range in
                                  let sc = Syntax.mk_Exp_app(Util.fvar (Some Data_ctor) tup top.range, args@[(varg <| Util.bvar_to_exp b)]) None top.range in
                                  let p = withinfo (Pat_cons(Util.fv tup, Some Data_ctor, pats@[(p, false)])) None (Range.union_ranges p'.p p.p) in
                                  Some(sc, p)
                                | _ -> failwith "Impossible"
                              end in
                    (Inr b, aq), sc_pat_opt in
                aux env (b::bs) sc_pat_opt rest
       in
       aux env [] None binders

    | App({tm=Var a}, arg, _) when (lid_equals a Const.assert_lid
                                   || lid_equals a Const.assume_lid) ->
      let phi = desugar_formula env arg in
      pos <| mk_Exp_app(fvar None a (range_of_lid a),
                        [targ <| phi;
                         varg <| mk_Exp_constant(Const_unit) None top.range])

    | App _ ->
      let rec aux args e = match (unparen e).tm with
        | App(e, t, imp) ->
          let arg = arg_withimp_e imp <| desugar_typ_or_exp env t in
          aux (arg::args) e
        | _ ->
          let head = desugar_exp env e in
          pos <| mk_Exp_app(head, args) in
      aux [] top

    | Seq(t1, t2) ->
      setpos <| mk_Exp_meta(Meta_desugared(desugar_exp env (mk_term (Let(false, [(mk_pattern PatWild t1.range,t1)], t2)) top.range Expr),
                              Sequence))

    | Let(is_rec, ((pat, _snd)::_tl), body) ->
      let ds_let_rec () =
        let bindings = (pat, _snd)::_tl in
        let funs = bindings |> List.map (fun (p, def) ->
          if is_app_pattern p
          then destruct_app_pattern env top_level p, def
          else match un_function p def with
                | Some (p, def) -> destruct_app_pattern env top_level p, def
                | _ -> begin match p.pat with
                                | PatAscribed({pat=PatVar(id,_)}, t) ->
                                  if top_level
                                  then (Inr (qualify env id), [], Some t), def
                                  else (Inl id, [], Some t), def
                                | PatVar(id, _) ->
                                  if top_level
                                  then (Inr (qualify env id), [], None), def
                                  else (Inl id, [], None), def
                                | _ -> raise (Error("Unexpected let binding", p.prange))
                      end) in
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
        let desugar_one_def env lbname ((_, args, result_t), def) =
            let def = match result_t with
                | None -> def
                | Some t -> mk_term (Ascribed(def, t)) (Range.union_ranges t.range def.range) Expr in
            let def = match args with
                | [] -> def
                | _ -> mk_term (un_curry_abs args def) top.range top.level in
            let body = desugar_exp env def in
            mk_lb (lbname, tun, body) in
        let lbs = List.map2 (desugar_one_def (if is_rec then env' else env)) fnames funs in
        let body = desugar_exp env' body in
        pos <| mk_Exp_let((is_rec, lbs), body) in

      let ds_non_rec pat t1 t2 =
        let t1 = desugar_exp env t1 in
        let env, binder, pat = desugar_binding_pat_maybe_top top_level env pat in
        begin match binder with
          | TBinder _ -> failwith "Unexpected type binder in let"
          | LetBinder(l, t) ->
            let body = desugar_exp env t2 in
            pos <| mk_Exp_let((false, [({lbname=Inr l; lbeff=Const.effect_ALL_lid; lbtyp=t; lbdef=t1})]), body)
          | VBinder (x,t,_) ->
            let body = desugar_exp env t2 in
            let body = match pat with
              | None
              | Some ({v=Pat_wild _}) -> body
              | Some pat -> mk_Exp_match(bvd_to_exp x t, [(pat, None, body)]) None body.pos in
            pos <| mk_Exp_let((false, [mk_lb (Inl x, t, t1)]), body)
        end in

      if is_rec || is_app_pattern pat
      then ds_let_rec()
      else ds_non_rec pat _snd body

    | If(t1, t2, t3) ->
      pos <| mk_Exp_match(desugar_exp env t1,
                          [(withinfo (Pat_constant (Const_bool true)) (*Inr tun*) None t2.range, None, desugar_exp env t2);
                           (withinfo (Pat_constant (Const_bool false)) (*Inr tun*) None t3.range, None, desugar_exp env t3)])

    | TryWith(e, branches) ->
      let r = top.range in
      let handler = mk_function branches r r in
      let body = mk_function [(mk_pattern (PatConst Const_unit) r, None, e)] r r in
      let a1 = mk_term (App(mk_term (Var Const.try_with_lid) r top.level, body, Nothing)) r  top.level in
      let a2 = mk_term (App(a1, handler, Nothing)) r top.level in
      desugar_exp env a2

    | Match(e, branches) ->
      let desugar_branch (pat, wopt, b) =
        let env, pat = desugar_match_pat env pat in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (desugar_exp env e) in
        let b = desugar_exp env b in
        (pat, wopt, b) in
      pos <| mk_Exp_match(desugar_exp env e, List.map desugar_branch branches)

    | Ascribed(e, t) ->
      pos <| mk_Exp_ascribed(desugar_exp env e, desugar_typ env t, None)

    | Record(_, []) ->
      raise (Error("Unexpected empty record", top.range))

    | Record(eopt, fields) ->
      let f, _ = List.hd fields in
      let qfn g = lid_of_ids (f.ns@[g]) in
      let record, _ = fail_or env  (try_lookup_record_by_field_name env) f in
      let get_field xopt f =
        let fn = f.ident in
        let found = fields |> Util.find_opt (fun (g, _) ->
          let gn = g.ident in
          fn.idText = gn.idText) in
        match found with
          | Some (_, e) -> qfn fn, e
          | None ->
            match xopt with
              | None ->
                raise (Error (Util.format1 "Field %s is missing" (text_of_lid f), top.range))
              | Some x ->
                qfn fn, mk_term (Project(x, f)) x.range x.level in
      let recterm = match eopt with
        | None ->
          Construct(record.constrname,
                    record.fields |> List.map (fun (f, _) ->
                    snd <| get_field None f, Nothing))

        | Some e ->
          let x = genident (Some e.range) in
          let xterm = mk_term (Var (lid_of_ids [x])) x.idRange Expr in
          let record = Record(None, record.fields |> List.map (fun (f, _) -> get_field (Some xterm) f)) in
          Let(false, [(mk_pattern (PatVar (x, false)) x.idRange, e)], mk_term record top.range top.level) in

      let recterm = mk_term recterm top.range top.level in
      let e = desugar_exp env recterm in
      begin match e.n with
        | Exp_meta(Meta_desugared({n=Exp_app({n=Exp_fvar(fv, _)}, args)}, Data_app)) ->
          let e = pos <| mk_Exp_app(mk_Exp_fvar(fv, Some (Record_ctor(record.typename, record.fields |> List.map fst))) None e.pos,
                                    args)  in
          mk_Exp_meta(Meta_desugared(e, Data_app))

        | _ -> e
      end

    | Project(e, f) ->
      let _, fieldname = fail_or env  (try_lookup_record_by_field_name env) f in
      let e = desugar_exp env e in
      let fn =
        let ns, _ = Util.prefix fieldname.ns in
        lid_of_ids (ns@[f.ident]) in
      pos <| mk_Exp_app(Util.fvar (Some (Record_projector fn)) fieldname (range_of_lid f), [varg e])

    | Paren e ->
      desugar_exp env e

    | _ ->
      error "Unexpected term" top top.range
  end

and desugar_typ env (top:term) : typ =
  let wpos t = t None top.range in
  let setpos t = {t with pos=top.range} in
  let top = unparen top in
  let head_and_args t =
    let rec aux args t = match (unparen t).tm with
        | App(t, arg, imp) -> aux ((arg,imp)::args) t
        | Construct(l, args') -> {tm=Name l; range=t.range; level=t.level}, args'@args
        | _ -> t, args in
    aux [] t in
  match top.tm with
    | Wild -> setpos tun

    | Requires (t, lopt) ->
      let t = label_conjuncts "pre-condition" true lopt t in
      if is_type env t
      then desugar_typ env t
      else desugar_exp env t |> Util.b2t

    | Ensures (t, lopt) ->
      let t = label_conjuncts "post-condition" false lopt t in
      if is_type env t then desugar_typ env t
      else desugar_exp env t |> Util.b2t

    | Op("*", [t1; _]) ->
      if is_type env t1
      then let rec flatten t = match t.tm with
            | Op("*", [t1;t2]) ->
              let rest = flatten t2 in
              t1::rest
            | _ -> [t] in
          let targs = flatten top |> List.map (fun t -> targ (desugar_typ env t)) in
          let tup = fail_or env  (try_lookup_typ_name env) (Util.mk_tuple_lid (List.length targs) top.range) in
          wpos <| mk_Typ_app(tup, targs)
      else raise (Error(Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" (term_to_string t1), top.range))

    | Op("=!=", args) ->
      desugar_typ env (mk_term(Op("~", [mk_term (Op("==", args)) top.range top.level])) top.range top.level)

    | Op(s, args) ->
      begin match op_as_tylid env (List.length args) top.range s with
        | None -> desugar_exp env top |> Util.b2t
        | Some l ->
          let args = List.map (fun t -> arg_withimp_t Nothing <| desugar_typ_or_exp env t) args in
          mk_typ_app (ftv l kun) args
      end

    | Tvar a ->
      setpos <| fail_or2 (try_lookup_typ_var env) a

    | Var l
    | Name l when (List.length l.ns = 0) ->
      begin match try_lookup_typ_var env l.ident with
        | Some t -> setpos t
        | None -> setpos <| fail_or env  (try_lookup_typ_name env) l
      end

    | Var l
    | Name l ->
      let l = Util.set_lid_range l top.range in
      setpos <| fail_or env  (try_lookup_typ_name env) l

    | Construct(l, args) ->
      let t = setpos <| fail_or env  (try_lookup_typ_name env) l in
      let args = List.map (fun (t, imp) -> arg_withimp_t imp <| desugar_typ_or_exp env t) args in
      mk_typ_app t args

    | Abs(binders, body) ->
      let rec aux env bs = function
        | [] ->
          let body = desugar_typ env body in
          wpos <| mk_Typ_lam(List.rev bs, body)
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
          let arg = arg_withimp_t imp <| desugar_typ_or_exp env arg in
          aux (arg::args) e
        | _ ->
          let head = desugar_typ env e in
          wpos <| mk_Typ_app(head, args) in
      aux [] top

    | Product([], t) ->
      failwith "Impossible: product with no binders"

    | Product(binders, t) ->
      let bs, t = uncurry binders t in
      let rec aux env bs = function
        | [] ->
          let cod = desugar_comp top.range true env t in
          wpos <| mk_Typ_fun(List.rev bs, cod)
        | hd::tl ->
          let mlenv = default_ml env in
          let bb = desugar_binder mlenv hd in
          let b, env = as_binder env hd.aqual bb in
          aux env (b::bs) tl in
      aux env [] bs

    | Refine(b,f) ->
      begin match desugar_exp_binder env b with
        | (None, _) -> failwith "Missing binder in refinement"
        | b ->
          let b, env = match as_binder env None (Inr b) with
            | (Inr x, _), env -> x, env
            | _ -> failwith "impossible" in
          let f = if is_type env f then desugar_formula env f else desugar_exp env f |> Util.b2t in
          wpos <| mk_Typ_refine(b, f)
      end

    | NamedTyp(_, t)
    | Paren t ->
      desugar_typ env t

    | Ascribed(t,k) ->
      wpos <| mk_Typ_ascribed'(desugar_typ env t, desugar_kind env k)

    | Sum(binders, t) ->
      let env, _, targs = List.fold_left (fun (env, tparams, typs) b ->
        let xopt, t = desugar_exp_binder env b in
        let env, x = match xopt with
                    | None -> env, new_bvd (Some top.range)
                    | Some x -> push_local_vbinding env x in
        (env, tparams@[Inr (bvd_to_bvar_s x t), None], typs@[targ <| close_with_lam tparams t]))
        (env, [], []) (binders@[mk_binder (NoName t) t.range Type None]) in
      let tup = fail_or env  (try_lookup_typ_name env) (Util.mk_dtuple_lid (List.length targs) top.range) in
      wpos <| mk_Typ_app(tup, targs)

    | Record _ -> failwith "Unexpected record type"

    | If _
    | Labeled _ -> desugar_formula env top
    | _ when (top.level=Formula) -> desugar_formula env top

    | _ -> error "Expected a type" top top.range

and desugar_comp r default_ok env t =
    let fail msg = raise (Error(msg, r)) in
    let pre_process_comp_typ (t:AST.term) =
        let head, args = head_and_args t in
        match head.tm with
            | Name lemma when (lemma.ident.idText = "Lemma") ->
              let unit = mk_term (Name Const.unit_lid) t.range Type, Nothing in
              let nil_pat = mk_term (Name Const.nil_lid) t.range Expr, Nothing in
              let decreases_clause, args = args |> List.partition (fun (arg, _) ->
                  match (unparen arg).tm with
                    | App({tm=Var d}, _, _) -> d.ident.idText = "decreases"
                    | _ -> false) in
              let args = match args with
                    | [] -> raise (Error("Not enough arguments to 'Lemma'", t.range))
                    | [ens] -> (* a single ensures clause *)
                      let req_true = mk_term (Requires (mk_term (Name Const.true_lid) t.range Formula, None)) t.range Type, Nothing in
                      [unit;req_true;ens;nil_pat]
                    | [req;ens] -> [unit;req;ens;nil_pat]
                    | more -> unit::more in
              let t = mk_term (Construct(lemma, args@decreases_clause)) t.range t.level in
              desugar_typ env t

            | Name tot when (tot.ident.idText = "Tot"
                             && not (DesugarEnv.is_effect_name env Const.effect_Tot_lid)
                             && lid_equals (DesugarEnv.current_module env) Const.prims_lid) ->
              //we're right at the beginning of Prims, when Tot isn't yet fully defined
              let args = List.map (fun (t, imp) -> arg_withimp_t imp <| desugar_typ_or_exp env t) args in
              mk_typ_app (Util.ftv Const.effect_Tot_lid kun) args

            | _ -> desugar_typ env t
        in
    let t = pre_process_comp_typ t in
    let head, args = Util.head_and_args t in
    match (compress_typ head).n, args with
        | Typ_const eff, (Inl result_typ, _)::rest ->
          let dec, rest = rest |> List.partition (function
                | (Inr _, _) -> false
                | (Inl t, _) ->
                    begin match t.n with
                        | Typ_app({n=Typ_const fv}, [(Inr _,_)]) -> lid_equals fv.v Const.decreases_lid
                        | _ -> false
                    end) in

          let decreases_clause = dec |> List.map (function
                | (Inl t, _) ->
                    begin match t.n with
                        | Typ_app(_, [(Inr arg, _)]) -> DECREASES arg
                        | _ -> failwith "impos"
                    end
                | _ -> failwith "impos") in
          if DesugarEnv.is_effect_name env eff.v
          || lid_equals eff.v Const.effect_Tot_lid  //We need the Tot effect before its definition is in scope; it is primitive
          then if lid_equals eff.v Const.effect_Tot_lid && List.length decreases_clause=0
               then mk_Total result_typ
               else let flags =
                        if      lid_equals eff.v Const.effect_Lemma_lid then [LEMMA]
                        else if lid_equals eff.v Const.effect_Tot_lid   then [TOTAL]
                        else if lid_equals eff.v Const.effect_ML_lid    then [MLEFFECT]
                        else [] in
                    let rest = 
                        if lid_equals eff.v Const.effect_Lemma_lid
                        then match rest with 
                                | [req;ens;(Inr pat, aq)] -> [req;ens;(Inr (Syntax.mk_Exp_meta(Meta_desugared(pat, Syntax.Meta_smt_pat))), aq)]
                                | _ -> rest 
                        else rest in
                        mk_Comp ({effect_name=eff.v;
                                  result_typ=result_typ;
                                  effect_args=rest;
                                  flags=flags@decreases_clause})
           else if default_ok
           then env.default_result_effect t r
           else fail (Util.format1 "%s is not an effect" (Print.typ_to_string t))
       | _  ->
         if default_ok
         then env.default_result_effect t r
         else fail (Util.format1 "%s is not an effect" (Print.typ_to_string t))

and desugar_kind env k : knd =
  let pos f = f k.range in
  let setpos kk = {kk with pos=k.range} in
  let k = unparen k in
  match k.tm with
    | Name {str="Type"} -> setpos mk_Kind_type
    | Name {str="Effect"} -> setpos mk_Kind_effect
    | Name l ->
      begin match DesugarEnv.find_kind_abbrev env (DesugarEnv.qualify_lid env l) with
        | Some l -> pos <| mk_Kind_abbrev((l, []), mk_Kind_unknown)
        | _ -> error "Unexpected term where kind was expected" k k.range
       end
    | Wild           -> setpos kun
    | Product(bs, k) ->
      let bs, k = uncurry bs k in
      let rec aux env bs = function
        | [] ->
          pos <| mk_Kind_arrow(List.rev bs, desugar_kind env k)
        | hd::tl ->
          let b, env = desugar_binder (default_ml env) hd |> as_binder env hd.aqual in
          aux env (b::bs) tl in
      aux env [] bs

    | Construct(l, args) ->
      begin match DesugarEnv.find_kind_abbrev env l with
        | None -> error "Unexpected term where kind was expected" k k.range
        | Some l ->
          let args = List.map (fun (t, b) ->
            let qual = if b=Hash then Some Implicit else None in
            desugar_typ_or_exp env t, qual) args in
          pos <| mk_Kind_abbrev((l, args), mk_Kind_unknown)
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
  let pos t = t None f.range in
  let setpos t = {t with pos=f.range} in
  let desugar_quant (q:lident) (qt:lident) b pats body =
    let tk = desugar_binder env ({b with blevel=Formula}) in
    match tk with
      | Inl(Some a,k) ->
        let env, a = push_local_tbinding env a in
        let pats = List.map (fun e -> arg_withimp_t Nothing <| desugar_typ_or_exp env e) pats in
        let body = desugar_formula env body in
        let body = match pats with
          | [] -> body
          | _ -> setpos <| mk_Typ_meta (Meta_pattern(body, pats)) in
        let body = pos <| mk_Typ_lam([t_binder (bvd_to_bvar_s a k)], body) in
        setpos <| mk_typ_app (ftv (set_lid_range qt b.brange) kun) [targ body]

      | Inr(Some x,t) ->
        let env, x = push_local_vbinding env x in
        let pats = List.map (fun e -> arg_withimp_t Nothing <| desugar_typ_or_exp env e) pats in
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
      mk_Typ_meta(Meta_labeled(f, l, dummyRange, p))

    | Op("==", ((hd::_args))) ->
      let args = hd::_args in
      let args = List.map (fun t -> arg_withimp_t Nothing <| desugar_typ_or_exp env t) args in
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
        | _ -> if is_type env f then desugar_typ env f else desugar_exp env f |> Util.b2t
      end

    | If(f1, f2, f3) ->
      mk_typ_app
        (ftv (set_lid_range Const.ite_lid f.range) kun)
        (List.map (fun x ->
            match desugar_typ_or_exp env x with
                | Inl t -> targ t
                | Inr v -> targ <| (Util.b2t v)) //implicitly coerce a boolean to a type
         [f1;f2;f3])

    | QForall([], _, _)
    | QExists([], _, _) -> failwith "Impossible: Quantifier without binders"

    | QForall((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QForall x) binders pats body)

    | QExists((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QExists x) binders pats body)

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
                (env, (Inl (bvd_to_bvar_s a k), b.aqual)::out)
            | Inr(Some x,t) ->
                let env, x = push_local_vbinding env x in
                (env, (Inr (bvd_to_bvar_s x t), b.aqual)::out)
            | _ -> raise (Error ("Unexpected binder", b.brange))) (env, []) bs in
    env, List.rev tpars

and desugar_exp_binder env b = match b.b with
  | Annotated(x, t) -> Some x, desugar_typ env t
  | TVariable t -> None, fail_or2 (try_lookup_typ_var env) t
  | NoName t -> None, desugar_typ env t
  | Variable x -> Some x, tun
  | _ -> raise (Error("Unexpected domain of an arrow or sum (expected a type)", b.brange))

and desugar_type_binder env b =
 let fail () = raise (Error("Unexpected domain of an arrow or sum (expected a kind)", b.brange)) in
 match b.b with
  | Annotated(x, t)
  | TAnnotated(x, t) -> Some x, desugar_kind env t
  | NoName t -> None, desugar_kind env t
  | TVariable x -> Some x, {mk_Kind_type with pos=b.brange}
  | _ -> fail ()

let gather_tc_binders tps k =
    let rec aux bs k = match k.n with
        | Kind_arrow(binders, k) -> aux (bs@binders) k
        | Kind_abbrev(_, k) -> aux bs k
        | _ -> bs in
    aux tps k |> Util.name_binders


let mk_data_discriminators quals env t tps k datas =
//    if env.iface && not env.admitted_iface then [] else
    let quals q = if not <| env.iface || env.admitted_iface then Assumption::q@quals else q@quals in
    let binders = gather_tc_binders tps k in
    let p = range_of_lid t in
    let imp_binders = binders |> List.map (fun (x, _) -> x, Some Implicit) in
    let binders = imp_binders@[null_v_binder <| mk_Typ_app'(Util.ftv t kun, Util.args_of_non_null_binders binders) None p] in
    let disc_type = mk_Typ_fun(binders, Util.total_comp (Util.ftv Const.bool_lid ktype) p) None p in
    datas |> List.map (fun d ->
        let disc_name = Util.mk_discriminator d in
        //Util.fprint1 "Making discriminator %s\n" disc_name.str;
        Sig_val_decl(disc_name, disc_type, quals [Logic; Discriminator d], range_of_lid disc_name))

let mk_indexed_projectors fvq refine_domain env (tc, tps, k) lid (formals:list<binder>) t =
    let binders = gather_tc_binders tps k in
    let p = range_of_lid lid in
    let pos q = Syntax.withinfo q None p in
    let projectee = {ppname=Syntax.mk_ident ("projectee", p);
                     realname=Util.genident (Some p)} in
    let arg_exp = Util.bvd_to_exp projectee tun in
    let arg_binder =
        let arg_typ = mk_Typ_app'(Util.ftv tc kun, Util.args_of_non_null_binders binders) None p in
        if not refine_domain
        then v_binder (Util.bvd_to_bvar_s projectee arg_typ) //records have only one constructor; no point refining the domain
        else let disc_name = Util.mk_discriminator lid in
             let x = Util.gen_bvar arg_typ in
             v_binder <| (Util.bvd_to_bvar_s projectee <| mk_Typ_refine(x, Util.b2t(mk_Exp_app(Util.fvar None disc_name p, [varg <| Util.bvar_to_exp x]) None p)) None p) in
    let imp_binders = binders |> List.map (fun (x, _) -> x, Some Implicit) in
    let binders = imp_binders@[arg_binder] in
    let arg = Util.arg_of_non_null_binder arg_binder in
    let subst = formals |> List.mapi (fun i f -> match fst f with
        | Inl a ->
            let field_name, _ = Util.mk_field_projector_name lid a i in
            let proj = mk_Typ_app(Util.ftv field_name kun, [arg]) None p in
            [Inl (a.v, proj)]

        | Inr x ->
            let field_name, _ = Util.mk_field_projector_name lid x i in
            let proj = mk_Exp_app(Util.fvar None field_name p, [arg]) None p in //TODO: Mark the projector with an fv_qual?
            [Inr (x.v, proj)]) |> List.flatten in

    let ntps = List.length tps in
    let all_params = (tps |> List.map (fun (b, _) -> (b, Some Implicit)))@formals in
//    let pattern_fields = Util.nth_tail ntps formals in
    formals |> List.mapi (fun i ax -> match fst ax with
        | Inl a ->
            let field_name, _ = Util.mk_field_projector_name lid a i in
            let kk = mk_Kind_arrow(binders, Util.subst_kind subst a.sort) p in
            [Sig_tycon(field_name, [], kk, [], [], [Logic; Projector(lid, Inl a.v)], range_of_lid field_name)]

        | Inr x ->
            let field_name, _ = Util.mk_field_projector_name lid x i in
            let t = mk_Typ_fun(binders, Util.total_comp (Util.subst_typ subst x.sort) p) None p in
            let quals q = if not env.iface || env.admitted_iface then Assumption::q else q in
            let quals = quals [Logic; Projector(lid, Inr x.v)] in
            let impl =
                if lid_equals Const.prims_lid  (DesugarEnv.current_module env)
                || fvq<>Data_ctor
                || !Options.__temp_no_proj
                then []
                else let projection = Util.gen_bvar tun in
                     let as_imp = function
                        | Some Implicit -> true
                        | _ -> false in
                     let arg_pats = all_params |> List.mapi (fun j by -> match by with
                        | Inl _, imp ->
                          if j < ntps then [] else [pos (Pat_tvar (Util.gen_bvar kun)), as_imp imp]
                        | Inr _, imp ->
                            if i+ntps=j  //this is the one to project
                            then [pos (Pat_var projection), as_imp imp]
                            else [pos (Pat_wild (Util.gen_bvar tun)), as_imp imp]) |> List.flatten in
                     let pat = (Syntax.Pat_cons(Util.fv lid, Some fvq, arg_pats) |> pos, None, Util.bvar_to_exp projection) in
                     let body = mk_Exp_match(arg_exp, [pat]) None p in
                     let imp = mk_Exp_abs(binders, body) None (range_of_lid field_name) in
                     let lb = {
                        lbname=Inr field_name;
                        lbtyp=tun;
                        lbeff=Const.effect_Tot_lid;
                        lbdef=imp;
                     } in
                     [Sig_let((false, [lb]), p, [], quals)] in
            Sig_val_decl(field_name, t, quals, range_of_lid field_name)::impl) |> List.flatten

let mk_data_projectors env = function
  | Sig_datacon(lid, t, tycon, quals, _, _) when (//(not env.iface || env.admitted_iface) &&
                                                not (lid_equals lid Const.lexcons_lid)) ->
    let refine_domain =
        if (quals |> Util.for_some (function RecordConstructor _ -> true | _ -> false))
        then false
        else let l, _, _ = tycon in
             match DesugarEnv.find_all_datacons env l with
                | Some l -> List.length l > 1
                | _ -> true in
        begin match Util.function_formals t with
        | Some(formals, cod) -> //close_typ (List.map (fun (x, _) -> (x, Some Implicit)) tps) t 
          let cod = Util.comp_result cod in
          let qual = match Util.find_map quals (function RecordConstructor fns -> Some (Record_ctor(lid, fns)) | _ -> None) with
            | None -> Data_ctor
            | Some q -> q in
          mk_indexed_projectors qual refine_domain env tycon lid formals cod

        | _ -> [] //no fields to project
    end

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
  let tot = mk_term (Name (Const.effect_Tot_lid)) rng Expr in
  let with_constructor_effect t = mk_term (App(tot, t, Nothing)) t.range t.level in
  let apply_binders t binders =
    let imp_of_aqual (b:AST.binder) = match b.aqual with 
        | Some Implicit -> Hash
        | _ -> Nothing in
    List.fold_left (fun out b -> mk_term (App(out, binder_to_term b, imp_of_aqual b)) out.range out.level)
      t binders in
  let tycon_record_as_variant = function
    | TyconRecord(id, parms, kopt, fields) ->
      let constrName = mk_ident("Mk" ^ id.idText, id.idRange) in
      let mfields = List.map (fun (x,t) -> mk_binder (Annotated(mangle_field_name x,t)) x.idRange Expr None) fields in
      let result = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type) parms in
      let constrTyp = mk_term (Product(mfields, with_constructor_effect result)) id.idRange Type in
      //let _ = Util.print_string (Util.format2 "Translated record %s to constructor %s\n" (id.idText) (term_to_string constrTyp)) in
      TyconVariant(id, parms, kopt, [(constrName, Some constrTyp, false)]), fields |> List.map (fun (x, _) -> DesugarEnv.qualify env x)
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
      _env, _env2, se, tconstr
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
        let t0 = t in
        let quals = if quals |> Util.for_some (function Logic -> true | _ -> false)
                    then quals
                    else if t0.level = Formula
                    then Logic::quals
                    else quals in
        let se =
            if quals |> List.contains Effect
            then let c = desugar_comp t.range false env' t in
                 Sig_effect_abbrev(qualify env id, typars, c, quals |> List.filter (function Effect -> false | _ -> true), rng)
            else let t = desugar_typ env' t in
                 Sig_typ_abbrev(qualify env id, typars, k, t, quals, rng) in
        let env = push_sigelt env se in
        env, [se]

    | [TyconRecord _] ->
      let trec = List.hd tcs in
      let t, fs = tycon_record_as_variant trec in
      desugar_tycon env rng (RecordType fs::quals) [t]

    |  _::_ ->
      let env0 = env in
      let mutuals = List.map (fun x -> qualify env <| tycon_id x) tcs in
      let rec collect_tcs quals et tc =
        let (env, tcs) = et in
        match tc with
          | TyconRecord _ ->
            let trec = tc in
            let t, fs = tycon_record_as_variant trec in
            collect_tcs (RecordType fs::quals) (env, tcs) t
          | TyconVariant(id, binders, kopt, constructors) ->
            let env, _, se, tconstr = desugar_abstract_tc quals env mutuals (TyconAbstract(id, binders, kopt)) in
            env, Inl(se, constructors, tconstr, quals)::tcs
          | TyconAbbrev(id, binders, kopt, t) ->
            let env, _, se, tconstr = desugar_abstract_tc quals env mutuals (TyconAbstract(id, binders, kopt)) in
            env, Inr(se, t, quals)::tcs
          | _ -> failwith "Unrecognized mutual type definition" in
      let env, tcs = List.fold_left (collect_tcs quals) (env, []) tcs in
      let tcs = List.rev tcs in
      let sigelts = tcs |> List.collect (function
        | Inr(Sig_tycon(id, tpars, k, _, _, _, _), t, quals) ->
          let env_tps = push_tparams env tpars in
          let t = desugar_typ env_tps t in
          [Sig_typ_abbrev(id, tpars, k, t, [], rng)]

        | Inl (Sig_tycon(tname, tpars, k, mutuals, _, tags, _), constrs, tconstr, quals) ->
          let tycon = (tname, tpars, k) in
          let env_tps = push_tparams env tpars in
          let constrNames, constrs = List.split <|
              (constrs |> List.map (fun (id, topt, of_notation) ->
                let t =
                  if of_notation
                  then match topt with
                    | Some t -> mk_term (Product([mk_binder (NoName t) t.range t.level None], tconstr)) t.range t.level
                    | None -> tconstr
                  else match topt with
                    | None -> failwith "Impossible"
                    | Some t -> t in
                let t = desugar_typ (default_total env_tps) (close env_tps t) in
                let name = qualify env id in
                let quals = tags |> List.collect (function
                    | RecordType fns -> [RecordConstructor fns]
                    | _ -> []) in
                (name, Sig_datacon(name, t |> Util.name_function_binders, tycon, quals, mutuals, rng)))) in
              Sig_tycon(tname, tpars, k, mutuals, constrNames, tags, rng)::constrs
        | _ -> failwith "impossible") in
      let bundle = Sig_bundle(sigelts, quals, List.collect Util.lids_of_sigelt sigelts, rng) in
      let env = push_sigelt env0 bundle in
      let data_ops = sigelts |> List.collect (mk_data_projectors env) in
      let discs = sigelts |> List.collect (function
        | Sig_tycon(tname, tps, k, _, constrs, quals, _) ->
          mk_data_discriminators quals env tname tps k constrs
        | _ -> []) in
      let ops = discs@data_ops in
      let env = List.fold_left push_sigelt env ops in
      env, [bundle]@ops

    | [] -> failwith "impossible"

let desugar_binders env binders =
    let env, binders = List.fold_left (fun (env,binders) b ->
    match desugar_binder env b with
      | Inl(Some a, k) ->
        let env, a = push_local_tbinding env a in
        env, t_binder (bvd_to_bvar_s a k)::binders

      | Inr(Some x,t) ->
        let env, x = push_local_vbinding env x in
        env, v_binder (bvd_to_bvar_s x t)::binders

      | _ -> raise (Error("Missing name in binder", b.brange))) (env, []) binders in
    env, List.rev binders

let rec desugar_decl env (d:decl) : (env_t * sigelts) = match d.d with
  | Pragma p ->
    let se = Sig_pragma(p, d.drange) in
    env, [se]

  | Open lid ->
    let env = DesugarEnv.push_namespace env lid in
    env, []

  | Tycon(qual, tcs) ->
    desugar_tycon env d.drange qual tcs

  | ToplevelLet(isrec, lets) ->
    begin match (compress_exp <| desugar_exp_maybe_top true env (mk_term (Let(isrec, lets, mk_term (Const Const_unit) d.drange Expr)) d.drange Expr)).n with
        | Exp_let(lbs, _) ->
          let lids = snd lbs |> List.map (fun lb -> match lb.lbname with
            | Inr l -> l
            | _ -> failwith "impossible") in
          let quals = snd lbs |> List.collect
            (function | {lbname=Inl _} -> []
                      | {lbname=Inr l} -> DesugarEnv.lookup_letbinding_quals env l) in
          let s = Sig_let(lbs, d.drange, lids, quals) in
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
    env, [Sig_assume(qualify env id, f, [Assumption], d.drange)]

  | Val(quals, id, t) ->
    let t = desugar_typ env (close_fun env t) in
    let quals = if env.iface && env.admitted_iface then Assumption::quals else quals in
    let se = Sig_val_decl(qualify env id, t, quals, d.drange) in
    let env = push_sigelt env se in
    env, [se]

  | Exception(id, None) ->
    let t = fail_or env  (try_lookup_typ_name env) Const.exn_lid in
    let l = qualify env id in
    let se = Sig_datacon(l, t, (Const.exn_lid,[],ktype), [ExceptionConstructor], [Const.exn_lid], d.drange) in
    let se' = Sig_bundle([se], [ExceptionConstructor], [l], d.drange) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_projectors env se in
    let discs = mk_data_discriminators [] env Const.exn_lid [] ktype [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | Exception(id, Some term) ->
    let t = desugar_typ env term in
    let t = mk_Typ_fun([null_v_binder t], mk_Total (fail_or env (try_lookup_typ_name env) Const.exn_lid)) None d.drange in
    let l = qualify env id in
    let se = Sig_datacon(l, t, (Const.exn_lid,[],ktype), [ExceptionConstructor], [Const.exn_lid], d.drange) in
    let se' = Sig_bundle([se], [ExceptionConstructor], [l], d.drange) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_projectors env se in
    let discs = mk_data_discriminators [] env Const.exn_lid [] ktype [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | KindAbbrev(id, binders, k) ->
    let env_k, binders = desugar_binders env binders in
    let k = desugar_kind env_k k in
    let name = DesugarEnv.qualify env id in
    let se = Sig_kind_abbrev(name, binders, k, d.drange) in
    let env = push_sigelt env se in
    env, [se]

  | NewEffect (quals, RedefineEffect(eff_name, eff_binders, defn)) ->
    let env0 = env in
    let env, binders = desugar_binders env eff_binders in
    let defn = desugar_typ env defn in
    let head, args = Util.head_and_args defn in
    begin match head.n with
        | Typ_const eff ->
          begin match DesugarEnv.try_lookup_effect_defn env eff.v with
            | None -> raise (Error("Effect " ^Print.sli eff.v^ " not found", d.drange))
            | Some ed ->
              let subst = Util.subst_of_list ed.binders args in
              let sub = Util.subst_typ subst in
              let ed = {
                     mname=qualify env0 eff_name;
                     qualifiers=quals;
                     binders=binders;
                     signature=Util.subst_kind subst ed.signature;
                     ret=sub ed.ret;
                     bind_wp=sub ed.bind_wp;
                     bind_wlp=sub ed.bind_wlp;
                     if_then_else=sub ed.if_then_else;
                     ite_wp=sub ed.ite_wp;
                     ite_wlp=sub ed.ite_wlp;
                     wp_binop=sub ed.wp_binop;
                     wp_as_type=sub ed.wp_as_type;
                     close_wp=sub ed.close_wp;
                     close_wp_t=sub ed.close_wp_t;
                     assert_p=sub ed.assert_p;
                     assume_p=sub ed.assume_p;
                     null_wp=sub ed.null_wp;
                     trivial=sub ed.trivial
              } in
            let se = Sig_new_effect(ed, d.drange) in
            let env = push_sigelt env0 se in
            env, [se]
        end
    | _ -> raise (Error((Print.typ_to_string head) ^ " is not an effect", d.drange))
    end

  | NewEffect (quals, DefineEffect(eff_name, eff_binders, eff_kind, eff_decls)) ->
    let env0 = env in
    let env = DesugarEnv.enter_monad_scope env eff_name in
    let env, binders = desugar_binders env eff_binders in
    let eff_k = desugar_kind env eff_kind in
    let env, decls = eff_decls |> List.fold_left (fun (env, out) decl ->
        let env, ses = desugar_decl env decl in
        env, List.hd ses::out) (env, []) in
    let decls = List.rev decls in
    let lookup s = match DesugarEnv.try_resolve_typ_abbrev env (DesugarEnv.qualify env (Syntax.mk_ident(s, d.drange))) with
        | None -> raise (Error("Monad " ^eff_name.idText^ " expects definition of "^s, d.drange))
        | Some t -> t in
    let ed = {
         mname=qualify env0 eff_name;
         qualifiers=quals;
         binders=binders;
         signature=eff_k;
         ret=lookup "return";
         bind_wp=lookup "bind_wp";
         bind_wlp=lookup "bind_wlp";
         if_then_else=lookup "if_then_else";
         ite_wp=lookup "ite_wp";
         ite_wlp=lookup "ite_wlp";
         wp_binop=lookup "wp_binop";
         wp_as_type=lookup "wp_as_type";
         close_wp=lookup "close_wp";
         close_wp_t=lookup "close_wp_t";
         assert_p=lookup "assert_p";
         assume_p=lookup "assume_p";
         null_wp=lookup "null_wp";
         trivial=lookup "trivial"
    } in
    let se = Sig_new_effect(ed, d.drange) in
    let env = push_sigelt env0 se in
    env, [se]

  | SubEffect l ->
    let lookup l = match DesugarEnv.try_lookup_effect_name env l with
        | None -> raise (Error("Effect name " ^Print.sli l^ " not found", d.drange))
        | Some l -> l in
    let src = lookup l.msource in
    let dst = lookup l.mdest in
    let lift = desugar_typ env l.lift_op in
    let se = Sig_sub_effect({source=src; target=dst; lift=lift}, d.drange) in
    env, [se]

 let desugar_decls env decls =
    List.fold_left (fun (env, sigelts) d ->
        let env, se = desugar_decl env d in
        env, sigelts@se) (env, []) decls

let open_prims_all =
    [AST.mk_decl (AST.Open Const.prims_lid) dummyRange;
     AST.mk_decl (AST.Open Const.all_lid) dummyRange]

(* Most important function: from AST to a module
   Keeps track of the name of variables and so on (in the context)
 *)
let desugar_modul_common curmod env (m:AST.modul) : env_t * Syntax.modul =
  let open_ns (mname:lident) d =
    let d = if List.length mname.ns <> 0
            then (AST.mk_decl (AST.Open (Syntax.lid_of_ids mname.ns)) (Syntax.range_of_lid mname))  :: d
            else d in
    d in
  let env = match curmod with
    | None -> env
    | Some(prev_mod, _) ->  DesugarEnv.finish_module_or_interface env prev_mod in
  let env, mname, decls, intf = match m with
    | Interface(mname, decls, admitted) ->
      DesugarEnv.prepare_module_or_interface true admitted env mname, mname, open_ns mname decls, true
    | Module(mname, decls) ->
      DesugarEnv.prepare_module_or_interface false false env mname, mname, open_ns mname decls, false in
  let env, sigelts = desugar_decls env decls in
  let modul = {
    name = mname;
    declarations = sigelts;
    exports = [];
    is_interface=intf;
    is_deserialized=false
  } in
  env, modul

let desugar_partial_modul curmod env (m:AST.modul) : env_t * Syntax.modul =
  let m =
    if !Options.interactive_fsi then
        match m with
            | Module(mname, decls) -> AST.Interface(mname, decls, Util.for_some (fun m -> m=mname.str) !Options.admit_fsi)
            | Interface(mname, _, _) -> failwith ("Impossible: " ^ mname.ident.idText)
    else m
  in
  desugar_modul_common curmod env m

let desugar_modul env (m:AST.modul) : env_t * Syntax.modul =
  let env, modul = desugar_modul_common None env m in
  let env = DesugarEnv.finish_module_or_interface env modul in
  if Options.should_dump modul.name.str then Util.fprint1 "%s\n" (Print.modul_to_string modul);
  env, modul

let desugar_file env (f:file) =
  let env, mods = List.fold_left (fun (env, mods) m ->
    let env, m = desugar_modul env m in
    env, m::mods) (env, []) f in
  env, List.rev mods

let add_modul_to_env (m:Syntax.modul) (en: env) :env =
  let en = DesugarEnv.prepare_module_or_interface false false en m.name in
  let en = List.fold_left DesugarEnv.push_sigelt ({ en with curmodule = Some(m.name) }) m.exports in
  DesugarEnv.finish_module_or_interface en m
