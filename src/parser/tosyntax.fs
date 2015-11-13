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
module FStar.Parser.ToSyntax

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Parser
open FStar.Parser.Env
open FStar.Parser.AST
open FStar.Ident
open FStar.Const

module C = FStar.Syntax.Const
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util

let trans_aqual = function
  | Some AST.Implicit -> Some S.Implicit
  | Some AST.Equality -> Some S.Equality
  | _ -> None

let trans_qual = function
  | AST.Private ->       S.Private
  | AST.Assumption ->    S.Assumption
  | AST.Opaque ->        S.Opaque
  | AST.Logic ->         S.Logic
  | AST.TotalEffect ->   S.TotalEffect
  | AST.DefaultEffect -> S.DefaultEffect None
  | AST.Effect ->        S.Effect

let trans_pragma = function
  | AST.SetOptions s -> S.SetOptions s
  | AST.ResetOptions -> S.ResetOptions

let as_imp = function
    | Hash
    | FsTypApp -> Some S.Implicit
    | _ -> None
let arg_withimp_e imp t =
    t, as_imp imp
let arg_withimp_t imp t =
    match imp with
        | Hash -> t, Some S.Implicit
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

let tm_type r = mk_term (Name (lid_of_path ["Type"] r)) r Kind

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

let compile_op_lid n s r = [mk_ident(compile_op n s, r)] |> lid_of_ids

let op_as_lid env arity rng s =
  let r l = Some (set_lid_range l rng) in
  let fallback () =
      match s with
        | "=" ->    r C.op_Eq
        | ":=" ->   r C.op_ColonEq
        | "<" ->    r C.op_LT
        | "<=" ->   r C.op_LTE
        | ">" ->    r C.op_GT
        | ">=" ->   r C.op_GTE
        | "&&" ->   r C.op_And
        | "||" ->   r C.op_Or
        | "*" ->    r C.op_Multiply
        | "+" ->    r C.op_Addition
        | "-" when (arity=1) -> r C.op_Minus
        | "-" ->    r C.op_Subtraction
        | "/" ->    r C.op_Division
        | "%" ->    r C.op_Modulus
        | "!" ->    r C.read_lid
        | "@" ->    r C.list_append_lid
        | "^" ->    r C.strcat_lid
        | "|>" ->   r C.pipe_right_lid
        | "<|" ->   r C.pipe_left_lid
        | "<>" ->   r C.op_notEq
        | "~"   ->  r C.not_lid
        | "=="  ->  r C.eq2_lid
        | "=!=" ->  r C.neq2_lid
        | "<<" ->   r C.precedes_lid
        | "/\\" ->  r C.and_lid
        | "\\/" ->  r C.or_lid
        | "==>" ->  r C.imp_lid
        | "<==>" -> r C.iff_lid
        | _ -> None in
   begin match Env.try_lookup_lid env (compile_op_lid arity s rng) with
        | Some ({n=Tm_fvar(fv, _)}) -> Some fv.v
        | _ -> fallback()
   end

//let rec is_type_binder env b =
//  if b.blevel = Formula
//  then match b.b with
//    | Variable _ -> false
//    | TAnnotated _
//    | TVariable _ -> true
//    | Annotated(_, t)
//    | NoName t -> is_kind env t
//  else match b.b with
//    | Variable _ -> raise (Error("Unexpected binder without annotation", b.brange))
//    | TVariable _ -> false
//    | TAnnotated _ -> true
//    | Annotated (_, t)
//    | NoName t -> is_kind env t

let sort_ftv ftv =
  Util.sort_with (fun x y -> String.compare x.idText y.idText) <|
      Util.remove_dups (fun x y -> x.idText = y.idText) ftv

let rec free_type_vars_b env binder = match binder.b with
  | Variable _ -> env, []
  | TVariable x ->
    let env, _ = Env.push_bv env x in
    (env, [x])
  | Annotated(_, term) ->
    (env, free_type_vars env term)
  | TAnnotated(id, _) ->
    let env, _ = Env.push_bv env id in
    (env, [])
  | NoName t ->
    (env, free_type_vars env t)
and free_type_vars env t = match (unparen t).tm with
  | Tvar a ->
    (match Env.try_lookup_id env a with
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
  | Let _
  | If _
  | QForall _
  | QExists _ -> [] (* not closing implicitly over free vars in formulas *)
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
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, tm_type x.idRange)) x.idRange Type (Some Implicit)) in
       let result = mk_term (Product(binders, t)) t.range t.level in
       result

let close_fun env t =
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, tm_type x.idRange)) x.idRange Type (Some Implicit)) in
       let t = match (unlabel t).tm with
        | Product _ -> t
        | _ -> mk_term (App(mk_term (Name C.effect_Tot_lid) t.range t.level, t, Nothing)) t.range t.level in
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
  | LocalBinder of bv     * S.aqual
  | LetBinder   of lident * S.term
let binder_of_bnd = function
  | LocalBinder (a, aq) -> a, aq
  | _ -> failwith "Impossible"
let as_binder env imp = function
  | (None, k) -> null_binder k, env
  | (Some a, k) ->
    let env, a = Env.push_bv env a in
    ({a with sort=k}, trans_aqual imp), env

type env_t = Env.env
type lenv_t = list<bv>

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

let mk_lb (n, t, e) = {lbname=n; lbunivs=[]; lbeff=C.effect_ALL_lid; lbtyp=t; lbdef=e}

let rec desugar_data_pat env (p:pattern) : (env_t * bnd * Syntax.pat) =
  let resolvex (l:lenv_t) e x =
    match l |> Util.find_opt (fun y -> y.ppname.idText=x.idText) with
      | Some y -> l, e, y
      | _ ->
        let e, x = push_bv e x in
        (x::l), e, x in
  let resolvea (l:lenv_t) e a =
    match l |> Util.find_opt (fun b -> b.ppname.idText=a.idText) with
      | Some b -> l, e, b
      | _ ->
        let e, a = push_bv e a in
        (a::l), e, a in
  let rec aux (loc:lenv_t) env (p:pattern) =
    let pos q = Syntax.withinfo q tun.n p.prange in
    let pos_r r q = Syntax.withinfo q tun.n r in
    match p.pat with
      | PatOr [] -> failwith "impossible"
      | PatOr (p::ps) ->
        let loc, env, var, p, _ = aux loc env p in
        let loc, env, ps = List.fold_left (fun (loc, env, ps) p ->
          let loc, env, _, p, _ = aux loc env p in
          loc, env, p::ps) (loc, env, []) ps in
        let pat = pos <| Pat_disj (p::List.rev ps) in
        ignore (S.pat_bvs pat); //checks that the pattern variables are linear and that the disjunction binds the same variables
        loc, env, var, pat, false

      | PatAscribed(p, t) ->
        let loc, env', binder, p, imp = aux loc env p in
        let binder = match binder with
            | LetBinder _ -> failwith "impossible"
            | LocalBinder(x, aq) -> 
              let t = desugar_term env (close_fun env t) in
              LocalBinder({x with sort=t}, aq) in
        loc, env', binder, p, imp

      | PatWild ->
        let x = S.new_bv (Some p.prange) tun in
        let y = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_wild x, false

      | PatConst c ->
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_constant c, false

      | PatVar (x, imp) ->
        let aq = if imp then Some S.Implicit else None in
        let loc, env, xbv = resolvex loc env x in
        loc, env, LocalBinder(xbv, aq), pos <| Pat_var xbv, imp

      | PatName l ->
        let l = fail_or (try_lookup_datacon env) l in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x,  None), pos <| Pat_cons(l, []), false

      | PatApp({pat=PatName l}, args) ->
        let loc, env, args = List.fold_right (fun arg (loc,env,args) ->
          let loc, env, _, arg, imp = aux loc env arg in
          (loc, env, (arg, imp)::args)) args (loc, env, []) in
        let l = fail_or  (try_lookup_datacon env) l in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_cons(l, args), false

      | PatApp _ -> raise (Error ("Unexpected pattern", p.prange))

      | PatList pats ->
        let loc, env, pats = List.fold_right (fun pat (loc, env, pats) ->
          let loc,env,_,pat, _ = aux loc env pat in
          loc, env, pat::pats) pats (loc, env, []) in
        let pat = List.fold_right (fun hd tl ->
            let r = Range.union_ranges hd.p tl.p in
            pos_r r <| Pat_cons(S.fv C.cons_lid (Some Data_ctor), [(hd, false);(tl, false)])) pats
                        (pos_r (Range.end_range p.prange) <| Pat_cons(S.fv C.nil_lid (Some Data_ctor), [])) in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pat, false

      | PatTuple(args, dep) ->
        let loc, env, args = List.fold_left (fun (loc, env, pats) p ->
          let loc, env, _, pat, _ = aux loc env p in
          loc, env, (pat, false)::pats) (loc,env,[]) args in
        let args = List.rev args in
        let l = if dep then Util.mk_dtuple_data_lid (List.length args) p.prange
                else Util.mk_tuple_data_lid (List.length args) p.prange in
        let constr = fail_or  (Env.try_lookup_lid env) l in
        let l = match constr.n with
          | Tm_fvar fv -> fv
          | _ -> failwith "impossible" in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_cons(l, args), false

      | PatRecord ([]) ->
        raise (Error ("Unexpected pattern", p.prange))

      | PatRecord (fields) ->
        let (f, _) = List.hd fields in
        let record, _ = fail_or (try_lookup_record_by_field_name env) f in
        let fields = fields |> List.map (fun (f, p) ->
          (fail_or (qualify_field_to_record env record) f, p)) in
        let args = record.fields |> List.map (fun (f, _) ->
          match fields |> List.tryFind (fun (g, _) -> lid_equals f g) with
            | None -> mk_pattern PatWild p.prange
            | Some (_, p) -> p) in
        let app = mk_pattern (PatApp(mk_pattern (PatName record.constrname) p.prange, args)) p.prange in
        let env, e, b, p, _ = aux loc env app in
        let p = match p.v with
            | Pat_cons((fv, _), args) -> pos <| Pat_cons((fv, Some (Record_ctor (record.typename, record.fields |> List.map fst))), args)
            | _ -> p in
        env, e, b, p, false in

  let _, env, b, p, _ = aux [] env p in
  env, b, p

and desugar_binding_pat_maybe_top top env p : (env_t * bnd * option<pat>) =
  if top
  then match p.pat with
    | PatVar (x, _) -> (env, LetBinder(qualify env x, tun), None)
    | PatAscribed({pat=PatVar (x, _)}, t) ->
      (env, LetBinder(qualify env x, desugar_term env t), None)
    | _ -> raise (Error("Unexpected pattern at the top-level", p.prange))
  else
    let (env, binder, p) = desugar_data_pat env p in
    let p = match p.v with
      | Pat_var _
      | Pat_wild _ -> None
      | _ -> Some p in
    (env, binder, p)

and desugar_binding_pat env p = desugar_binding_pat_maybe_top false env p

and desugar_match_pat_maybe_top _ env pat =
  let (env, _, pat) = desugar_data_pat env pat in
  (env, pat)

and desugar_match_pat env p = desugar_match_pat_maybe_top false env p

and desugar_term env e : S.term = desugar_exp_maybe_top false env e

and desugar_exp_maybe_top (top_level:bool) (env:env_t) (top:term) : S.term =
  let mk e = S.mk e None top.range in
  let setpos e = {e with pos=top.range} in
  begin match (unparen top).tm with
    | Wild -> setpos tun
   
    | Labeled _ -> desugar_formula env top
   
    | Requires (t, lopt) ->
      let t = label_conjuncts "pre-condition" true lopt t in
      desugar_formula env t

    | Ensures (t, lopt) ->
      let t = label_conjuncts "post-condition" false lopt t in
      desugar_formula env t

    | Const c -> mk (Tm_constant c)

    | Op("=!=", args) ->
      desugar_term env (mk_term(Op("~", [mk_term (Op("==", args)) top.range top.level])) top.range top.level)

    | Tvar a ->
      setpos <| fail_or2 (try_lookup_id env) a

    | Op(s, args) ->
      begin match op_as_lid env (List.length args) top.range s with
        | None -> raise (Error("Unexpected operator: " ^ s, top.range))
        | Some l ->
          let op = fvar None l (range_of_lid l) in
          let args = args |> List.map (fun t -> desugar_term env t, None) in
          mk (Tm_app(op, args))
      end

    | Name {str="Type"}   -> mk (Tm_type U_unknown)
    | Name {str="Effect"} -> mk (Tm_constant Const_effect)
   
    | Var l
    | Name l ->
      if l.str = "ref"
      then begin match Env.try_lookup_lid env C.alloc_lid with
            | None -> raise (Error ("Identifier 'ref' not found; include lib/st.fst in your path", range_of_lid l))
            | Some e -> setpos e
           end
      else setpos <| fail_or (Env.try_lookup_lid env) l

    | Construct(l, args) ->
      let head = mk (Tm_fvar(fail_or (Env.try_lookup_datacon env) l))  in 
      begin match args with
        | [] -> head
        | _ ->
          let args = List.map (fun (t, imp) ->
            let te = desugar_term env t in
            arg_withimp_e imp te) args in
          let app = mk (Tm_app(head, args)) in
          mk (Tm_meta(app, Meta_desugared Data_app))
      end

    | Sum(binders, t) ->
      let env, _, targs = List.fold_left (fun (env, tparams, typs) b ->
                let xopt, t = desugar_binder env b in
                let env, x = 
                    match xopt with
                    | None -> env, S.new_bv (Some top.range) tun
                    | Some x -> push_bv env x in
                (env, tparams@[{x with sort=t}, None], typs@[arg <| U.abs tparams t]))
        (env, [], []) 
        (binders@[mk_binder (NoName t) t.range Type None]) in
      let tup = fail_or  (try_lookup_lid env) (Util.mk_dtuple_lid (List.length targs) top.range) in
      mk <| Tm_app(tup, targs)

    | Product(binders, t) ->
      let bs, t = uncurry binders t in
      let rec aux env bs = function
        | [] ->
          let cod = desugar_comp top.range true env t in
          setpos <| U.arrow (List.rev bs) cod
      
        | hd::tl ->
          let mlenv = default_ml env in
          let bb = desugar_binder mlenv hd in
          let b, env = as_binder env hd.aqual bb in
          aux env (b::bs) tl in
      aux env [] bs

    | Refine(b, f) ->
      begin match desugar_binder env b with
        | (None, _) -> failwith "Missing binder in refinement"
  
        | b ->
          let (x, _), env = as_binder env None b in
          let f = desugar_formula env f in
          setpos <| U.refine x f
      end

    | Abs(binders, body) ->
      let _, ftv = List.fold_left (fun (env, ftvs) pat ->
        match pat.pat with
          | PatAscribed(_, t) -> env, free_type_vars env t@ftvs
          | _ -> env, ftvs) (env, []) binders in
      let ftv = sort_ftv ftv in
      let binders = (ftv |> List.map (fun a -> mk_pattern (PatTvar(a, true)) top.range))@binders in //close over the free type variables
      (*
         fun (P1 x1) (P2 x2) (P3 x3) -> e
           
            is desugared to 

         fun y1 y2 y3 -> match (y1, y2, y3) with 
                | (P1 x1, P2 x2, P3 x3) -> [[e]]
      *)
      let rec aux env bs sc_pat_opt = function
            | [] ->
              let body = desugar_term env body in
              let body = match sc_pat_opt with
                | Some (sc, pat) -> 
                  let body = Subst.close (S.pat_bvs pat |> List.map S.mk_binder) body in
                  S.mk (Tm_match(sc, [(pat, None, body)])) None body.pos
                | None -> body in
              setpos (U.abs (List.rev bs) body)

            | p::rest ->
              let env, b, pat = desugar_binding_pat env p in
              let b, sc_pat_opt = match b with
                | LetBinder _ -> failwith "Impossible"
                | LocalBinder (x, aq) ->
                    let sc_pat_opt = match pat, sc_pat_opt with
                        | None, _ -> sc_pat_opt
                        | Some p, None -> Some (S.bv_to_name x, p)
                        | Some p, Some (sc, p') ->
                             begin match sc.n, p'.v with
                                | Tm_name _, _ ->
                                  let tup2 = S.fv (Util.mk_tuple_data_lid 2 top.range) (Some Data_ctor) in
                                  let sc = S.mk (Tm_app(mk (Tm_fvar tup2), [arg sc; arg <| S.bv_to_name x])) None top.range in
                                  let p = withinfo (Pat_cons(tup2, [(p', false);(p, false)])) tun.n (Range.union_ranges p'.p p.p) in
                                  Some(sc, p)
                                | Tm_app(_, args), Pat_cons(_, pats) ->
                                  let tupn = S.fv (Util.mk_tuple_data_lid (1 + List.length args) top.range) (Some Data_ctor) in
                                  let sc = mk (Tm_app(mk (Tm_fvar tupn), args@[arg <| S.bv_to_name x])) in
                                  let p = withinfo (Pat_cons(tupn, pats@[(p, false)])) tun.n (Range.union_ranges p'.p p.p) in
                                  Some(sc, p)
                                | _ -> failwith "Impossible"
                              end in
                    (x, aq), sc_pat_opt in
                aux env (b::bs) sc_pat_opt rest
       in
       aux env [] None binders

    | App({tm=Var a}, phi, _) when (lid_equals a C.assert_lid
                                   || lid_equals a C.assume_lid) ->
      let phi = desugar_formula env phi in
      mk (Tm_app(fvar None a (range_of_lid a),
                 [arg phi;
                  arg <| mk (Tm_constant(Const_unit))]))

    | App _ ->
      let rec aux args e = match (unparen e).tm with
        | App(e, t, imp) ->
          let arg = arg_withimp_e imp <| desugar_term env t in
          aux (arg::args) e
        | _ ->
          let head = desugar_term env e in
          mk (Tm_app(head, args)) in
      aux [] top

    | Seq(t1, t2) ->
      mk (Tm_meta(desugar_term env (mk_term (Let(false, [(mk_pattern PatWild t1.range,t1)], t2)) top.range Expr), 
                  Meta_desugared Sequence))

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

        let env', fnames, rec_bindings =
          List.fold_left (fun (env, fnames, rec_bindings) ((f, _, _), _) ->
            let env, lbname, rec_bindings = match f with
              | Inl x ->
                let env, xx = push_bv env x in
                env, Inl xx, S.mk_binder xx::rec_bindings 
              | Inr l ->
                push_top_level_rec_binding env l.ident, Inr l, rec_bindings in
            env, (lbname::fnames), rec_bindings) (env, [], []) funs in

        let fnames = List.rev fnames in

        let desugar_one_def env lbname ((_, args, result_t), def) =
            let def = match result_t with
                | None -> def
                | Some t -> mk_term (Ascribed(def, t)) (Range.union_ranges t.range def.range) Expr in
            let def = match args with
                | [] -> def
                | _ -> mk_term (un_curry_abs args def) top.range top.level in
            let body = desugar_term env def in
            let body = if is_rec then Subst.close rec_bindings body else body in
            mk_lb (lbname, tun, body) in
        let lbs = List.map2 (desugar_one_def (if is_rec then env' else env)) fnames funs in
        let body = desugar_term env' body in
        mk <| (Tm_let((is_rec, lbs), Subst.close rec_bindings body)) in

      let ds_non_rec pat t1 t2 =
        let t1 = desugar_term env t1 in
        let env, binder, pat = desugar_binding_pat_maybe_top top_level env pat in
        begin match binder with
          | LetBinder(l, t) ->
            let body = desugar_term env t2 in
            mk <| Tm_let((false, [({lbname=Inr l; lbunivs=[]; lbeff=C.effect_ALL_lid; lbtyp=t; lbdef=t1})]), body)

          | LocalBinder (x,_) ->
            let body = desugar_term env t2 in
            let body = match pat with
              | None
              | Some ({v=Pat_wild _}) -> body
              | Some pat -> 
                S.mk (Tm_match(S.bv_to_name x, [U.branch (pat, None, body)])) None body.pos in
                mk <| Tm_let((false, [mk_lb (Inl x, x.sort, t1)]), Subst.close [S.mk_binder x] body)
        end in

      if is_rec 
      || is_app_pattern pat
      then ds_let_rec()
      else ds_non_rec pat _snd body

    | If(t1, t2, t3) ->
      mk (Tm_match(desugar_term env t1,
                    [(withinfo (Pat_constant (Const_bool true)) tun.n t2.range, None, desugar_term env t2);
                     (withinfo (Pat_constant (Const_bool false)) tun.n t3.range, None, desugar_term env t3)]))

    | TryWith(e, branches) ->
      let r = top.range in
      let handler = mk_function branches r r in
      let body = mk_function [(mk_pattern (PatConst Const_unit) r, None, e)] r r in
      let a1 = mk_term (App(mk_term (Var C.try_with_lid) r top.level, body, Nothing)) r  top.level in
      let a2 = mk_term (App(a1, handler, Nothing)) r top.level in
      desugar_term env a2

    | Match(e, branches) ->
      let desugar_branch (pat, wopt, b) =
        let env, pat = desugar_match_pat env pat in
        let bs = S.pat_bvs pat |> List.map S.mk_binder in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (Subst.close bs <| desugar_term env e) in
        let b = Subst.close bs <| desugar_term env b in
        (pat, wopt, b) in
      mk <| Tm_match(desugar_term env e, List.map desugar_branch branches)

    | Ascribed(e, t) ->
      mk <| Tm_ascribed(desugar_term env e, desugar_term env t, None)

    | Record(_, []) ->
      raise (Error("Unexpected empty record", top.range))

    | Record(eopt, fields) ->
      let f, _ = List.hd fields in
      let qfn g = lid_of_ids (f.ns@[g]) in
      let record, _ = fail_or  (try_lookup_record_by_field_name env) f in
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
          let x = FStar.Ident.gen e.range in
          let xterm = mk_term (Var (lid_of_ids [x])) x.idRange Expr in
          let record = Record(None, record.fields |> List.map (fun (f, _) -> get_field (Some xterm) f)) in
          Let(false, [(mk_pattern (PatVar (x, false)) x.idRange, e)], mk_term record top.range top.level) in

      let recterm = mk_term recterm top.range top.level in
      let e = desugar_term env recterm in
      begin match e.n with
        | Tm_meta({n=Tm_app({n=Tm_fvar(fv, _)}, args)}, Meta_desugared Data_app) ->
          let e = mk <| Tm_app(S.fvar (Some (Record_ctor(record.typename, record.fields |> List.map fst))) fv.v e.pos,
                               args)  in
          mk <| Tm_meta(e, Meta_desugared Data_app)

        | _ -> e
      end

    | Project(e, f) ->
      let fieldname, is_rec = fail_or  (try_lookup_projector_by_field_name env) f in
      let e = desugar_term env e in
      let fn =
        let ns, _ = Util.prefix fieldname.ns in
        lid_of_ids (ns@[f.ident]) in
      let qual = if is_rec then Some (Record_projector fn) else None in
      mk <| Tm_app(S.fvar (Some (Record_projector fn)) fieldname (range_of_lid f), [arg e])

    | NamedTyp(_, e)
    | Paren e ->
      desugar_term env e

    | _ when (top.level=Formula) -> desugar_formula env top

    | _ ->
      error "Unexpected term" top top.range
  end

and desugar_comp r default_ok env t =
    let fail msg = raise (Error(msg, r)) in
    let pre_process_comp_typ (t:AST.term) =
        let head, args = head_and_args t in
        match head.tm with
            | Name lemma when (lemma.ident.idText = "Lemma") ->
              let unit = mk_term (Name C.unit_lid) t.range Type, Nothing in
              let nil_pat = mk_term (Name C.nil_lid) t.range Expr, Nothing in
              let decreases_clause, args = args |> List.partition (fun (arg, _) ->
                  match (unparen arg).tm with
                    | App({tm=Var d}, _, _) -> d.ident.idText = "decreases"
                    | _ -> false) in
              let args = match args with
                    | [] -> raise (Error("Not enough arguments to 'Lemma'", t.range))
                    | [ens] -> (* a single ensures clause *)
                      let req_true = mk_term (Requires (mk_term (Name C.true_lid) t.range Formula, None)) t.range Type, Nothing in
                      [unit;req_true;ens;nil_pat]
                    | [req;ens] -> [unit;req;ens;nil_pat]
                    | more -> unit::more in
              let t = mk_term (Construct(lemma, args@decreases_clause)) t.range t.level in
              desugar_term env t

            | Name tot when (tot.ident.idText = "Tot"
                             && not (Env.is_effect_name env C.effect_Tot_lid)
                             && lid_equals (Env.current_module env) C.prims_lid) ->
              //we're right at the beginning of Prims, when Tot isn't yet fully defined
              let args = List.map (fun (t, imp) -> arg_withimp_t imp <| desugar_term env t) args in
              S.mk (Tm_app(S.fvar None C.effect_Tot_lid r, args)) None r

            | _ -> desugar_term env t
        in
    let t = pre_process_comp_typ t in
    let head, args = Util.head_and_args t in
    match (Subst.compress head).n, args with
        | Tm_fvar (eff,_), (result_typ, _)::rest ->
          let dec, rest = rest |> List.partition (fun (t, _) -> 
                    begin match t.n with
                        | Tm_app({n=Tm_fvar(fv, _)}, [_]) -> lid_equals fv.v C.decreases_lid
                        | _ -> false
                    end) in

          let decreases_clause = dec |> List.map (fun (t, _) -> 
                      match t.n with
                        | Tm_app(_, [(arg, _)]) -> DECREASES arg
                        | _ -> failwith "impos") in
          if Env.is_effect_name env eff.v
          || lid_equals eff.v C.effect_Tot_lid  //We need the Tot effect before its definition is in scope; it is primitive
          then if lid_equals eff.v C.effect_Tot_lid && List.length decreases_clause=0
               then mk_Total result_typ
               else let flags =
                        if      lid_equals eff.v C.effect_Lemma_lid then [LEMMA]
                        else if lid_equals eff.v C.effect_Tot_lid   then [TOTAL]
                        else if lid_equals eff.v C.effect_ML_lid    then [MLEFFECT]
                        else [] in
                    let rest = 
                        if lid_equals eff.v C.effect_Lemma_lid
                        then match rest with 
                                | [req;ens;(pat, aq)] -> 
                                  [req; ens;
                                   (S.mk (Tm_meta(pat, Meta_desugared Meta_smt_pat)) None pat.pos, aq)]
                                | _ -> rest 
                        else rest in
                        mk_Comp ({effect_name=eff.v;
                                  result_typ=result_typ;
                                  effect_args=rest;
                                  flags=flags@decreases_clause})
           else if default_ok
           then env.default_result_effect t r
           else fail (Util.format1 "%s is not an effect" (Print.term_to_string t))
       | _  ->
         if default_ok
         then env.default_result_effect t r
         else fail (Util.format1 "%s is not an effect" (Print.term_to_string t))

and desugar_formula env (f:term) : S.term =
  let connective s = match s with
    | "/\\"  -> Some C.and_lid
    | "\\/"  -> Some C.or_lid
    | "==>"  -> Some C.imp_lid
    | "<==>" -> Some C.iff_lid
    | "~"    -> Some C.not_lid
    | _ -> None in
  let mk t = S.mk t None f.range in
  let pos t = t None f.range in
  let setpos t = {t with pos=f.range} in
  let desugar_quant (q:lident) (qt:lident) b pats body =
    let tk = desugar_binder env ({b with blevel=Formula}) in
    let desugar_pats env pats = List.map (fun es -> es |> List.map (fun e -> arg_withimp_t Nothing <| desugar_term env e)) pats in
    match tk with
      | Some a, k ->
        let env, a = push_bv env a in
        let a = {a with sort=k} in
        let pats = desugar_pats env pats in
        let body = desugar_formula env body in
        let body = match pats with
          | [] -> body
          | _ -> mk (Tm_meta (body, Meta_pattern pats)) in
        let body = setpos <| U.abs [S.mk_binder a] body in
        mk <| Tm_app (S.fvar None (set_lid_range qt b.brange) b.brange, [arg body])

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
      mk <| Tm_meta(f, Meta_labeled(l, f.pos, p))

    | QForall([], _, _)
    | QExists([], _, _) -> failwith "Impossible: Quantifier without binders"

    | QForall((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QForall x) binders pats body)

    | QExists((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QExists x) binders pats body)

    | QForall([b], pats, body) ->
      desugar_quant C.forall_lid C.allTyp_lid b pats body

    | QExists([b], pats, body) ->
      desugar_quant C.exists_lid C.allTyp_lid b pats body

    | Paren f ->
      desugar_formula env f

    | _ -> desugar_term env f

and typars_of_binders env bs =
    let env, tpars = List.fold_left (fun (env, out) b ->
        let tk = desugar_binder env ({b with blevel=Formula}) in  (* typars follow the same binding conventions as formulas *)
        match tk with
            | Some a, k ->
                let env, a = push_bv env a in
                let a = {a with sort=k} in
                (env, (a, b.aqual)::out)
            | _ -> raise (Error ("Unexpected binder", b.brange))) (env, []) bs in
    env, List.rev tpars

and desugar_binder env b : option<ident> * S.term = match b.b with
  | Annotated(x, t) -> Some x, desugar_term env t
  | TVariable t -> None, fail_or2 (try_lookup_id env) t
  | NoName t -> None, desugar_term env t
  | Variable x -> Some x, tun
  | _ -> raise (Error("Unexpected domain of an arrow or sum (expected a type)", b.brange))

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
    let disc_type = mk_Typ_fun(binders, Util.total_comp (Util.ftv C.bool_lid ktype) p) None p in
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
                if lid_equals C.prims_lid  (Env.current_module env)
                || fvq<>Data_ctor
                || Options.dont_gen_projectors (Env.current_module env).str
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
                        lbeff=C.effect_Tot_lid;
                        lbdef=imp;
                     } in
                     [Sig_let((false, [lb]), p, [], quals)] in
            Sig_val_decl(field_name, t, quals, range_of_lid field_name)::impl) |> List.flatten

let mk_data_projectors env = function
  | Sig_datacon(lid, t, tycon, quals, _, _) when (//(not env.iface || env.admitted_iface) &&
                                                not (lid_equals lid C.lexcons_lid)) ->
    let refine_domain =
        if (quals |> Util.for_some (function RecordConstructor _ -> true | _ -> false))
        then false
        else let l, _, _ = tycon in
             match Env.find_all_datacons env l with
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
  let tot = mk_term (Name (C.effect_Tot_lid)) rng Expr in
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
      TyconVariant(id, parms, kopt, [(constrName, Some constrTyp, false)]), fields |> List.map (fun (x, _) -> Env.qualify env x)
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
    let env = Env.push_namespace env lid in
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
                      | {lbname=Inr l} -> Env.lookup_letbinding_quals env l) in
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
    let t = fail_or  (try_lookup_typ_name env) C.exn_lid in
    let l = qualify env id in
    let se = Sig_datacon(l, t, (C.exn_lid,[],ktype), [ExceptionConstructor], [C.exn_lid], d.drange) in
    let se' = Sig_bundle([se], [ExceptionConstructor], [l], d.drange) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_projectors env se in
    let discs = mk_data_discriminators [] env C.exn_lid [] ktype [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | Exception(id, Some term) ->
    let t = desugar_typ env term in
    let t = mk_Typ_fun([null_v_binder t], mk_Total (fail_or (try_lookup_typ_name env) C.exn_lid)) None d.drange in
    let l = qualify env id in
    let se = Sig_datacon(l, t, (C.exn_lid,[],ktype), [ExceptionConstructor], [C.exn_lid], d.drange) in
    let se' = Sig_bundle([se], [ExceptionConstructor], [l], d.drange) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_projectors env se in
    let discs = mk_data_discriminators [] env C.exn_lid [] ktype [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | KindAbbrev(id, binders, k) ->
    let env_k, binders = desugar_binders env binders in
    let k = desugar_kind env_k k in
    let name = Env.qualify env id in
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
          begin match Env.try_lookup_effect_defn env eff.v with
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
    let env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders env eff_binders in
    let eff_k = desugar_kind env eff_kind in
    let env, decls = eff_decls |> List.fold_left (fun (env, out) decl ->
        let env, ses = desugar_decl env decl in
        env, List.hd ses::out) (env, []) in
    let decls = List.rev decls in
    let lookup s = match Env.try_resolve_typ_abbrev env (Env.qualify env (Syntax.mk_ident(s, d.drange))) with
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
    let lookup l = match Env.try_lookup_effect_name env l with
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
    [AST.mk_decl (AST.Open C.prims_lid) dummyRange;
     AST.mk_decl (AST.Open C.all_lid) dummyRange]

(* Most important function: from AST to a module
   Keeps track of the name of variables and so on (in the context)
 *)
let desugar_modul_common curmod env (m:AST.modul) : env_t * Syntax.modul * bool =
  let open_ns (mname:lident) d =
    let d = if List.length mname.ns <> 0
            then (AST.mk_decl (AST.Open (Syntax.lid_of_ids mname.ns)) (Syntax.range_of_lid mname))  :: d
            else d in
    d in
  let env = match curmod with
    | None -> env
    | Some(prev_mod, _) ->  Env.finish_module_or_interface env prev_mod in
  let (env, pop_when_done), mname, decls, intf = match m with
    | Interface(mname, decls, admitted) ->
      Env.prepare_module_or_interface true admitted env mname, mname, open_ns mname decls, true
    | Module(mname, decls) ->
      Env.prepare_module_or_interface false false env mname, mname, open_ns mname decls, false in
  let env, sigelts = desugar_decls env decls in
  let modul = {
    name = mname;
    declarations = sigelts;
    exports = [];
    is_interface=intf;
    is_deserialized=false
  } in
  env, modul, pop_when_done

let desugar_partial_modul curmod env (m:AST.modul) : env_t * Syntax.modul =
  let m =
    if !Options.interactive_fsi then
        match m with
            | Module(mname, decls) -> AST.Interface(mname, decls, Util.for_some (fun m -> m=mname.str) !Options.admit_fsi)
            | Interface(mname, _, _) -> failwith ("Impossible: " ^ mname.ident.idText)
    else m
  in
  let x, y, _ = desugar_modul_common curmod env m in
  x,y

let desugar_modul env (m:AST.modul) : env_t * Syntax.modul =
  let env, modul, pop_when_done = desugar_modul_common None env m in
  let env = Env.finish_module_or_interface env modul in
  if Options.should_dump modul.name.str then Util.fprint1 "%s\n" (Print.modul_to_string modul);
  (if pop_when_done then export_interface modul.name env else env), modul

let desugar_file env (f:file) =
  let env, mods = List.fold_left (fun (env, mods) m ->
    let env, m = desugar_modul env m in
    env, m::mods) (env, []) f in
  env, List.rev mods 

let add_modul_to_env (m:Syntax.modul) (en: env) :env =
  let en, pop_when_done = Env.prepare_module_or_interface false false en m.name in
  let en = List.fold_left Env.push_sigelt ({ en with curmodule = Some(m.name) }) m.exports in
  let env = Env.finish_module_or_interface en m in
  if pop_when_done then export_interface m.name env else env
