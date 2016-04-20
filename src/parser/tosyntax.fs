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

// VALS_HACK_HERE

let trans_aqual = function
  | Some AST.Implicit -> Some S.imp_tag
  | Some AST.Equality -> Some S.Equality
  | _ -> None

let trans_qual r = function
  | AST.Private ->       S.Private
  | AST.Assumption ->    S.Assumption
  | AST.Inline ->        S.Inline
  | AST.Unfoldable ->    S.Unfoldable
  | AST.Irreducible ->   S.Irreducible
  | AST.Logic ->         S.Logic
  | AST.TotalEffect ->   S.TotalEffect
  | AST.Effect ->        S.Effect
  | AST.New  ->          S.New
  | AST.Abstract ->      S.Abstract
  | AST.Opaque ->        FStar.TypeChecker.Errors.warn r "The 'opaque' qualifier is deprecated; use 'unfoldable', which is also the default"; S.Unfoldable 
  | AST.DefaultEffect -> raise (Error("The 'default' qualifier on effects is no longer supported", r))
  
let trans_pragma = function
  | AST.SetOptions s -> S.SetOptions s
  | AST.ResetOptions sopt -> S.ResetOptions sopt

let as_imp = function
    | Hash -> Some S.imp_tag 
    | _ -> None
let arg_withimp_e imp t =
    t, as_imp imp
let arg_withimp_t imp t =
    match imp with
        | Hash -> t, Some S.imp_tag
        | _ -> t, None

let contains_binder binders =
  binders |> Util.for_some (fun b -> match b.b with
    | Annotated _ -> true
    | _ -> false)

let rec unparen t = match t.tm with
  | Paren t -> unparen t
  | _ -> t

let tm_type_z r = mk_term (Name (lid_of_path ["Type0"] r)) r Kind
let tm_type r = mk_term (Name (lid_of_path   [ "Type"] r)) r Kind

let rec delta_qualifier t = 
    let t = Subst.compress t in
    match t.n with
        | Tm_delayed _ -> failwith "Impossible"
        | Tm_fvar fv -> fv.fv_delta 
        | Tm_bvar _
        | Tm_name _ 
        | Tm_match _ 
        | Tm_uvar _ 
        | Tm_unknown -> Delta_equational
        | Tm_type _
        | Tm_constant _
        | Tm_arrow _ -> Delta_constant
        | Tm_uinst(t, _)
        | Tm_refine({sort=t}, _)
        | Tm_meta(t, _)
        | Tm_ascribed(t, _, _)
        | Tm_app(t, _) 
        | Tm_abs(_, t, _) 
        | Tm_let(_, t) -> delta_qualifier t

let incr_delta_qualifier t = 
    let d = delta_qualifier t in
    let rec aux d = match d with
        | Delta_equational -> d
        | Delta_constant -> Delta_unfoldable 1
        | Delta_unfoldable i -> Delta_unfoldable (i + 1)
        | Delta_abstract d -> aux d in
    aux d
 
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

let op_as_term env arity rng s : option<S.term> =
  let r l dd = Some (S.lid_as_fv (set_lid_range l rng) dd None |> S.fv_to_tm) in
  let fallback () =
      match s with
        | "=" ->    r C.op_Eq Delta_equational
        | ":=" ->   r C.op_ColonEq Delta_equational
        | "<" ->    r C.op_LT Delta_equational
        | "<=" ->   r C.op_LTE Delta_equational
        | ">" ->    r C.op_GT Delta_equational
        | ">=" ->   r C.op_GTE Delta_equational
        | "&&" ->   r C.op_And Delta_equational
        | "||" ->   r C.op_Or Delta_equational
        | "+" ->    r C.op_Addition Delta_equational
        | "-" when (arity=1) -> r C.op_Minus Delta_equational
        | "-" ->    r C.op_Subtraction Delta_equational
        | "/" ->    r C.op_Division Delta_equational
        | "%" ->    r C.op_Modulus Delta_equational
        | "!" ->    r C.read_lid Delta_equational
        | "@" ->    r C.list_append_lid Delta_equational
        | "^" ->    r C.strcat_lid Delta_equational
        | "|>" ->   r C.pipe_right_lid Delta_equational
        | "<|" ->   r C.pipe_left_lid Delta_equational
        | "<>" ->   r C.op_notEq Delta_equational
        | "~"   ->  r C.not_lid (Delta_unfoldable 2)
        | "=="  ->  r C.eq2_lid Delta_constant
        | "<<" ->   r C.precedes_lid Delta_constant
        | "/\\" ->  r C.and_lid (Delta_unfoldable 1)
        | "\\/" ->  r C.or_lid (Delta_unfoldable 1)
        | "==>" ->  r C.imp_lid (Delta_unfoldable 1)
        | "<==>" -> r C.iff_lid (Delta_unfoldable 2)
        | _ -> None in
   begin match Env.try_lookup_lid env (compile_op_lid arity s rng) with
        | Some t -> Some t
        | _ -> fallback()
   end

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
  | Labeled _ -> failwith "Impossible --- labeled source term"

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


  | Abs _  (* not closing implicitly over free vars in all these forms: TODO: Fixme! *)
  | Let _
  | If _
  | QForall _
  | QExists _  
  | Record _ 
  | Match _
  | TryWith _
  | Seq _ -> []

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
       let t = match (unparen t).tm with
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

let mk_lb (n, t, e) = {lbname=n; lbunivs=[]; lbeff=C.effect_ALL_lid; lbtyp=t; lbdef=e}
let no_annot_abs bs t = U.abs bs t None 

let rec desugar_data_pat env p : (env_t * bnd * Syntax.pat) =
  let check_linear_pattern_variables (p:Syntax.pat) = 
    let rec pat_vars (p:Syntax.pat) = match p.v with 
      | Pat_dot_term _
      | Pat_wild _
      | Pat_constant _ -> S.no_names
      | Pat_var x -> Util.set_add x S.no_names
      | Pat_cons(_, pats) -> 
        pats |> List.fold_left (fun out (p, _) -> Util.set_union out (pat_vars p)) S.no_names
      | Pat_disj [] -> failwith "Impossible"
      | Pat_disj (hd::tl) ->
        let xs = pat_vars hd in
        if not (Util.for_all (fun p -> let ys = pat_vars p in 
                              Util.set_is_subset_of xs ys 
                              && Util.set_is_subset_of ys xs) tl)
        then raise (Error ("Disjunctive pattern binds different variables in each case", p.p))
        else xs in
    pat_vars p in

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
        loc, env, LocalBinder(x, None), pos <| Pat_wild x, false

      | PatConst c ->
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_constant c, false

      | PatTvar(x, aq)
      | PatVar (x, aq) ->
        let imp = (aq=Some Implicit) in
        let aq = trans_aqual aq in
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
            pos_r r <| Pat_cons(S.lid_as_fv C.cons_lid Delta_constant (Some Data_ctor), [(hd, false);(tl, false)])) pats
                        (pos_r (Range.end_range p.prange) <| Pat_cons(S.lid_as_fv C.nil_lid Delta_constant (Some Data_ctor), [])) in
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
            | Pat_cons(fv, args) -> pos <| Pat_cons(({fv with fv_qual=Some (Record_ctor (record.typename, record.fields |> List.map fst))}), args)
            | _ -> p in
        env, e, b, p, false in

  let _, env, b, p, _ = aux [] env p in
  ignore <| check_linear_pattern_variables p;
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

and desugar_term env e : S.term = 
    let env = {env with expect_typ=false} in
    desugar_term_maybe_top false env e

and desugar_typ env e : S.term = 
    let env = {env with expect_typ=true} in
    desugar_term_maybe_top false env e

and desugar_term_maybe_top (top_level:bool) (env:env_t) (top:term) : S.term =
  let mk e = S.mk e None top.range in
  let setpos e = {e with pos=top.range} in
  begin match (unparen top).tm with
    | Wild -> setpos tun
   
    | Labeled _ -> desugar_formula env top
   
    | Requires (t, lopt) ->
      desugar_formula env t

    | Ensures (t, lopt) ->
      desugar_formula env t

    | Const c -> mk (Tm_constant c)

    | Op("=!=", args) ->
      desugar_term env (mk_term(Op("~", [mk_term (Op("==", args)) top.range top.level])) top.range top.level)

    | Op("*", [_;_]) when (op_as_term env 2 top.range "*" |> Option.isNone) -> //if op_Star has not been rebound, then it's reserved for tuples
      let rec flatten t = match t.tm with
            | Op("*", [t1;t2]) ->
              let rest = flatten t2 in
              t1::rest
            | _ -> [t] in
      let targs = flatten (unparen top) |> List.map (fun t -> as_arg (desugar_typ env t)) in
      let tup = fail_or (Env.try_lookup_lid env) (Util.mk_tuple_lid (List.length targs) top.range) in
      mk (Tm_app(tup, targs))

    | Tvar a ->
      setpos <| fail_or2 (try_lookup_id env) a

    | Op(s, args) ->
      begin match op_as_term env (List.length args) top.range s with
        | None -> raise (Error("Unexpected operator: " ^ s, top.range))
        | Some op ->
          let args = args |> List.map (fun t -> desugar_term env t, None) in
          mk (Tm_app(op, args))
      end

    | Name {str="Type0"}  -> mk (Tm_type U_zero)
    | Name {str="Type"}   -> mk (Tm_type U_unknown)
    | Name {str="Effect"} -> mk (Tm_constant Const_effect)
    | Name {str="True"}   -> S.fvar (Ident.set_lid_range Const.true_lid top.range) Delta_constant None
    | Name {str="False"}   -> S.fvar (Ident.set_lid_range Const.false_lid top.range) Delta_constant None
   
    | Var l
    | Name l ->
      setpos <| fail_or (Env.try_lookup_lid env) l

    | Construct(l, args) ->
      let head, is_data = match Env.try_lookup_datacon env l with 
        | None -> fail_or (Env.try_lookup_lid env) l, false
        | Some head -> mk (Tm_fvar head), true in
      begin match args with
        | [] -> head
        | _ ->
          let args = List.map (fun (t, imp) ->
            let te = desugar_term env t in
            arg_withimp_e imp te) args in
          let app = mk (Tm_app(head, args)) in
          if is_data 
          then mk (Tm_meta(app, Meta_desugared Data_app))
          else app
      end

    | Sum(binders, t) ->
      let env, _, targs = List.fold_left (fun (env, tparams, typs) b ->
                let xopt, t = desugar_binder env b in
                let env, x = 
                    match xopt with
                    | None -> env, S.new_bv (Some top.range) tun
                    | Some x -> push_bv env x in
                (env, tparams@[{x with sort=t}, None], typs@[as_arg <| no_annot_abs tparams t]))
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
      let binders = (ftv |> List.map (fun a -> mk_pattern (PatTvar(a, Some AST.Implicit)) top.range))@binders in //close over the free type variables
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
              setpos (no_annot_abs (List.rev bs) body)

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
                                  let tup2 = S.lid_as_fv (Util.mk_tuple_data_lid 2 top.range) Delta_constant (Some Data_ctor) in
                                  let sc = S.mk (Tm_app(mk (Tm_fvar tup2), [as_arg sc; as_arg <| S.bv_to_name x])) None top.range in
                                  let p = withinfo (Pat_cons(tup2, [(p', false);(p, false)])) tun.n (Range.union_ranges p'.p p.p) in
                                  Some(sc, p)
                                | Tm_app(_, args), Pat_cons(_, pats) ->
                                  let tupn = S.lid_as_fv (Util.mk_tuple_data_lid (1 + List.length args) top.range) Delta_constant (Some Data_ctor) in
                                  let sc = mk (Tm_app(mk (Tm_fvar tupn), args@[as_arg <| S.bv_to_name x])) in
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
      mk (Tm_app(fvar a Delta_equational None,
                 [as_arg phi;
                  as_arg <| mk (Tm_constant(Const_unit))]))

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
      let ds_let_rec_or_app () =
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
                push_top_level_rec_binding env l.ident S.Delta_equational, Inr l, rec_bindings in
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
            let lbname = match lbname with
                | Inl x -> Inl x
                | Inr l -> Inr (S.lid_as_fv l (incr_delta_qualifier body) None) in
            let body = if is_rec then Subst.close rec_bindings body else body in
            mk_lb (lbname, tun, body) in
        let lbs = List.map2 (desugar_one_def (if is_rec then env' else env)) fnames funs in
        let body = desugar_term env' body in
        mk <| (Tm_let((is_rec, lbs), Subst.close rec_bindings body)) in
      //end ds_let_rec_or_app

      let ds_non_rec pat t1 t2 =
        let t1 = desugar_term env t1 in
        let env, binder, pat = desugar_binding_pat_maybe_top top_level env pat in
        begin match binder with
          | LetBinder(l, t) ->
            let body = desugar_term env t2 in
            let fv = S.lid_as_fv l (incr_delta_qualifier t1) None in
            mk <| Tm_let((false, [({lbname=Inr fv; lbunivs=[]; lbeff=C.effect_ALL_lid; lbtyp=t; lbdef=t1})]), body)

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
      then ds_let_rec_or_app()
      else ds_non_rec pat _snd body

    | If(t1, t2, t3) ->
      let x = Syntax.new_bv (Some t3.range) S.tun in
      mk (Tm_match(desugar_term env t1,
                    [(withinfo (Pat_constant (Const_bool true)) tun.n t2.range, None, desugar_term env t2);
                     (withinfo (Pat_wild x) tun.n t3.range, None, desugar_term env t3)]))

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
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (desugar_term env e) in
        let b = desugar_term env b in
        Util.branch (pat, wopt, b) in
      mk <| Tm_match(desugar_term env e, List.map desugar_branch branches)

    | Ascribed(e, t) ->
      let env = Env.default_ml env in
      let c = desugar_comp t.range true env t in
      let annot = if Util.is_ml_comp c
                  then Inl (Util.comp_result c)
                  else Inr c in
      mk <| Tm_ascribed(desugar_term env e, annot, None)

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
          Let(false, [(mk_pattern (PatVar (x, None)) x.idRange, e)], mk_term record top.range top.level) in

      let recterm = mk_term recterm top.range top.level in
      let e = desugar_term env recterm in
      begin match e.n with
        | Tm_meta({n=Tm_app({n=Tm_fvar fv}, args)}, Meta_desugared Data_app) ->
          let e = mk <| Tm_app(S.fvar (Ident.set_lid_range fv.fv_name.v e.pos) Delta_constant (Some (Record_ctor(record.typename, record.fields |> List.map fst))),
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
      mk <| Tm_app(S.fvar (Ident.set_lid_range fieldname (range_of_lid f)) Delta_equational qual, [as_arg e])

    | NamedTyp(_, e)
    | Paren e ->
      desugar_term env e

    | _ when (top.level=Formula) -> desugar_formula env top

    | _ ->
      error "Unexpected term" top top.range
  end

and desugar_args env args = 
    args |> List.map (fun (a, imp) -> arg_withimp_e imp (desugar_term env a))
          
and desugar_comp r default_ok env t =
    let fail : string -> 'a = fun msg -> raise (Error(msg, r)) in
    let is_requires (t, _) = match (unparen t).tm with 
        | Requires _ -> true
        | _ -> false in
    let is_ensures (t, _) = match (unparen t).tm with 
        | Ensures _ -> true
        | _ -> false in
    let is_app head (t, _) = match (unparen t).tm with 
       | App({tm=Var d}, _, _) -> d.ident.idText = head
       | _ -> false in
    let is_decreases = is_app "decreases" in
    let pre_process_comp_typ (t:AST.term) =
        let head, args = head_and_args t in
        match head.tm with
            | Name lemma when (lemma.ident.idText = "Lemma") -> //need to add the unit result type and the empty SMTPat list, if n
              let unit_tm = mk_term (Name C.unit_lid) t.range Type, Nothing in
              let nil_pat = mk_term (Name C.nil_lid) t.range Expr, Nothing in
              let req_true = mk_term (Requires (mk_term (Name C.true_lid) t.range Formula, None)) t.range Type, Nothing in
              let args = match args with
                    | [] -> raise (Error("Not enough arguments to 'Lemma'", t.range))
                    | [ens] -> [unit_tm;req_true;ens;nil_pat] //a single ensures clause
                    | [req;ens] when (is_requires req && is_ensures ens) -> [unit_tm;req;ens;nil_pat]
                    | [ens;dec] when (is_ensures ens && is_decreases dec) -> [unit_tm;req_true;ens;nil_pat;dec]
                    | [req;ens;dec] when (is_requires req && is_ensures ens && is_app "decreases" dec) -> [unit_tm;req;ens;nil_pat;dec]
                    | more -> unit_tm::more in      
              let head = fail_or (Env.try_lookup_effect_name env) lemma in
              head, args

            | Name l when Env.is_effect_name env l ->
             //we have an explicit effect annotation ... no need to add anything
             fail_or (Env.try_lookup_effect_name env) l, args


            | Name l when (lid_equals (Env.current_module env) C.prims_lid //we're right at the beginning of Prims, when Tot isn't yet fully defined           
                               && l.ident.idText = "Tot") ->
             //we have an explicit effect annotation ... no need to add anything
             Ident.set_lid_range Const.effect_Tot_lid head.range, args

            | Name l when (lid_equals (Env.current_module env) C.prims_lid //we're right at the beginning of Prims, when GTot isn't yet fully defined           
                               && l.ident.idText = "GTot") ->
             //we have an explicit effect annotation ... no need to add anything
             Ident.set_lid_range Const.effect_GTot_lid head.range, args
       
            | Name l when ((l.ident.idText="Type" 
                            || l.ident.idText="Type0"
                            || l.ident.idText="Effect")
                           && default_ok) -> 
              //the default effect for Type is always Tot
              Ident.set_lid_range Const.effect_Tot_lid head.range, [t, Nothing]
             
            | _  when default_ok -> //add the default effect              
             Ident.set_lid_range env.default_result_effect head.range, [t, Nothing]
          
            | _ -> 
             fail (Util.format1 "%s is not an effect" (AST.term_to_string t)) in
    let eff, args = pre_process_comp_typ t in
    if List.length args = 0 
    then fail (Util.format1 "Not enough args to effect %s" (Print.lid_to_string eff));
    let result_arg, rest = List.hd args, List.tl args in
    let result_typ = desugar_typ env (fst result_arg) in
    let rest = desugar_args env rest in
    let dec, rest = rest |> List.partition (fun (t, _) -> 
            begin match t.n with
                | Tm_app({n=Tm_fvar fv}, [_]) -> S.fv_eq_lid fv C.decreases_lid
                | _ -> false
            end) in

    let decreases_clause = dec |> List.map (fun (t, _) -> 
                match t.n with
                | Tm_app(_, [(arg, _)]) -> DECREASES arg
                | _ -> failwith "impos") in
    let no_additional_args = List.length decreases_clause = 0
                             && List.length rest = 0 in
    if no_additional_args 
    && lid_equals eff C.effect_Tot_lid 
    then mk_Total result_typ
    else if no_additional_args 
         && lid_equals eff C.effect_GTot_lid 
    then mk_GTotal result_typ
    else let flags =
            if      lid_equals eff C.effect_Lemma_lid then [LEMMA]
            else if lid_equals eff C.effect_Tot_lid   then [TOTAL]
            else if lid_equals eff C.effect_ML_lid    then [MLEFFECT]
            else if lid_equals eff C.effect_GTot_lid  then [SOMETRIVIAL]
            else [] in
        let rest = 
            if lid_equals eff C.effect_Lemma_lid
            then match rest with 
                    | [req;ens;(pat, aq)] -> 
                      let pat = match pat.n with 
                        | Tm_fvar fv when S.fv_eq_lid fv Const.nil_lid -> //we really want the empty pattern to be in universe S 0 rather than generalizing it 
                          let nil = S.mk_Tm_uinst pat [U_succ U_zero] in
                          let pattern = S.mk_Tm_uinst (S.fvar (Ident.set_lid_range Const.pattern_lid pat.pos) Delta_constant None) [U_zero] in //;U_zero] in 
                          S.mk_Tm_app nil [(pattern, Some S.imp_tag)] None pat.pos 
                        | _ -> pat in
                        [req; ens;
                        (S.mk (Tm_meta(pat, Meta_desugared Meta_smt_pat)) None pat.pos, aq)]
                    | _ -> rest 
            else rest in
        mk_Comp ({effect_name=eff;
                    result_typ=result_typ;
                    effect_args=rest;
                    flags=flags@decreases_clause})
           
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
  let desugar_quant (q:lident) b pats body =
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
        let body = setpos <| no_annot_abs [S.mk_binder a] body in
        mk <| Tm_app (S.fvar (set_lid_range q b.brange) (Delta_unfoldable 1) None, [as_arg body])

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
      desugar_quant C.forall_lid b pats body

    | QExists([b], pats, body) ->
      desugar_quant C.exists_lid b pats body

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
                (env, (a, trans_aqual b.aqual)::out)
            | _ -> raise (Error ("Unexpected binder", b.brange))) (env, []) bs in
    env, List.rev tpars

and desugar_binder env b : option<ident> * S.term = match b.b with
  | TAnnotated(x, t)
  | Annotated(x, t) -> Some x, desugar_typ env t
  | TVariable x     -> Some x, mk (Tm_type U_unknown) None x.idRange
  | NoName t        -> None, desugar_typ env t
  | Variable x      -> Some x, tun

let mk_data_discriminators quals env t tps k datas =
    let quals q = if not <| env.iface || env.admitted_iface 
                  then S.Assumption::q@quals 
                  else q@quals in
    let binders = tps @ fst (U.arrow_formals k) in
    let p = range_of_lid t in
    let binders, args = Util.args_of_binders binders in
    let imp_binders = binders |> List.map (fun (x, _) -> x, Some S.imp_tag) in
    let binders = imp_binders@[S.null_binder <| (S.mk_Tm_app(S.fv_to_tm (S.lid_as_fv t Delta_constant None)) args None p)] in
    let disc_type = U.arrow binders (S.mk_Total (S.fv_to_tm (S.lid_as_fv C.bool_lid Delta_constant None))) in
    datas |> List.map (fun d ->
        let disc_name = Util.mk_discriminator d in
        Sig_declare_typ(disc_name, [], disc_type, quals [S.Logic; S.Discriminator d], range_of_lid disc_name))

let mk_indexed_projectors iquals fvq refine_domain env tc lid (inductive_tps:binders) imp_tps (fields:list<S.binder>) t =
    let p = range_of_lid lid in
    let pos q = Syntax.withinfo q tun.n p in
    let projectee ptyp = S.gen_bv "projectee" (Some p) ptyp in
    let tps = List.map2 (fun (_, imp) (x, _) -> (x, imp)) inductive_tps imp_tps in
    let arg_binder, indices =
        let head, args0 = Util.head_and_args t in
        let args = 
            let rec arguments tps args = match tps, args with 
                | [], _ -> args
                | _, [] -> raise (Error("Not enough arguments to type", Ident.range_of_lid lid))
                | (_, Some (S.Implicit _))::tps', (_, Some (S.Implicit _))::args' -> arguments tps' args'
                | (_, Some (S.Implicit _))::tps', (_, _)::_ -> arguments tps' args
                | (_, _)::_, (a, Some (S.Implicit _))::_ ->
                  raise (Error("Unexpected implicit annotation on argument", a.pos))
                | (_, _)::tps', (_, _)::args' -> arguments tps' args' in
            arguments inductive_tps args0 in
        let indices = args |> List.map (fun _ -> S.new_bv (Some p) tun |> S.mk_binder) in
        let arg_typ = S.mk_Tm_app (S.fv_to_tm (S.lid_as_fv tc Delta_constant None)) 
                                  (tps@indices |> List.map (fun (x, imp) -> S.bv_to_name x,imp)) None p in
        let arg_binder = 
            if not refine_domain
            then S.mk_binder (projectee arg_typ) //records have only one constructor; no point refining the domain
            else let disc_name = Util.mk_discriminator lid in
                 let x = S.new_bv (Some p) arg_typ in
                 S.mk_binder ({projectee arg_typ with sort=refine x (Util.b2t(S.mk_Tm_app (S.fvar (Ident.set_lid_range disc_name p) Delta_equational None)
                                                                                          [as_arg <| S.bv_to_name x] None p))}) in
        arg_binder, indices in

    let arg_exp = S.bv_to_name (fst arg_binder) in
    let imp_binders = imp_tps @ (indices |> List.map (fun (x, _) -> x, Some S.imp_tag)) in
    let binders = imp_binders@[arg_binder] in

    let arg = Util.arg_of_non_null_binder arg_binder in

    let subst = fields |> List.mapi (fun i (a, _) -> 
            let field_name, _ = Util.mk_field_projector_name lid a i in
            let proj = mk_Tm_app (S.fv_to_tm (S.lid_as_fv field_name Delta_equational None)) [arg] None p in
            NT(a, proj)) in

    let ntps = List.length tps in
    let all_params = imp_tps@fields in

    fields |> List.mapi (fun i (x, _) -> 
        let field_name, _ = Util.mk_field_projector_name lid x i in
        let t = U.arrow binders (S.mk_Total (Subst.subst subst x.sort)) in
        let only_decl = 
            lid_equals C.prims_lid  (Env.current_module env)
            || fvq<>Data_ctor
            || Options.dont_gen_projectors (Env.current_module env).str in
        let no_decl = Syntax.is_type x.sort in
        let quals q = if only_decl then S.Assumption::q else q in
        let quals = quals (S.Projector(lid, x.ppname)::iquals) in
        let decl = Sig_declare_typ(field_name, [], t, quals, range_of_lid field_name) in
        if only_decl
        then [decl] //only the signature
        else let projection = S.gen_bv x.ppname.idText None tun in
                let arg_pats = all_params |> List.mapi (fun j (x,imp) -> 
                    let b = S.is_implicit imp in
                    if i+ntps=j  //this is the one to project
                    then pos (Pat_var projection), b
                    else if b && j < ntps
                         then pos (Pat_dot_term (S.gen_bv x.ppname.idText None tun, tun)), b 
                         else pos (Pat_wild (S.gen_bv x.ppname.idText None tun)), b) in
            let pat = (S.Pat_cons(S.lid_as_fv lid Delta_constant (Some fvq), arg_pats) |> pos, None, S.bv_to_name projection) in
            let body = mk (Tm_match(arg_exp, [U.branch pat])) None p in
            let imp = no_annot_abs binders body in
            let dd = if quals |> List.contains S.Abstract 
                     then Delta_abstract Delta_equational
                     else Delta_equational in
            let lb = {  lbname=Inr (S.lid_as_fv field_name dd None);
                        lbunivs=[];
                        lbtyp=tun;
                        lbeff=C.effect_Tot_lid;
                        lbdef=imp } in
            let impl = Sig_let((false, [lb]), p, [lb.lbname |> right |> (fun fv -> fv.fv_name.v)], quals) in
            if no_decl then [impl] else [decl;impl]) |> List.flatten

let mk_data_projectors iquals env (inductive_tps, se) = match se with 
  | Sig_datacon(lid, _, t, l, n, quals, _, _) when (//(not env.iface || env.admitted_iface) &&
                                                not (lid_equals lid C.lexcons_lid)) ->
    let refine_domain =
        if (quals |> Util.for_some (function RecordConstructor _ -> true | _ -> false))
        then false
        else match Env.find_all_datacons env l with
                | Some l -> List.length l > 1
                | _ -> true in
        let formals, cod = U.arrow_formals t in
        begin match formals with 
            | [] -> [] //no fields to project
            | _ ->
              let fv_qual = match Util.find_map quals (function RecordConstructor fns -> Some (Record_ctor(lid, fns)) | _ -> None) with
                | None -> Data_ctor
                | Some q -> q in
              let iquals = if List.contains S.Abstract iquals
                           then S.Private::iquals
                           else iquals in
              let tps, rest = Util.first_N n formals in
              mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod
        end

  | _ -> []

let mk_typ_abbrev lid uvs typars k t lids quals rng = 
    let dd = if quals |> List.contains S.Abstract
             then Delta_abstract (incr_delta_qualifier t)
             else incr_delta_qualifier t in
    let lb = {    
        lbname=Inr (S.lid_as_fv lid dd None);
        lbunivs=uvs;
        lbdef=no_annot_abs typars t;
        lbtyp=U.arrow typars (S.mk_Total k);
        lbeff=C.effect_Tot_lid;
    } in
    Sig_let((false, [lb]), rng, lids, quals) 

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
        | None -> Util.ktype
        | Some k -> desugar_term _env' k in
      let tconstr = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type) binders in
      let qlid = qualify _env id in
      let typars = Subst.close_binders typars in
      let k = Subst.close typars k in
      let se = Sig_inductive_typ(qlid, [], typars, k, mutuals, [], quals, rng) in
      let _env = Env.push_top_level_rec_binding _env id S.Delta_constant in
      let _env2 = Env.push_top_level_rec_binding _env' id S.Delta_constant in
      _env, _env2, se, tconstr
    | _ -> failwith "Unexpected tycon" in
  let push_tparams env bs = 
    let env, bs = List.fold_left (fun (env, tps) (x, imp) -> 
        let env, y = Env.push_bv env x.ppname in
        env, (y, imp)::tps) (env, []) bs in 
    env, List.rev bs in
  match tcs with
    | [TyconAbstract(id, bs, kopt)] ->
        let kopt = match kopt with 
            | None -> Some (tm_type_z id.idRange)
            | _ -> kopt in
        let tc = TyconAbstract(id, bs, kopt) in
        let _, _, se, _ = desugar_abstract_tc quals env [] tc in
        let se = match se with 
           | Sig_inductive_typ(l, _, typars, k, [], [], quals, rng) -> 
             let quals = if quals |> List.contains S.Assumption
                         then quals
                         else (Util.print2 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n" 
                                                (Range.string_of_range rng) (Print.lid_to_string l);          
                               S.Assumption::S.New::quals) in
             let t = match typars with 
                | [] -> k
                | _ -> mk (Tm_arrow(typars, mk_Total k)) None rng in
             Sig_declare_typ(l, [], t, quals, rng)
           | _ -> se in
        let env = push_sigelt env se in
        (* let _ = pr "Pushed %s\n" (text_of_lid (qualify env (tycon_id tc))) in *)
        env, [se]

    | [TyconAbbrev(id, binders, kopt, t)] ->
        let env', typars = typars_of_binders env binders in
        let k = match kopt with
            | None ->
              if Util.for_some (function S.Effect -> true | _ -> false) quals
              then teff
              else tun
            | Some k -> desugar_term env' k in
        let t0 = t in
        let quals = if quals |> Util.for_some (function S.Logic -> true | _ -> false)
                    then quals
                    else if t0.level = Formula
                    then S.Logic::quals
                    else quals in
        let se =
            if quals |> List.contains S.Effect
            then let c = desugar_comp t.range false env' t in
                 let typars = Subst.close_binders typars in
                 let c = Subst.close_comp typars c in
                 Sig_effect_abbrev(qualify env id, [], typars, c, quals |> List.filter (function S.Effect -> false | _ -> true), rng)
            else let t = desugar_typ env' t in
                 let nm = qualify env id in
                 mk_typ_abbrev nm [] typars k t [nm] quals rng in
                  
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
      let tps_sigelts = tcs |> List.collect (function
        | Inr(Sig_inductive_typ(id, uvs, tpars, k, _, _, _, _), t, quals) -> //should be impossible
          let env_tps, _ = push_tparams env tpars in
          let t = desugar_term env_tps t in
          [[], mk_typ_abbrev id uvs tpars k t [id] quals rng]
          
        | Inl (Sig_inductive_typ(tname, univs, tpars, k, mutuals, _, tags, _), constrs, tconstr, quals) ->
          let tycon = (tname, tpars, k) in
          let env_tps, tps = push_tparams env tpars in
          let data_tpars = List.map (fun (x, _) -> (x, Some (S.Implicit true))) tps in
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
                let t = desugar_term (default_total env_tps) (close env_tps t) in
                let name = qualify env id in
                let quals = tags |> List.collect (function
                    | RecordType fns -> [RecordConstructor fns]
                    | _ -> []) in
                let ntps = List.length data_tpars in
                (name, (tps, Sig_datacon(name, univs, Util.arrow data_tpars (mk_Total (t |> Util.name_function_binders)), 
                                         tname, ntps, quals, mutuals, rng))))) in
              ([], Sig_inductive_typ(tname, univs, tpars, k, mutuals, constrNames, tags, rng))::constrs
        | _ -> failwith "impossible") in
      let sigelts = tps_sigelts |> List.map snd in
      let bundle = Sig_bundle(sigelts, quals, List.collect Util.lids_of_sigelt sigelts, rng) in
      let env = push_sigelt env0 bundle in
      let data_ops = tps_sigelts |> List.collect (mk_data_projectors quals env) in
      let discs = sigelts |> List.collect (function
        | Sig_inductive_typ(tname, _, tps, k, _, constrs, quals, _) when (List.length constrs > 1)->
          let quals = if List.contains S.Abstract quals
                      then S.Private::quals
                      else quals in
          mk_data_discriminators quals env tname tps k constrs
        | _ -> []) in
      let ops = discs@data_ops in
      let env = List.fold_left push_sigelt env ops in
      env, [bundle]@ops

    | [] -> failwith "impossible"

let desugar_binders env binders =
    let env, binders = List.fold_left (fun (env,binders) b ->
    match desugar_binder env b with
      | (Some a, k) ->
        let env, a = Env.push_bv env a in 
        env, S.mk_binder ({a with sort=k})::binders

      | _ -> raise (Error("Missing name in binder", b.brange))) (env, []) binders in
    env, List.rev binders

let rec desugar_effect env d (quals: qualifiers) eff_name eff_binders eff_kind eff_decls mk =
    let env0 = env in
    let env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders env eff_binders in
    let eff_k = desugar_term (Env.default_total env) eff_kind in
    let env, decls = eff_decls |> List.fold_left (fun (env, out) decl ->
        let env, ses = desugar_decl env decl in
        env, List.hd ses::out) (env, []) in
    let binders = Subst.close_binders binders in
    let eff_k = Subst.close binders eff_k in
    let lookup s =
        let l = Env.qualify env (mk_ident(s, d.drange)) in
        [], Subst.close binders <| fail_or (try_lookup_definition env) l in
    let mname       =qualify env0 eff_name in
    let qualifiers  =List.map (trans_qual d.drange) quals in
    let se = mk mname qualifiers binders eff_k lookup in
    let env = push_sigelt env0 se in
    env, [se]

and desugar_decl env (d:decl) : (env_t * sigelts) = 
  let trans_qual = trans_qual d.drange in
  match d.d with
  | Pragma p ->
    let se = Sig_pragma(trans_pragma p, d.drange) in
    env, [se]

  | TopLevelModule _ -> 
    raise (Error("Multiple modules in a file are no longer supported", d.drange)) //the parser desugars this away with a warning

  | Open lid ->
    let env = Env.push_namespace env lid in
    env, []

  | ModuleAbbrev(x, l) ->
    Env.push_module_abbrev env x l, []

  | Tycon(qual, tcs) ->
    desugar_tycon env d.drange (List.map trans_qual qual) tcs

  | ToplevelLet(quals, isrec, lets) ->
    begin match (Subst.compress <| desugar_term_maybe_top true env (mk_term (Let(isrec, lets, mk_term (Const Const_unit) d.drange Expr)) d.drange Expr)).n with
        | Tm_let(lbs, _) ->
          let fvs = snd lbs |> List.map (fun lb -> right lb.lbname) in
          let quals = match quals with 
            | _::_ -> List.map trans_qual quals 
            | _ -> snd lbs |> List.collect
            (function | {lbname=Inl _} -> []
                      | {lbname=Inr fv} -> Env.lookup_letbinding_quals env fv.fv_name.v) in
          let quals = 
            if lets |> Util.for_some (fun (_, t) -> t.level=Formula)
            then S.Logic::quals
            else quals in
          let lbs = if quals |> List.contains S.Abstract
                    then fst lbs, snd lbs |> List.map (fun lb -> 
                            let fv = right lb.lbname in
                            {lb with lbname=Inr ({fv with fv_delta=Delta_abstract fv.fv_delta})}) 
                    else lbs in
          let s = Sig_let(lbs, d.drange, fvs |> List.map (fun fv -> fv.fv_name.v), quals) in
          let env = push_sigelt env s in
          env, [s]
        | _ -> failwith "Desugaring a let did not produce a let"
    end

  | Main t ->
    let e = desugar_term env t in
    let se = Sig_main(e, d.drange) in
    env, [se]

  | Assume(atag, id, t) ->
    let f = desugar_formula env t in
    env, [Sig_assume(qualify env id, f, [S.Assumption], d.drange)]

  | Val(quals, id, t) ->
    let t = desugar_term env (close_fun env t) in
    let quals = if env.iface && env.admitted_iface then Assumption::quals else quals in
    let se = Sig_declare_typ(qualify env id, [], t, List.map trans_qual quals, d.drange) in
    let env = push_sigelt env se in
    env, [se]

  | Exception(id, None) ->
    let t = fail_or (try_lookup_lid env) C.exn_lid in
    let l = qualify env id in
    let se = Sig_datacon(l, [], t, C.exn_lid, 0, [ExceptionConstructor], [C.exn_lid], d.drange) in
    let se' = Sig_bundle([se], [ExceptionConstructor], [l], d.drange) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_projectors [] env ([], se) in
    let discs = mk_data_discriminators [] env C.exn_lid [] tun [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | Exception(id, Some term) ->
    let t = desugar_term env term in
    let t = U.arrow ([null_binder t]) (mk_Total <| fail_or (try_lookup_lid env) C.exn_lid) in
    let l = qualify env id in
    let se = Sig_datacon(l, [], t, C.exn_lid, 0, [ExceptionConstructor], [C.exn_lid], d.drange) in
    let se' = Sig_bundle([se], [ExceptionConstructor], [l], d.drange) in
    let env = push_sigelt env se' in
    let data_ops = mk_data_projectors [] env ([], se) in
    let discs = mk_data_discriminators [] env C.exn_lid [] tun [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | KindAbbrev(id, binders, k) ->
    let env_k, binders = desugar_binders env binders in
    let k = desugar_term env_k k in
    let name = Env.qualify env id in
    let se = mk_typ_abbrev name [] binders tun k [name] [] d.drange in
    let env = push_sigelt env se in
    env, [se]

  | NewEffect (quals, RedefineEffect(eff_name, eff_binders, defn)) ->
    let env0 = env in
    let env, binders = desugar_binders env eff_binders in
    let ed, args = 
        let head, args = head_and_args defn in 
        let ed = match head.tm with 
          | Name l -> fail_or (Env.try_lookup_effect_defn env) l
          | _ -> raise (Error("Effect " ^AST.term_to_string head^ " not found", d.drange)) in
        ed, desugar_args env args in
    let binders = Subst.close_binders binders in
    let sub (_, x) =
        let edb, x = Subst.open_term ed.binders x in
        let s = Util.subst_of_list edb args in
        [], Subst.close binders (Subst.subst s x) in
    let ed = {
            mname=qualify env0 eff_name;
            qualifiers  =List.map trans_qual quals;
            univs       =[];
            binders     =binders;
            signature   =snd (sub ([], ed.signature));
            ret         =sub ed.ret;
            bind_wp     =sub ed.bind_wp;
            bind_wlp    =sub ed.bind_wlp;
            if_then_else=sub ed.if_then_else;
            ite_wp      =sub ed.ite_wp;
            ite_wlp     =sub ed.ite_wlp;
            wp_binop    =sub ed.wp_binop;
            wp_as_type  =sub ed.wp_as_type;
            close_wp    =sub ed.close_wp;
            assert_p    =sub ed.assert_p;
            assume_p    =sub ed.assume_p;
            null_wp     =sub ed.null_wp;
            trivial     =sub ed.trivial
    } in
    let se = Sig_new_effect(ed, d.drange) in
    let env = push_sigelt env0 se in
    env, [se]

  | NewEffectForFree (RedefineEffect _) ->
    failwith "impossible"

  | NewEffectForFree (DefineEffect(eff_name, eff_binders, eff_kind, eff_decls)) ->
    desugar_effect
      env d [] eff_name eff_binders eff_kind eff_decls
      (fun mname qualifiers binders eff_k lookup ->
        let dummy_tscheme = [], mk Tm_unknown None Range.dummyRange in
        Sig_new_effect_for_free ({
          mname       = mname;
          qualifiers  = qualifiers;
          univs       = [];
          binders     = binders;
          signature   = eff_k;
          ret         = lookup "return";
          bind_wp     = lookup "bind_wp";
          bind_wlp    = lookup "bind_wlp";
          if_then_else= dummy_tscheme;
          ite_wp      = lookup "ite_wp";
          ite_wlp     = lookup "ite_wlp";
          wp_binop    = lookup "wp_binop";
          wp_as_type  = lookup "wp_as_type";
          close_wp    = lookup "close_wp";
          assert_p    = lookup "assert_p";
          assume_p    = lookup "assume_p";
          null_wp     = lookup "null_wp";
          trivial     = lookup "trivial"
      }, d.drange))

  | NewEffect (quals, DefineEffect(eff_name, eff_binders, eff_kind, eff_decls)) ->
    desugar_effect
      env d quals eff_name eff_binders eff_kind eff_decls
      (fun mname qualifiers binders eff_k lookup ->
        Sig_new_effect({
          mname       = mname;
          qualifiers  = qualifiers;
          univs       = [];
          binders     = binders;
          signature   = eff_k;
          ret         = lookup "return";
          bind_wp     = lookup "bind_wp";
          bind_wlp    = lookup "bind_wlp";
          if_then_else= lookup "if_then_else";
          ite_wp      = lookup "ite_wp";
          ite_wlp     = lookup "ite_wlp";
          wp_binop    = lookup "wp_binop";
          wp_as_type  = lookup "wp_as_type";
          close_wp    = lookup "close_wp";
          assert_p    = lookup "assert_p";
          assume_p    = lookup "assume_p";
          null_wp     = lookup "null_wp";
          trivial     = lookup "trivial"
      }, d.drange))

  | SubEffect l ->
    let lookup l = match Env.try_lookup_effect_name env l with
        | None -> raise (Error("Effect name " ^Print.lid_to_string l^ " not found", d.drange))
        | Some l -> l in
    let src = lookup l.msource in
    let dst = lookup l.mdest in
    let lift = [],desugar_term env l.lift_op in
    let se = Sig_sub_effect({source=src; target=dst; lift=lift}, d.drange) in
    env, [se]

 let desugar_decls env decls =
    List.fold_left (fun (env, sigelts) d ->
        let env, se = desugar_decl env d in
        env, sigelts@se) (env, []) decls

let open_prims_all =
    [AST.mk_decl (AST.Open C.prims_lid) Range.dummyRange;
     AST.mk_decl (AST.Open C.all_lid) Range.dummyRange]

(* Most important function: from AST to a module
   Keeps track of the name of variables and so on (in the context)
 *)
let desugar_modul_common curmod env (m:AST.modul) : env_t * Syntax.modul * bool =
  let open_ns (mname:lident) d =
    let d = if List.length mname.ns <> 0
            then (AST.mk_decl (AST.Open (lid_of_ids mname.ns)) (range_of_lid mname))  :: d
            else d in
    d in
  let env = match curmod with
    | None -> env
    | Some(prev_mod) ->  Env.finish_module_or_interface env prev_mod in
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
    is_interface=intf
  } in
  env, modul, pop_when_done

let desugar_partial_modul curmod (env:env_t) (m:AST.modul) : env_t * Syntax.modul =
  let m =
    if !Options.interactive_fsi then
        match m with
            | Module(mname, decls) -> AST.Interface(mname, decls, true)
            | Interface(mname, _, _) -> failwith ("Impossible: " ^ mname.ident.idText)
    else m
  in
  let x, y, _ = desugar_modul_common curmod env m in
  x,y

let desugar_modul env (m:AST.modul) : env_t * Syntax.modul =
  let env, modul, pop_when_done = desugar_modul_common None env m in
  let env = Env.finish_module_or_interface env modul in
  if Options.should_dump modul.name.str 
  then Util.print1 "%s\n" (Print.modul_to_string modul);
  (if pop_when_done then export_interface modul.name env else env), modul

let desugar_file (env:env_t) (f:file) =
  let env, mods = List.fold_left (fun (env, mods) m ->
    let env, m = desugar_modul env m in
    env, m::mods) (env, []) f in
  env, List.rev mods 

let add_modul_to_env (m:Syntax.modul) (en: env) :env =
  let en, pop_when_done = Env.prepare_module_or_interface false false en m.name in
  let en = List.fold_left Env.push_sigelt ({ en with curmodule = Some(m.name) }) m.exports in
  let env = Env.finish_module_or_interface en m in
  if pop_when_done then export_interface m.name env else env
