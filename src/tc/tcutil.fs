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
// (c) Microsoft Corporation. All rights reserved

module Microsoft.FStar.Tc.Util

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Tc.Normalize
open Microsoft.FStar.Tc.Rel

let t_unit = withkind Kind_type <| Typ_const (Util.withsort Const.unit_lid Kind_type)
let t_bool = withkind Kind_type <| Typ_const (Util.withsort Const.bool_lid Kind_type)
let t_int = withkind Kind_type <| Typ_const (Util.withsort Const.int_lid Kind_type)
let t_int64 = withkind Kind_type <| Typ_const (Util.withsort Const.int64_lid Kind_type)
let t_string = withkind Kind_type <| Typ_const (Util.withsort Const.string_lid Kind_type)
let t_float = withkind Kind_type <| Typ_const (Util.withsort Const.float_lid Kind_type)
let t_char = withkind Kind_type <| Typ_const(Util.withsort Const.char_lid Kind_type)

let typing_const env (s:sconst) = match s with 
  | Const_unit -> t_unit
  | Const_bool _ -> t_bool
  | Const_int32 _ -> t_int
  | Const_string _ -> t_string
  | Const_float _ -> t_float
  | Const_char _ -> t_char
  | Const_int64 _ -> t_int64
  | _ -> raise (Error("Unsupported constant", Tc.Env.get_range env))

let push_tparams env tps = 
  List.fold_left (fun env tp -> 
                    let binding = match tp with
                      | Tparam_typ (a, k) -> Binding_typ (a, k) 
                      | Tparam_term (x, t) -> Binding_var (x, t) in
                      push_local_binding env binding) env tps 

let is_xvar_free (x:bvvdef) t = 
  let _, xvs = Util.freevars_typ t in
  Util.for_some (fun (bv:bvvar) -> Util.bvd_eq bv.v x) xvs

let is_tvar_free (a:btvdef) t = 
  let tvs, _ = Util.freevars_typ t in
  Util.for_some (fun (bv:btvar) -> Util.bvd_eq bv.v a) tvs 

let new_kvar env =
  let wf k () =
    let tvs, xvs = Util.freevars_kind k in 
    let tvs', xvs' = Env.idents env in
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    Util.forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
  Kind_uvar (Unionfind.fresh (Uvar wf))
          
let new_tvar env k =
  let rec pre_kind_compat k1 k2 = match compress_kind k1, compress_kind k2 with 
    | _, Kind_uvar uv 
    | Kind_uvar uv, _ -> true
    | Kind_type, Kind_type -> true
    | Kind_tcon(_, k1, k2, _), Kind_tcon(_, k1', k2', _) -> pre_kind_compat k1 k1' && pre_kind_compat k2 k2'
    | Kind_dcon(_, _, k1, _), Kind_dcon(_, _, k1', _) -> pre_kind_compat k1 k1'
    | k1, k2 -> //Util.print_string (Util.format2 "Pre-kind-compat failed on %s and %s\n" (Print.kind_to_string k1) (Print.kind_to_string k2)); 
    false in
  let wf t tk =
    let tvs, xvs = Util.freevars_typ t in 
    let tvs', xvs' = Env.idents env in 
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    let freevars_in_env = Util.forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
    let err () = 
//      Util.print_string (Util.format3 "Failed: Trying to unify uvar of kind %s with type %s of kind %s\n" (Print.kind_to_string k) (Print.typ_to_string t) (Print.kind_to_string tk));
//      Util.print_string (Util.format3 "freevars = %s; %s; %s\n" 
//        (if freevars_in_env then "true" else "false") 
//        (List.map (fun x -> Print.strBvd x.v) tvs |> String.concat ", ")
//        (List.map (fun x -> Print.strBvd x.v) xvs |> String.concat ", "));
      () in
    let result = freevars_in_env && pre_kind_compat k tk in
    if result then result else (err(); result) in
  withkind k <| Typ_uvar (Unionfind.fresh (Uvar wf), k)

let new_evar env t =
  let wf e t = 
    let tvs, xvs = Util.freevars_exp e in
    let tvs', xvs' = Env.idents env in 
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
  Exp_uvar (Unionfind.fresh (Uvar wf), t)

let new_cvar env t = 
  Flex (Unionfind.fresh Floating, t)

let close_guard (b:list<binding>) (g:guard) : guard = match g with 
  | Trivial -> g
  | Guard f -> Guard <|
   List.fold_right (fun b f -> match b with 
      | Env.Binding_var(x, t) -> Util.mk_forall x t f
      | Env.Binding_typ(a, k) -> Util.mk_forallT a k f
      | _ -> failwith "impossible") b f

let check_and_ascribe (env:env) (e:exp) (t1:typ) (t2:typ) : exp * guard =
  match try_subtype env t1 t2 with
    | None -> 
        ignore <| try_subtype env t1 t2;
        if env.is_pattern
        then raise (Error(Tc.Errors.expected_pattern_of_type t2 e t1, Tc.Env.get_range env))
        else raise (Error(Tc.Errors.expected_expression_of_type t2 e t1, Tc.Env.get_range env))
    | Some f -> 
        Exp_ascribed(e, t2), f

let maybe_instantiate env e t = 
  let rec aux norm subst t e = 
    let t = compress_typ t in 
    match t.t with 
      | Typ_univ(_, _, c)
      | Typ_fun(_, _, c, _) when not (Util.is_total_comp c) -> 
        (e, Util.subst_typ subst t)

      | Typ_univ(a, k, c) -> (* is_total_comp *)
        if env.instantiate_targs 
        then 
          let arg = new_tvar env (Util.subst_kind subst k) in
          let subst = Inl(a, arg)::subst in
          let f = Exp_tapp(e, arg) in
          aux norm subst (force_comp c).result_typ f 
        else (e, Util.subst_typ subst t)

      | Typ_fun(xopt, t1, c, b) -> (* is_total_comp *)
        begin match xopt with 
          | Some x when (b && env.instantiate_vargs) -> 
            let arg = new_evar env (Util.subst_typ subst t1) in
            let subst = Inr(x, arg)::subst in 
            let f = Exp_app(e, arg, true) in
            aux norm subst (force_comp c).result_typ f
          | _ -> (e, Util.subst_typ subst t)
        end

      | _ when not norm -> 
        let t' = normalize env t in 
        begin match t'.t with 
          | Typ_fun _
          | Typ_univ _ -> aux true subst t' e
          | _ -> (e, Util.subst_typ subst t')
        end

      | _ -> (e, Util.subst_typ subst t) in
  aux false [] t e

let destruct_function_typ (env:env) (t:typ) (f:option<exp>) (imp_arg_follows:bool) (default_ml:bool) : (typ * option<exp>) = 
  let rec aux norm subst t f =
    let t = compress_typ t in 
    match t.t with 
      | Typ_uvar _ when (not imp_arg_follows) -> 
        let arg = new_tvar env Kind_type in
        let res = new_tvar env Kind_type in 
        let eff = if default_ml then Util.ml_comp res (Env.get_range env) else new_cvar env res in
        let tf = withkind Kind_type <| Typ_fun(None, arg, eff, false) in
        trivial <| teq env t tf;
        (tf, f)

      | Typ_univ(a, k, c) when Util.is_total_comp c -> 
        (* need to instantiate an implicit type argument *)
        let arg = new_tvar env (Util.subst_kind subst k) in
        let subst = Inl(a, arg)::subst in
        let g = match f with 
          | None -> None
          | Some f -> Some <| Exp_tapp(f, arg) in
        aux norm subst (force_comp c).result_typ g 

      | Typ_fun(_, _, _, false) when imp_arg_follows -> 
        (* function type wants an explicit argument, but we have an implicit arg expected *)
        raise (Error (Tc.Errors.unexpected_implicit_argument, Tc.Env.get_range env))
      
      | Typ_fun(Some x, t1, c, imp_t1) when (Util.is_total_comp c && imp_t1 && not imp_arg_follows) ->
        (* need to instantiate an implicit argument *)
        let arg = new_evar env (Util.subst_typ subst t1) in
        let subst = Inr(x, arg)::subst in 
        let g = match f with 
          | None -> None
          | Some f -> Some <| Exp_app(f, arg, true) in
        aux norm subst (force_comp c).result_typ g

      | Typ_fun _ -> 
        (* either, we have an implicit function but with an explicit instantiation following;
           or, we have a function with an explicit argument and no implicit arg following *)
        (Util.subst_typ subst t, f)

      | _ when not norm -> 
        let t = normalize env t in 
        aux true subst t f 

      | _ -> 
        let _ = match f with 
          | Some e -> Util.print_string (Util.format1 "destruct function type failed on expression %s\n" (Print.exp_to_string e))
          | _ -> Util.print_string "Destruct function typ failed, no expression available" in
        raise (Error (Tc.Errors.expected_function_typ (Util.subst_typ subst t), Tc.Env.get_range env)) in
    aux false [] t f

let destruct_poly_typ (env:env) (t:typ) (f:exp) targ : (typ*exp) = 
  let rec aux norm subst t f =
    let t = compress_typ t in 
    match t.t with 
      | Typ_univ _ -> 
        (Util.subst_typ subst t, f)

      | Typ_fun(Some x, t1, c, true) when Util.is_total_comp c ->
        (* need to instantiate an implicit argument *)
        let arg = new_evar env (Util.subst_typ subst t1) in
        let subst = Inr(x, arg)::subst in
        let g = Exp_app(f, arg, true) in
        aux norm subst (force_comp c).result_typ g

      | _ when not norm -> 
        let t = normalize env t in 
        aux true subst t f 

      | _ -> 
        raise (Error (Tc.Errors.expected_poly_typ f (Util.subst_typ subst t) targ, Tc.Env.get_range env)) in
    aux false [] t f

let destruct_tcon_kind env ktop tt imp_arg_follows = 
  let rec aux t k = 
    let k = compress_kind k in 
    match k with 
     | Kind_uvar uv when not imp_arg_follows ->  (* inference never introduces a dependent function *)
          let k' = Kind_tcon(None, new_kvar env, new_kvar env, false) in
          trivial <| keq env None k k';
          k', t
     | Kind_tcon(_, _, _, false) when not imp_arg_follows -> k, t
     | Kind_tcon(_, _, _, true) when imp_arg_follows -> k, t
     | Kind_tcon(Some a, k1, k2, true) -> 
       let targ = new_tvar env k1 in 
       let k2 = Util.subst_kind [Inl(a, targ)] k2 in
       let t' = withkind k2 <| Typ_app(t, targ, true) in
       aux t' k2
     | Kind_dcon(Some x, t1, k1, true) -> 
       let earg = new_evar env t1 in 
       let k1 = Util.subst_kind [Inr(x, earg)] k1 in
       let t' = withkind k1 <| Typ_dep(t, earg, true) in 
       aux t' k1
     | Kind_abbrev(_, k) -> aux t k
     | _ -> raise (Error(Tc.Errors.expected_tcon_kind tt ktop, Tc.Env.get_range env)) in
  aux tt ktop

let destruct_dcon_kind env ktop tt imp_arg_follows =
  let rec aux t k =  
    let k = compress_kind k in 
    match k with 
    | Kind_uvar uv when not imp_arg_follows ->  (* inference never introduces a dependent function *)
        let k' = Kind_dcon(None, new_tvar env Kind_type, new_kvar env, false) in
        trivial <| keq env None k k';
        (k', t)
    | Kind_tcon(aopt, k, k', true) -> 
      let arg = new_tvar env k in
      let kres = match aopt with 
        | None -> k'
        | Some a -> Util.subst_kind [Inl(a, arg)] k' in
      aux (withkind kres <| Typ_app(t, arg, true)) kres
    | Kind_dcon(_, _, _, b) when (b=imp_arg_follows) -> (k, t)
    | Kind_dcon(Some x, t1, k1, true) -> 
      let earg = new_evar env t1 in 
      let k1 = Util.subst_kind [Inr(x, earg)] k1 in
      let t' = withkind k1 <| Typ_dep(t, earg, true) in 
      aux t' k1
    | Kind_abbrev(_, k) -> aux t k
    | _ -> raise (Error(Tc.Errors.expected_dcon_kind tt ktop, Tc.Env.get_range env)) in
  aux tt ktop

let pat_as_exps env p : list<exp> = 
  let single_arg = function 
    | [Inl p] -> Inl p
    | [Inr e] -> Inr (e, false)
    | _ -> failwith "Impossible" in
  let single = function 
    | [te] -> te
    | _ -> failwith "impossible" in
  let rec aux p = match p with
    | Pat_wild ->  [Inr (new_evar env (new_tvar env Kind_type))]
    | Pat_twild  -> [Inl (new_tvar env (new_kvar env))]
    | Pat_var x -> [Inr (Util.bvd_to_exp x (new_tvar env Kind_type))]
    | Pat_tvar a -> [Inl (Util.bvd_to_typ a (new_kvar env))]
    | Pat_constant c -> [Inr (Exp_constant c)]
    | Pat_cons(l, pats) -> 
      let args = List.map (fun p -> single_arg (aux p)) pats in 
      [Inr (Util.mk_data l args)]
    | Pat_disj pats -> 
      pats |> List.map (fun p -> single <| aux p)
    | Pat_withinfo(p, r) -> 
      aux p |> List.map (function 
        | Inr (e) -> Inr (Exp_meta(Meta_info(e, tun, r)))
        | Inl t -> Inl (withkind kun <| Typ_meta(Meta_pos(t, r)))) in
  List.map (function 
    | Inl _ -> failwith "Impossible"
    | Inr (e) -> e) (aux p)    

let generalize env e (c:comp) : (exp * comp) = 
  if not <| Util.is_total_comp c 
  then e, c
  else
     let _ = printfn "Generalizing %s\n" (Print.typ_to_string (Util.comp_result c)) in 
     let print_uvars uvs =
       uvs |> List.iter (fun (uv, _) -> printfn "\t%d" (Unionfind.uvar_id uv)) in
     let t = (force_comp c).result_typ in
     let uvars = Env.uvars_in_env env in
     printfn "Uvars in env:"; print_uvars uvars.uvars_t;
     let uvars_t = (Util.uvars_in_typ t).uvars_t in
     printfn "Uvars in type:"; print_uvars uvars_t;
     let generalizable = uvars_t |> List.filter (fun (uv,_) -> not (uvars.uvars_t |> Util.for_some (fun (uv',_) -> Unionfind.equivalent uv uv'))) in 
     let tvars = generalizable |> List.map (fun (u,k) -> 
      let a = Util.new_bvd (Some <| Tc.Env.get_range env) in
      let t = Util.bvd_to_typ a k in
      unchecked_unify u t;
      (a,k)) in
    let e, t = tvars |> List.fold_left (fun (e,t) (a,k) ->
      let t' = withkind Kind_type <| Typ_univ(a, k, Util.total_comp t (Env.get_range env)) in
      let e' = Exp_tabs(a, k, e) in
      (e', t')) (e,t) in
    e, Util.total_comp t (Env.get_range env)

let mk_basic_tuple_type env n = 
  let r = Tc.Env.get_range env in
  let l = Util.mk_tuple_lid n in
  let k = Tc.Env.lookup_typ_lid env l in
  let t = withkind k <| Typ_const(withinfo l k r) in
  let rec close t ktop = match ktop with 
    | Kind_dcon(Some x, tx, k, _) -> 
      let cod = close t k in
      withkind ktop <| Typ_lam(x, tx, close t k)
    | Kind_dcon(None, tx, k, _) -> 
      withkind ktop <| Typ_lam(Util.new_bvd (Some r), tx, close t k)
    | Kind_tcon(Some a, k1, k, _) -> 
      withkind ktop <| Typ_tlam(a, k1, close t k)
    | Kind_tcon(None, k1, k, _) -> 
      withkind ktop <| Typ_tlam(Util.new_bvd (Some r), k1, close t k)
    | _ -> t in 
  let rec build t k = match k with 
    | Kind_tcon(Some a, ka, k, _) ->
      let u = new_tvar env Kind_type in 
      let arg = close u ka in
      let kk = Util.subst_kind [Inl(a, arg)] k in
      build (withkind kk <| Typ_app(t, arg, false))  kk
    | _ -> t in
  build t k

let extract_lb_annotation env t e = match t.t with 
  | Typ_unknown -> 
    let mk_kind env = function 
      | Kind_unknown -> new_kvar env
      | k -> k in
    let mk_typ env t = match t.t with 
      | Typ_unknown -> new_tvar env Kind_type
      | _ -> t in
    let rec aux env e = match e with 
      | Exp_meta(Meta_info(e, _, _)) 
      | Exp_meta(Meta_desugared(e, _)) -> aux env e 
      | Exp_tabs(a, k, e) -> 
        let k = mk_kind env k in
        let env = Env.push_local_binding env (Binding_typ(a, k)) in
        withkind Kind_type <| Typ_univ(a, k, aux_comp env e)
      | Exp_abs(x, t, e) -> 
        let t = mk_typ env t in
        let env = Env.push_local_binding env (Binding_var(x, t)) in
        withkind Kind_type <| Typ_fun(Some x, t, aux_comp env e, false)
      | Exp_ascribed(e, t) -> t
      | _ -> new_tvar env Kind_type 
    and aux_comp env e = match e with 
      | Exp_meta(Meta_info(e, _, _))
      | Exp_meta(Meta_desugared(e, _)) -> aux_comp env e
      | Exp_tabs _
      | Exp_abs _ -> Util.total_comp (aux env e) (Env.get_range env)
      | Exp_ascribed(e, t) -> 
        let c = aux_comp env e in
        begin match compress_comp c with 
          | Comp ct -> Comp ({ct with result_typ=t})
          | Flex (u, t0) -> 
            Rel.trivial <| Rel.teq env t t0;
            Flex (u, t)
        end
      | _ -> new_cvar env (new_tvar env Kind_type) in
    aux env e       
  | _ -> t

(*********************************************************************************************)
(* Utils related to monadic computations *)
(*********************************************************************************************)
type comp_with_binder = option<Env.binding> * comp

let destruct_comp c : (typ * typ * typ) = 
  let wp, wlp = match c.effect_args with 
    | [Inl wp; Inl wlp] -> wp, wlp
    | _ -> failwith (Printf.sprintf "Impossible: Got a computation %s with effect args %s" c.effect_name.str 
      (String.concat ";" <| List.map Print.either_to_string c.effect_args)) in
  c.result_typ, wp, wlp

let lift_comp c m lift =
  let res, wp, wlp = destruct_comp c in
  {effect_name=m;
   result_typ=c.result_typ;
   effect_args=[Inl (lift c.result_typ wp); Inl (lift c.result_typ wlp)]}

let lift_and_destruct env c1 c2 = 
  let c1 = Tc.Normalize.weak_norm_comp env c1 in
  let c2 = Tc.Normalize.weak_norm_comp env c2 in 
  let m, lift1, lift2 = Tc.Env.join env c1.effect_name c2.effect_name in
  let m1 = lift_comp c1 m lift1 in
  let m2 = lift_comp c2 m lift2 in
  let md = Tc.Env.monad_decl env m in
  let a, kwp = Tc.Env.wp_signature env md.mname in
  (md, a, kwp), (destruct_comp m1), destruct_comp m2

let mk_comp md result wp wlp = 
  Comp ({effect_name=md.mname;
         result_typ=result;
         effect_args=[Inl wp; Inl wlp]})

let bind env (c1:comp) ((b, c2):comp_with_binder) : comp = 
  if Util.is_total_comp c1 && Util.is_total_comp c2
  then c2
  else if Util.is_ml_comp c2
  then c2
  else
    let (md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2) = lift_and_destruct env c1 c2 in 
    let mk_lam wp = match b with 
      | None -> withkind (Kind_dcon(None, t1, wp.k, false)) <| Typ_lam(Util.new_bvd None, t1, wp) 
      | Some (Env.Binding_var(x, t)) -> withkind (Kind_dcon(Some x, t, wp.k, false)) <| Typ_lam(x, t, wp)
      | Some (Env.Binding_lid(l, t)) -> withkind (Kind_dcon(None, t, wp.k, false)) <| Typ_lam(Util.new_bvd None, t, wp)
      | Some _ -> failwith "Unexpected type-variable binding" in
    let args = [Inl t1; Inl t2; Inl wp1; Inl wlp1; Inl (mk_lam wp2); Inl (mk_lam wlp2)] in
    let k = Util.subst_kind [Inl(a, t2)] kwp in
    let wp = {Util.mk_typ_app md.bind_wp args with k=k} in
    let wlp = {Util.mk_typ_app md.bind_wlp args with k=k} in 
    mk_comp md t2 wp wlp

let bind_ite env (cond:typ) (c1:comp) (c2:comp) : comp = 
  let (md, a, kwp), (t, wp1, wlp1), (_, wp2, wlp2) = lift_and_destruct env c1 c2 in 
  let k = Util.subst_kind [Inl(a, t)] kwp in
  let wlp = {Util.mk_typ_app md.ite_wlp [Inl t; Inl cond; Inl wlp1; Inl wlp2] with k=k} in
  let wp = {Util.mk_typ_app md.ite_wp [Inl t; Inl cond; Inl wp1; Inl wlp1; Inl wp2; Inl wlp2] with k=k} in
  mk_comp md t wp wlp

let lift_formula t wp wlp env f = 
  let md_pure = Tc.Env.monad_decl env Const.pure_effect_lid in
  let a, kwp = Tc.Env.wp_signature env md_pure.mname in 
  let k = Util.subst_kind [Inl(a, t)] kwp in
  let wp = {Util.mk_typ_app wp [Inl t; Inl f] with k=k} in
  let wlp = {Util.mk_typ_app wlp [Inl t; Inl f] with k=k} in
  mk_comp md_pure t_unit wp wlp 

let lift_assertion env f =
  let assert_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assert_pure_lid in
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula assert_pure assume_pure t_unit env f

let lift_assumption env f =
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assert_pure_lid in
  lift_formula assume_pure assume_pure t_unit env f

let lift_pure env f = 
  let t = new_tvar env Kind_type in 
  let assert_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assert_pure_lid in
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula assert_pure assume_pure t env f

let strengthen_precondition env c f = match f with 
  | Trivial -> c
  | Guard f -> bind env (lift_assertion env f) (None, c)

let weaken_precondition env c f = match f with 
  | Trivial -> c
  | Guard f -> bind env (lift_assumption env f) (None, c)

let close_comp env bindings (c:comp) = 
  let close_wp md res_t bindings wp0 =  
    List.fold_right (fun b wp -> match b with 
      | Env.Binding_var(x, t) -> 
        let wp = withkind (Kind_dcon(None, t, wp0.k, false)) <| Typ_lam(x, t, wp) in
        {Util.mk_typ_app md.close_wp [Inl res_t; Inl t; Inl wp] with k=wp0.k}
      | Env.Binding_typ(a, k) -> //A bit sloppy here: close_wp_t is only for Type; overloading it here for all kinds
        let wp = withkind (Kind_tcon(None, k, wp0.k, false)) <| Typ_tlam(a, k, wp) in
        {Util.mk_typ_app md.close_wp_t [Inl res_t; Inl wp] with k=wp0.k}
      | Env.Binding_lid(l, t) -> 
        (* TODO: replace every occurrence of l in wp with a fresh bound var, abstract over the bound var and then close it.
                 Except that it is highly unlikely for the wp to actually contain such a free occurrence of l *)
        wp
      | Env.Binding_sig s -> failwith "impos") bindings wp0 in //(Printf.sprintf "NYI close_comp_typ with binding %A" b)) 
  let c = Tc.Normalize.weak_norm_comp env c in
  let t, wp, wlp = destruct_comp c in
  let md = Tc.Env.monad_decl env c.effect_name in
  let wp = close_wp md c.result_typ bindings wp in
  let wlp = close_wp md c.result_typ bindings wlp in
  mk_comp md c.result_typ wp wlp

let weaken_result_typ (env:env)  (e:exp) (c:comp) (t:typ) : exp * comp = 
  let c = Tc.Normalize.weak_norm_comp env c in
  let tc, wp, wlp = destruct_comp c in
  let g = Tc.Rel.subtype env tc t in
  let md = Tc.Env.monad_decl env c.effect_name in
  let c = strengthen_precondition env (mk_comp md tc wp wlp) g in
  e, c

let check_comp (env:env) (e:exp) (c:comp) (c':comp) : exp * comp * guard = 
  match Tc.Rel.sub_comp env c c' with 
    | None -> raise (Error(Tc.Errors.computed_computation_type_does_not_match_annotation e c c', Tc.Env.get_range env))
    | Some g -> e, c', g