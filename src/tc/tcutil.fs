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
let t_uint8 = withkind Kind_type <| Typ_const (Util.withsort Const.uint8_lid Kind_type)
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
  | Const_uint8 _ -> t_char
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

let eq_bv_bvd bv bvd = Util.bvd_eq bv.v bvd
  
let new_kvar env =
  let wf k () =
    let tvs, xvs = Util.freevars_kind k in 
    let tvs', xvs' = Env.idents env in
    Util.forall_exists eq_bv_bvd tvs tvs' && Util.forall_exists eq_bv_bvd xvs xvs' in
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
    let freevars_in_env = Util.forall_exists eq_bv_bvd tvs tvs' && Util.forall_exists eq_bv_bvd xvs xvs' in
    let err () = 
      if debug env 
      then begin
        Options.fvdie := true;
        Util.print_string (Util.format3 "Failed: Trying to unify uvar of kind %s with type %s of kind %s\n" (Print.kind_to_string k) (Print.typ_to_string t) (Print.kind_to_string tk));
        Util.print_string (Util.format3 "freevars = %s; %s; %s\n" 
          (if freevars_in_env then "true" else "false") 
          (List.map (fun x -> Util.format2 "%s@%s" (Print.strBvd x.v) (Range.string_of_range (range_of_bvd x.v))) tvs |> String.concat ", ")
          (List.map (fun x -> Print.strBvd x.v) xvs |> String.concat ", "))
        //        printfn "%A" t
      end in
    let result = freevars_in_env && pre_kind_compat k tk in
    if result then result else (err(); result) in
  withkind k <| Typ_uvar (Unionfind.fresh (Uvar wf), k)

let new_evar env t =
  let wf e t = 
    let tvs, xvs = Util.freevars_exp e in
    let tvs', xvs' = Env.idents env in 
    forall_exists eq_bv_bvd tvs tvs' && Util.forall_exists eq_bv_bvd xvs xvs' in
  Exp_uvar (Unionfind.fresh (Uvar wf), t)

let new_cvar env t = 
  Flex (Unionfind.fresh Floating, t)

let close_guard (b:list<binding>) (g:guard) : guard = match g with 
  | Trivial -> g
  | NonTrivial f -> NonTrivial <|
   List.fold_right (fun b f -> match b with 
      | Env.Binding_var(x, t) -> Util.mk_forall x t f
      | Env.Binding_typ(a, k) -> Util.mk_forallT a k f
      | _ -> failwith "impossible") b f

let apply_guard g e = match g with 
    | Trivial -> g
    | NonTrivial f -> NonTrivial (withkind Kind_type <| Typ_dep(f, e, false))

let check_and_ascribe env (e:exp) (t1:typ) (t2:typ) : exp * guard =
  match try_subtype env t1 t2 with
    | None -> 
        if env.is_pattern
        then raise (Error(Tc.Errors.expected_pattern_of_type t2 e t1, Tc.Env.get_range env))
        else raise (Error(Tc.Errors.expected_expression_of_type t2 e t1, Tc.Env.get_range env))
    | Some f -> 
        Exp_ascribed(e, t2), apply_guard f e

let new_function_typ env (x:bvvdef) = 
    let arg = new_tvar env Kind_type in
    let res = new_tvar env Kind_type in 
    let eff = new_cvar env res in
    withkind Kind_type <| Typ_fun(Some x, arg, eff, false) 

let new_poly_typ env (a:btvdef) = 
    let arg = new_kvar env in
    let res = new_tvar (Tc.Env.push_local_binding env (Tc.Env.Binding_typ(a, arg))) Kind_type in 
    let eff = new_cvar env res in
    withkind Kind_type <| Typ_univ(a, arg, eff) 
  
let uvar_as_function_typ env (topt:option<typ>) (x:bvvdef) = 
    let tf = new_function_typ env x in
    match topt with 
      | Some t -> 
        trivial <| teq env t tf; //forces a unification
        tf
      | _ -> tf

let destruct_function_typ env (t:typ) (xopt:option<bvvdef>) (f:option<exp>) (imp_arg_follows:bool) (default_effect:option<lident>) : (typ * option<exp>) = 
  let fail subst t f = 
    let _ = match f with 
      | Some e -> Util.print_string (Util.format1 "destruct function type failed on expression %s\n" (Print.exp_to_string e))
      | _ -> Util.print_string "Destruct function typ failed, no expression available" in
    raise (Error (Tc.Errors.expected_function_typ (Util.subst_typ subst t), Tc.Env.get_range env)) in
  let rec aux xopt norm subst t f =
    let t = compress_typ t in 
    match t.t with 
      | Typ_uvar _ when (not imp_arg_follows) -> 
        let arg = new_tvar env Kind_type in
        let res = new_tvar env Kind_type in 
        let eff, xopt = match default_effect with 
            | None -> new_cvar env res, xopt
            | Some l -> 
                if lid_equals l Const.ml_effect_lid
                then Util.ml_comp res (Env.get_range env), None 
                else if lid_equals l Const.tot_effect_lid 
                then Total res, None
                else new_cvar env res, xopt in
        let tf = withkind Kind_type <| Typ_fun(xopt, arg, eff, false) in
        trivial <| teq env t tf;
        (tf, f)

      | Typ_univ(a, k, c) -> 
        if Util.is_total_comp c 
        then          (* need to instantiate an implicit type argument *)
            let arg = new_tvar env (Util.subst_kind subst k) in
            let subst = Inl(a, arg)::subst in
            let g = match f with 
              | None -> None
              | Some f -> Some <| Exp_tapp(f, arg) in
            aux None norm subst (force_comp c).result_typ g 
        else if not norm 
        then let t = normalize env t in 
             aux xopt true subst t f 
        else fail subst t f

      | Typ_fun(_, _, _, false) when imp_arg_follows -> 
        (* function type wants an explicit argument, but we have an implicit arg expected *)
        raise (Error (Tc.Errors.unexpected_implicit_argument, Tc.Env.get_range env))
      
      | Typ_fun(xopt, t1, c, imp_t1) ->
        if Util.is_some xopt && Util.is_total_comp c && imp_t1 && not imp_arg_follows
        then (* need to instantiate an implicit argument *)
            let x = must xopt in
            let arg = new_evar env (Util.subst_typ subst t1) in
            let subst = Inr(x, arg)::subst in 
            let g = match f with 
              | None -> None
              | Some f -> Some <| Exp_app(f, arg, true) in
            aux None norm subst (force_comp c).result_typ g
        else (* either, we have an implicit function but with an explicit instantiation following;
               or, we have a function with an explicit argument and no implicit arg following *)
            (Util.compress_typ <| Util.subst_typ subst t, f)

      | _ when not norm -> 
        let t = normalize env t in 
        aux xopt true subst t f 

      | _ -> fail subst t f in
    aux xopt false [] t f

let destruct_poly_typ env (t:typ) (f:exp) targ : (typ*exp) = 
  let fail subst t f = 
    raise (Error (Tc.Errors.expected_poly_typ f (Util.subst_typ subst t) targ, Tc.Env.get_range env)) in
  let rec aux norm subst t f =
    let t = compress_typ t in 
    match t.t with 
      | Typ_univ _ -> 
        (Util.subst_typ subst t, f)

      | Typ_fun(Some x, t1, c, true) -> 
        if Util.is_total_comp c
        then (* need to instantiate an implicit argument *)
            let arg = new_evar env (Util.subst_typ subst t1) in
            let subst = Inr(x, arg)::subst in
            let g = Exp_app(f, arg, true) in
            aux norm subst (force_comp c).result_typ g
        else fail subst t f

      | _ when not norm -> 
        let t = normalize env t in 
        aux true subst t f 

      | _ -> fail subst t f in
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

let mk_basic_dtuple_type env n = 
  let r = Tc.Env.get_range env in
  let l = Util.mk_dtuple_lid n r in
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

let extract_lb_annotation is_rec env t e = match t.t with 
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
          | Total _ -> Total t
          | Flex (u, _) -> Flex(u, t)
        end
      | _ ->
        if is_rec then Util.ml_comp (new_tvar env Kind_type) (Env.get_range env)
        else new_cvar env (new_tvar env Kind_type) in
    aux env e       
  | _ -> t

(*********************************************************************************************)
(* Utils related to monadic computations *)
(*********************************************************************************************)
type comp_with_binder = option<Env.binding> * comp

let destruct_comp c : (typ * typ * typ) = 
  let wp, wlp = match c.effect_args with 
    | [Inl wp; Inl wlp] -> wp, wlp
    | _ -> failwith (Util.format2 "Impossible: Got a computation %s with effect args %s" c.effect_name.str 
      (String.concat ";" <| List.map Print.either_to_string c.effect_args)) in
  c.result_typ, wp, wlp

let lift_comp c m lift =
  let res, wp, wlp = destruct_comp c in
  {effect_name=m;
   result_typ=c.result_typ;
   effect_args=[Inl (lift c.result_typ wp); Inl (lift c.result_typ wlp)]; 
   flags=[]}

let lift_and_destruct env c1 c2 = 
  let c1 = Tc.Normalize.weak_norm_comp env c1 in
  let c2 = Tc.Normalize.weak_norm_comp env c2 in 
  let m, lift1, lift2 = Tc.Env.join env c1.effect_name c2.effect_name in
  let m1 = lift_comp c1 m lift1 in
  let m2 = lift_comp c2 m lift2 in
  let md = Tc.Env.get_monad_decl env m in
  let a, kwp = Tc.Env.wp_signature env md.mname in
  (md, a, kwp), (destruct_comp m1), destruct_comp m2

let force_total c = match compress_comp c with 
    | Total t -> Some t
    | Flex(u, t) -> 
        let tot = Total t in
        Unionfind.change u (Resolved tot);
        Some t
    | Comp c -> 
        if Util.is_pure_comp (Comp c )
        then Some c.result_typ
        else None 

let is_pure env c = 
  let c = Tc.Normalize.weak_norm_comp env c in
  lid_equals c.effect_name Const.pure_effect_lid

let mk_comp md result wp wlp flags = 
  Comp ({effect_name=md.mname;
         result_typ=result;
         effect_args=[Inl wp; Inl wlp];
         flags=flags})

//let return_value env t v = Util.total_comp t (range_of_exp v (Env.get_range env))

let return_value env t v = 
  match Tc.Env.monad_decl_opt env Const.pure_effect_lid with 
    | None -> Util.total_comp t (range_of_exp v (Env.get_range env))
    | Some m -> 
       let a, kwp = Env.wp_signature env Const.pure_effect_lid in
       let k = Util.subst_kind [Inl(a, t)] kwp in
       let wp = {Util.mk_typ_app m.ret [Inl t; Inr v] with k=k} in
       let wlp = wp in
       mk_comp m t wp wlp [RETURN]

let bind env (c1:comp) ((b, c2):comp_with_binder) : comp = 
//  if debug env
//  then 
//    (let bstr = match b with 
//      | None -> "none"
//      | Some (Env.Binding_var(x, _)) -> Print.strBvd x
//      | _ -> "??" in
//    printfn "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s" (Print.comp_typ_to_string c1) bstr (Print.comp_typ_to_string c2));
  let try_simplify () = 
    if Util.is_trivial_wp c1
    then match b with 
         | None -> Some c2 
         | Some (Env.Binding_lid _) -> Some c2
         | Some (Env.Binding_var(x, _)) -> 
           if Util.is_ml_comp c2 //|| not (Util.is_free [Inr x] (Util.freevars_comp c2))
           then Some c2
           else None
         | _ -> None
    else if Util.is_ml_comp c1 && Util.is_ml_comp c2 then Some c2
    else None in
  match try_simplify () with 
    | Some c -> c
    | None -> 
      let (md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2) = lift_and_destruct env c1 c2 in 
      let mk_lam wp = match b with 
        | None -> withkind (Kind_dcon(None, t1, wp.k, false)) <| Typ_lam(Util.new_bvd None, t1, wp) 
        | Some (Env.Binding_var(x, t)) -> withkind (Kind_dcon(Some x, t, wp.k, false)) <| Typ_lam(x, t, wp)
        | Some (Env.Binding_lid(l, t)) -> withkind (Kind_dcon(None, t, wp.k, false)) <| Typ_lam(Util.new_bvd None, t, wp)
        | Some _ -> failwith "Unexpected type-variable binding" in
      let wp_args = [Inl t1; Inl t2; Inl wp1; Inl wlp1; Inl (mk_lam wp2); Inl (mk_lam wlp2)] in
      let wlp_args = [Inl t1; Inl t2; Inl wlp1; Inl (mk_lam wlp2)] in
//      if debug env
//      then printfn "Making bind c1=%s\nc2=%s\nlifted to %s\n" (Print.comp_typ_to_string c1) (Print.comp_typ_to_string c2) (md.mname.str);
      let k = Util.subst_kind [Inl(a, t2)] kwp in
      let wp = {Util.mk_typ_app md.bind_wp wp_args with k=k} in
      let wlp = {Util.mk_typ_app md.bind_wlp wlp_args with k=k} in 
      let c = mk_comp md t2 wp wlp [] in
//      if debug env then printfn "Result comp type is %s\n" (Print.comp_typ_to_string c);
//      if debug env then printfn "Normalized comp type is %s\n" (Print.comp_typ_to_string (Comp <| Normalize.normalize_comp env c));
      c
     
let lift_formula env t mk_wp mk_wlp f = 
  let md_pure = Tc.Env.get_monad_decl env Const.pure_effect_lid in
  let a, kwp = Tc.Env.wp_signature env md_pure.mname in 
  let k = Util.subst_kind [Inl(a, t)] kwp in
  let wp = {Util.mk_typ_app mk_wp [Inl t; Inl f] with k=k} in
  let wlp = {Util.mk_typ_app mk_wlp [Inl t; Inl f] with k=k} in
  mk_comp md_pure t_unit wp wlp []

let lift_assertion env f =
  let assert_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assert_pure_lid in
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula env t_unit assert_pure assume_pure f

let lift_assumption env f =
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula env t_unit assume_pure assume_pure f

let lift_pure env t f = 
  let assert_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assert_pure_lid in
  let assume_pure = must <| Tc.Env.lookup_typ_abbrev env Const.assume_pure_lid in
  lift_formula env t assert_pure assume_pure f

let strengthen_precondition env (c:comp) f = match f with 
  | Trivial -> c
  | NonTrivial f -> 
    let tt = Util.compress_typ (Util.comp_result c) in
    let c = Tc.Normalize.weak_norm_comp env c in
//    check_sharing tt (Util.compress_typ <| c.result_typ) "strengthen_precondition 1";
    let res_t, wp, wlp = destruct_comp c in
//    check_sharing tt (Util.compress_typ res_t) "strengthen_precondition 2";
    let md = Tc.Env.get_monad_decl env c.effect_name in 
    let wp = Util.mk_typ_app md.assert_p [Inl res_t; Inl f; Inl wp] in
    let wlp = Util.mk_typ_app md.assume_p [Inl res_t; Inl f; Inl wlp] in
    let c2 = mk_comp md res_t wp wlp [] in
//    check_sharing tt (Util.compress_typ (Util.comp_result c2)) "strengthen_precondition 3";
    c2

let weaken_precondition env c f = match f with 
  | Trivial -> c
  | NonTrivial f -> 
    if Util.is_ml_comp c then c
    else
      let c = Tc.Normalize.weak_norm_comp env c in
      let res_t, wp, wlp = destruct_comp c in
      let md = Tc.Env.get_monad_decl env c.effect_name in 
      let wp = Util.mk_typ_app md.assume_p [Inl res_t; Inl f; Inl wp] in
      let wlp = Util.mk_typ_app md.assume_p [Inl res_t; Inl f; Inl wlp] in
      mk_comp md res_t wp wlp c.flags

let bind_cases env (res_t:typ) (cases:list<(option<formula> * comp)>) : comp =
  (if List.length cases = 0 then failwith "Empty cases!"); (* TODO: Fix precedence of semi colon *)
  match cases with 
    | [(None, c)] -> c
    | [(Some f, c)] -> strengthen_precondition env c (NonTrivial f)
    | _ -> 
      let caccum, some_pat_matched = cases |> List.fold_left (fun (caccum, prior_pat_matched) (gopt, c) -> 
        let prior_or_c_matched, cguard = match prior_pat_matched, gopt with 
          | None, Some g -> Some g, Some g
          | Some g, None -> prior_pat_matched, Some <| Util.mk_neg g
          | Some g, Some g' -> Some (Util.mk_disj g g'), Some <| Util.mk_conj (Util.mk_neg g) g'
          | None, None -> None, None in
        let c = match cguard with 
          | None -> c
          | Some g -> weaken_precondition env c (NonTrivial g) in 
        match caccum with 
          | None -> (Some c, prior_or_c_matched)
          | Some caccum -> 
            let (md, a, kwp), (t, wp1, wlp1), (_, wp2, wlp2) = lift_and_destruct env caccum c in 
            let k = Util.subst_kind [Inl(a, t)] kwp in
            let wp_conj wp1 wp2 = 
              {Util.mk_typ_app md.wp_binop [Inl t; Inl wp1; Inl (Util.ftv Const.and_lid); Inl wp2] with k=k} in
            let wp = wp_conj wp1 wp2 in
            let wlp = wp_conj wlp1 wlp2 in 
            (Some <| mk_comp md t wp wlp [], prior_or_c_matched)) (None, None) in
      let caccum = force_comp (must <| caccum) in
      let md = Tc.Env.get_monad_decl env caccum.effect_name in
      let res_t, wp, wlp = destruct_comp caccum in
      let wp = match some_pat_matched with 
        | None -> wp 
        | Some guard -> Util.mk_typ_app md.assert_p [Inl res_t; Inl guard; Inl wp] in
      let a, kwp = Tc.Env.wp_signature env caccum.effect_name in
      let k = Util.subst_kind [Inl(a, res_t)] kwp in
      let wp = {Util.mk_typ_app md.ite_wp [Inl res_t; Inl wlp; Inl wp] with k=k} in
      let wlp = {Util.mk_typ_app md.ite_wlp [Inl res_t; Inl wlp] with k=k} in
      //Comp <| Normalize.normalize_comp env (
      mk_comp md res_t wp wlp []

let close_comp env bindings (c:comp) = 
  if Util.is_ml_comp c then c
  else
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
    let md = Tc.Env.get_monad_decl env c.effect_name in
    let wp = close_wp md c.result_typ bindings wp in
    let wlp = close_wp md c.result_typ bindings wlp in
    mk_comp md c.result_typ wp wlp c.flags

let weaken_result_typ env (e:exp) (c:comp) (t:typ) : exp * comp = 
  let c = Tc.Normalize.weak_norm_comp env c in
  let tc, _, _ = destruct_comp c in
  let g = Tc.Rel.subtype env tc t in
  match g with 
    | Trivial -> e, Comp c
    | NonTrivial f -> 
      let md = Tc.Env.get_monad_decl env c.effect_name in
      let x = new_bvd None in
      let xexp = Util.bvd_to_exp x t in
      let wp = Util.mk_typ_app md.ret [Inl t; Inr xexp] in
      let cret = mk_comp md t wp wp c.flags in
      let eq_ret = strengthen_precondition env cret (NonTrivial (Util.mk_typ_app f [Inr xexp])) in
      let c = bind env (Comp c) (Some(Env.Binding_var(x, tc)), eq_ret) in
      e, c

let check_comp env (e:exp) (c:comp) (c':comp) : exp * comp * guard = 
  match Tc.Rel.sub_comp env c c' with 
    | None -> raise (Error(Tc.Errors.computed_computation_type_does_not_match_annotation e c c', Tc.Env.get_range env))
    | Some g -> e, c', g

let maybe_assume_result_eq_pure_term env (e:exp) (c:comp) : comp = 
  if not (is_pure env c) then c
  else let c = Tc.Normalize.weak_norm_comp env c in
       let t = c.result_typ in
       let c = Comp c in 
       let x = Util.new_bvd None in
       let xexp = Util.bvd_to_exp x t in
       let ret = return_value env t xexp in
       let eq_ret = weaken_precondition env ret (NonTrivial (Util.mk_eq xexp e)) in
       bind env c (Some (Env.Binding_var(x, t)), eq_ret)

let refine_data_type env l (args:list<either<(btvdef*knd), (option<bvvdef> * typ * bool)>>) (result_t:typ) =
  let rec aux args = function 
    | Inl(a,k)::rest  ->
      let args = Inl (Util.bvd_to_typ a k)::args in
      withkind Kind_type <| Typ_univ(a, k, aux_comp args rest)
    | Inr(xopt,t,imp)::rest -> 
      let x = match xopt with 
        | None -> Util.new_bvd None 
        | Some x -> x in
      let args = Inr (Util.bvd_to_exp x t, imp)::args in
      withkind Kind_type <| Typ_fun(Some x, t, aux_comp args rest, imp)
    | [] -> result_t
  and aux_comp args = function 
    | [] -> 
      let v = Util.mk_curried_app (Util.fvar l (range_of_lid l)) (List.rev args) in
      return_value env result_t v
    | rest -> Util.total_comp (aux args rest) (range_of_lid l) in
  aux [] args

let maybe_instantiate env e t = 
  let rec aux norm subst t e = 
    let ret subst t = match subst with 
      | [] -> e, return_value env t e
      | _ -> e, Util.subst_comp subst (Total t) in
    let t = compress_typ t in 
    match t.t with 
      | Typ_univ(a, k, c) -> 
        if env.instantiate_targs 
        then 
          let arg = new_tvar env (Util.subst_kind subst k) in
          let subst = Inl(a, arg)::subst in
          let f = Exp_tapp(e, arg) in
          if Util.is_total_comp c
          then aux norm subst (Util.comp_result c) f 
          else (f, Util.subst_comp subst c)
        else (e, Util.subst_comp subst (Total t))

      | Typ_fun(xopt, t1, c, b) -> (* is_total_comp *)
        begin match xopt with 
          | Some x when (b && env.instantiate_vargs) -> 
            let arg = new_evar env (Util.subst_typ subst t1) in
            let subst = Inr(x, arg)::subst in 
            let f = Exp_app(e, arg, true) in
            if Util.is_total_comp c
            then aux norm subst (Util.comp_result c) f
            else (f, Util.subst_comp subst c)
          | _ -> (e, Util.subst_comp subst (Total t))
        end

      | _ when not norm -> 
        let t' = normalize env t in 
        begin match t'.t with 
          | Typ_fun _
          | Typ_univ _ -> aux true subst t' e
          | _ -> ret subst t
        end

      | _ -> ret subst t in
  aux false [] t e


(**************************************************************************************)
(* Generalizing types ... the spot where we call the solver *)
(**************************************************************************************)
let check_uvars r t = 
  let uvt = Util.uvars_in_typ t in
  if List.length uvt.uvars_e + List.length uvt.uvars_t + List.length uvt.uvars_k > 0
  then Tc.Errors.report r "Unconstrained unification variables; please add an annotation"

let discharge_guard env g = 
    if not (!Options.verify) then ()
    else match g with 
        | Trivial -> ()
        | NonTrivial vc -> 
            let vc = Normalize.norm_typ [Normalize.Delta; Normalize.Beta] env vc in
             if Tc.Env.debug env then Tc.Errors.diag (Tc.Env.get_range env) (Util.format1 "Checking VC=\n%s\n" (Print.formula_to_string vc));
            if not <| env.solver.solve env vc
            then Tc.Errors.report (Tc.Env.get_range env) (Tc.Errors.failed_to_prove_specification [])
   
let generalize env (ecs:list<(lbname*exp*comp)>) : (list<(lbname*exp*comp)>) = 
//  let _ = printfn "Generalizing %s\n" (Print.typ_to_string (Util.comp_result c)) in
//  let _ = printfn "In normal form %s\n" (Print.typ_to_string (Normalize.norm_typ  [Normalize.Beta; Normalize.Delta; Normalize.SNComp; Normalize.DeltaComp] env (Util.comp_result c))) in 
//     let print_uvars uvs =
//       uvs |> List.iter (fun (uv, _) -> printfn "\t%d" (Unionfind.uvar_id uv)) in
  if not <| (Util.for_all (fun (_, _, c) -> Util.is_pure_comp c) ecs)
  then ecs
  else
     let norm c = 
        if !Options.verify
        then Normalize.normalize_comp env c
        else Normalize.norm_comp [Normalize.Beta; Normalize.Delta] env c in
     let env_uvars = Env.uvars_in_env env in
     let gen_uvars uvs = 
       uvs |> List.filter (fun (uv,_) -> not (env_uvars.uvars_t |> Util.for_some (fun (uv',_) -> Unionfind.equivalent uv uv'))) in 
     let uvars = ecs |> List.map (fun (x, e, c) -> 
      let t = Util.comp_result c in 
      match Util.compress_typ t with 
        | {t=Typ_univ _} -> (* explicit abstractions need not be generalized *)
          (x, [], e, Util.force_comp c)
        | _ -> 
      let c = norm c in //Util.force_comp c in
      let t = c.result_typ in
      let uvt = Util.uvars_in_typ t in
      let uvs = gen_uvars <| uvt.uvars_t in 
      if !Options.verify && not <| Util.is_total_comp (Comp c)
      then begin
          let _, wp, _ = destruct_comp c in //(norm (Comp c)) in
          let post = withkind (Kind_dcon(None, t, Kind_type, false)) <| Typ_lam(Util.new_bvd None, t, Util.ftv Const.true_lid) in
          let vc = Normalize.norm_typ [Normalize.Delta; Normalize.Beta] env (withkind Kind_type <| Typ_app(wp, post, false)) in
          if Tc.Env.debug env then Tc.Errors.diag (range_of_lbname x) (Util.format2  "Checking %s with VC=\n%s\n" (Print.lbname_to_string x) (Print.formula_to_string vc));
          if not <| env.solver.solve env vc
          then Tc.Errors.report (range_of_lbname x) (Tc.Errors.failed_to_prove_specification_of x [])
      end;
      x, uvs, e, Util.force_comp <| return_value env t e) in

     let ecs = uvars |> List.map (fun (x, uvs, e, c) -> 
      let tvars = uvs |> List.map (fun (u, k) -> 
        let a = match Unionfind.find u with 
          | Fixed ({t=Typ_btvar a}) -> a.v 
          | _ -> 
              let a = Util.new_bvd (Some <| Tc.Env.get_range env) in
              let t = Util.bvd_to_typ a k in
//              let _ = printfn "Unifying %d with %s\n" (Unionfind.uvar_id u) (Print.typ_to_string t) in
              unchecked_unify u t; a in
        (a, k)) in
      let e, t = tvars |> List.fold_left (fun (e,t) (a,k) ->
        let t' = withkind Kind_type <| Typ_univ(a, k, Util.total_comp t (Env.get_range env)) in
        let e' = Exp_tabs(a, k, e) in
        (e', t')) (e,c.result_typ) in
      x, e, Util.total_comp t (range_of_exp e (Env.get_range env))) in
     ecs 
