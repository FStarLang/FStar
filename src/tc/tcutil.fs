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
            
let terr env t1 t2 exp = 
  let msg = 
     Util.format3 "Expected an expression of type:\n\n%s\n\nbut got (%s):\n\n%s"
      (Print.typ_to_string t1) 
      (Print.exp_to_string exp)
      (Print.typ_to_string t2) in
    raise (Error (msg, exp.p))

let t_unit = Typ_const (Util.withsort Const.unit_lid Kind_star)
let t_bool = Typ_const (Util.withsort Const.bool_lid Kind_star)
let t_int = Typ_const (Util.withsort Const.int_lid Kind_star)
let t_string = Typ_const (Util.withsort Const.string_lid Kind_star)
let t_float = Typ_const (Util.withsort Const.float_lid Kind_star)

let typing_const (_:env) (s:sconst) = match s with 
  | Const_unit -> t_unit
  | Const_bool _ -> t_bool
  | Const_int32 _ -> t_int
  | Const_string _ -> t_string
  | Const_float _ -> t_float
  | _ -> raise (NYI "Unsupported constant")

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
  let wf t k =
    let tvs, xvs = Util.freevars_typ t in 
    let tvs', xvs' = Env.idents env in 
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    Util.forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
  Typ_uvar (Unionfind.fresh (Uvar wf), k)

let new_evar env t =
  let wf e t = 
    let tvs, xvs = Util.freevars_exp e in
    let tvs', xvs' = Env.idents env in 
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
  withinfo (Exp_uvar (Unionfind.fresh (Uvar wf), t)) t (Env.get_range env)

let unchecked_unify uv t = Unionfind.change uv (Fixed t) (* used to be an alpha-convert t here *)

let unify uvars_in_b (uv,a) b = 
  let occurs uv t = Util.for_some (Unionfind.equivalent uv) (uvars_in_b b) in
    match Unionfind.find uv with 
      | Uvar wf -> 
          if wf b a && not (occurs uv b)
          then (unchecked_unify uv b; true)
          else false
      | _ -> failwith "impossible"
let unify_typ  = unify (fun t -> (uvars_in_typ t).uvars_t |> List.map fst)
let unify_kind = unify (fun u -> (uvars_in_kind u).uvars_k)
let unify_exp  = unify (fun t -> (uvars_in_exp t).uvars_e |> List.map fst)

(**********************************************************************************************)
(* Reduction of types via the Krivine Abstract Machine (KN), with lazy
   reduction and strong reduction (under binders), as described in:

   Strongly reducing variants of the Krivine abstract machine
   Pierre Crégut
   Higher-Order Symb Comput (2007) 20: 209–230 *)
type config<'a> = {code:'a;
                   environment:environment;
                   stack:stack}
and environment = list<env_entry>    
and stack = list<stack_entry>
and env_entry = 
  | T of (btvdef * tclos * memo<typ>)
  | V of (bvvdef * vclos * memo<exp>)
  | TDummy of btvdef
  | VDummy of bvvdef
and stack_entry = either<tclos,vclos> * bool
and tclos = (typ * environment)
and vclos = (exp * environment)
and memo<'a> = ref<option<'a>>

let push se config = {config with stack=se::config.stack}
let pop config = match config.stack with 
  | [] -> None, config
  | hd::tl -> Some hd, {config with stack=tl}
  
let rec sn tcenv (config:config<typ>) : config<typ> =
  let rebuild config  = 
    let rec aux out stack : typ = match stack with
      | [] -> out
      | (Inl (t,e), imp)::rest -> 
        let c = sn tcenv ({code=t; environment=e; stack=[]}) in 
        aux (Typ_app(out, c.code, imp)) rest 
      | (Inr (v,e), imp)::rest -> 
        let c = wne tcenv ({code=v; environment=e; stack=[]}) in 
        aux (Typ_dep(out, c.code, imp)) rest in
    {config with code=aux config.code config.stack; stack=[]} in

  let sn_prod xopt t1 t2 mk = 
    let c1 = sn tcenv ({config with code=t1; stack=[]}) in
    let c2 = match xopt with 
      | None -> {config with code=t2; stack=[]}
      | Some x -> {config with code=t2; environment=VDummy x::config.environment; stack=[]} in
    let c2 = sn tcenv c2 in 
    {config with code=mk c1.code c2.code} in
 
  match Util.compress_typ config.code with 
    | Typ_uvar(uv, k) ->
      rebuild config 

    | Typ_const fv ->
      begin match Tc.Env.lookup_typ_abbrev tcenv fv.v with
        | None -> rebuild config 
        | Some t -> (* delta(); alpha ();  *)
          sn tcenv ({config with code=Util.alpha_convert t})
      end  
        
    | Typ_btvar btv -> 
      begin match config.environment |> Util.find_opt (function | TDummy a | T (a, _, _) -> bvd_eq btv.v a | _ -> false) with 
        | None  (* possible for an open term *)
        | Some (TDummy _) -> rebuild config 
        | Some (T(_, (t,e), m)) -> 
          begin match !m with 
            | Some t -> (* nlazy();  *)
              sn tcenv ({config with code=t; environment=e}) 
            | None -> 
              let config' = {code=t; environment=e; stack=[]} in
              let c = sn tcenv config' in
              m := Some c.code;
              sn tcenv ({c with stack=config.stack})
          end
        | _ -> failwith "Impossible: expected a type"
      end

    | Typ_app(t1, t2, imp) -> 
      let se = Inl (t2, config.environment), imp in
      let config = push se ({config with code=t1}) in 
      sn tcenv config 
        
    | Typ_dep(t, v, imp) -> 
      let se = Inr (v, config.environment), imp in
      let config = push se ({config with code=t}) in 
      sn tcenv config 

    | Typ_lam(x, t1, t2) -> 
      let c1 = sn tcenv ({config with code=t1; stack=[]}) in
      begin match pop config with 
        | None, config -> (* stack is empty; reduce under lambda and return *)
          let c2 = sn tcenv ({config with 
            code=t2;
            environment=VDummy x::config.environment}) in
          {config with code=Typ_lam(x, c1.code, c2.code)} 
            
        | Some (Inr vclos, _), config -> (* beta(); *)
          sn tcenv ({config with 
            code=t2;
            environment=V(x,vclos,ref None)::config.environment})
            
        | _ -> failwith "Impossible: ill-typed redex"
      end
        
        
    | Typ_tlam(a, k, t) -> 
      let ck = snk tcenv ({code=k; environment=config.environment; stack=[]}) in
      begin match pop config with 
        | None, config  -> (* stack is empty; reduce under lambda and be done *)
          let c = sn tcenv ({config with 
            code=t;
            environment=TDummy a::config.environment}) in 
          {config with code=Typ_tlam(a, ck.code, c.code)}
            
        | Some (Inl tclos, _), config ->  (* beta();  type-level beta redex *)
          sn tcenv ({config with 
            code=t;
            environment=T(a,tclos,ref None)::config.environment})
            
        | _ -> failwith "Impossible: Ill-typed redex"
      end
  
    | Typ_ascribed(t, _) -> 
      sn tcenv ({config with code=t})

    | Typ_meta(Meta_pos(t, p)) -> 
      let c = sn tcenv ({config with code=t}) in
      {c with code=Typ_meta(Meta_pos(c.code, p))}

    (* In all remaining cases, the stack should be empty *)
    | Typ_fun(xopt, t1, t2, imp) -> 
      sn_prod xopt t1 t2 (fun t1 t2 -> Typ_fun(xopt, t1, t2, imp)) 
        
    | Typ_refine(x, t1, t2) -> 
      sn_prod (Some x) t1 t2 (fun t1 t2 -> Typ_refine(x, t1, t2)) 
  
    | Typ_univ(a, k, t) -> 
      let ck = snk tcenv ({code=k; environment=config.environment; stack=[]}) in 
      let ct = sn tcenv ({config with 
        code=t; 
        stack=[];
        environment=TDummy a::config.environment}) in 
      {config with code=Typ_univ(a, ck.code, ct.code)}

    | Typ_meta(Meta_pattern(t, ps)) -> (* no reduction in patterns *)
      let c = sn tcenv ({config with code=t}) in
      {c with code=Typ_meta(Meta_pattern(c.code, ps))}
    
    | Typ_meta(Meta_cases tl) -> 
      let cases = snl tcenv (tl |> List.map (fun t -> {config with code=t; stack=[]})) in
      let t = Typ_meta(Meta_cases (cases |> List.map (fun c -> c.code))) in
      {config with code=t}
        
    | Typ_meta(Meta_tid _)
    | Typ_unknown -> failwith "impossible"
            
and snl tcenv configs : list<config<typ>> =
  List.map (sn tcenv) configs

and snk tcenv (config:config<kind>) : config<kind> =
  match Util.compress_kind config.code with
    | Kind_uvar _ 
    | Kind_star -> config
    | Kind_tcon(aopt, k1, k2, imp) -> 
      let c1 = snk tcenv ({config with code=k1}) in
      let c2 = snk tcenv ({config with 
        code=k2;
        environment=(match aopt with 
          | None -> config.environment
          | Some a -> TDummy a::config.environment)}) in 
      {config with code=Kind_tcon(aopt, c1.code, c2.code, imp)}
        
    | Kind_dcon(xopt, t1, k2, imp) -> 
      let c1 = sn tcenv ({code=t1; environment=config.environment; stack=[]}) in
      let c2 = snk tcenv ({config with 
        code=k2;
        environment=(match xopt with 
          | None -> config.environment
          | Some x -> VDummy x::config.environment)}) in 
      {config with code=Kind_dcon(xopt, c1.code, c2.code, imp)}
        
    | Kind_unknown -> 
      failwith "Impossible"

(* The type checker never attempts to reduce expressions itself; relies on the solver for that *)
and wne tcenv (config:config<exp>) : config<exp> = config 
      
let normalize tcenv t = 
  let c = sn tcenv ({code=t; environment=[]; stack=[]}) in
  c.code

(**********************************************************************************************************************)
type rel = 
  | EQ 
  | SUB

let rec krel rel env k k' : bool =
  let k, k' = compress_kind k, compress_kind k' in
  match k, k' with 
    | Kind_star, Kind_star -> true
    | Kind_tcon(aopt, k1, k2, _), Kind_tcon(bopt, k1', k2', _) -> 
      if krel rel env k1' k1
      then match aopt, bopt with 
        | None, _
        | _, None -> krel rel env k2 k2'
        | Some a, Some b -> 
          let k2' = Util.subst_kind [Inl(b, Util.bvd_to_typ a k1')] k2' in
          krel rel env k2 k2'
      else false
    | Kind_dcon(xopt, t1, k1, _), Kind_dcon(yopt, t1', k1', _) -> 
      if trel rel env t1' t1
      then match xopt, yopt with 
        | None, _
        | _, None -> krel rel env k1 k1'
        | Some x, Some y -> 
          let k1' = Util.subst_kind [Inr(y, Util.bvd_to_exp x t1')] k1' in
          krel rel env k1 k1'
      else false
    | Kind_uvar uv, k1  
    | k1 , Kind_uvar uv -> 
      unify_kind (uv, ()) k1
    | _ -> false 

and trel rel env t t' = 
  let rec aux norm t t' =
    let t, t' = compress_typ t, compress_typ t' in
      match t, t' with 
       | Typ_ascribed(t, _), _
       | Typ_meta (Meta_pattern(t, _)), _
       | Typ_meta (Meta_pos(t, _)), _ -> aux norm t t' 

       | _, Typ_ascribed(t', _)
       | _, Typ_meta (Meta_pattern(t', _))
       | _, Typ_meta (Meta_pos(t', _)) -> aux norm t t'

       | Typ_refine(_, t, _), _ when (rel=SUB) -> aux norm t t'
       | _, Typ_refine(_, t', _) when (rel=SUB) -> aux norm t t'

       | Typ_btvar a1, Typ_btvar a1' -> Util.bvd_eq a1.v a1'.v 
       | Typ_const c1, Typ_const c1' -> 
         if Util.fvar_eq c1 c1' then true
         else if not norm
         then aux true (normalize env t) (normalize env t') 
         else false

       | Typ_fun(Some x, t1, t2, _), Typ_fun(Some x', t1', t2', _)  
       | Typ_lam(x, t1, t2), Typ_lam(x', t1', t2')  
       | Typ_refine(x, t1, t2), Typ_refine(x', t1', t2') -> 
         aux norm t1' t1 && 
         aux norm t2 (Util.subst_typ [Inr(x', Util.bvd_to_exp x t1)] t2')
      
       | Typ_fun(_, t1, t2, _), Typ_fun(_, t1', t2', _)  -> 
         aux norm t1' t1 &&
         aux norm t2 t2'
     
       | Typ_tlam(a1, k1, t1), Typ_tlam(a1', k1', t1')  
       | Typ_univ(a1, k1, t1), Typ_univ(a1', k1', t1') -> 
         krel rel env k1' k1 &&
         aux norm t1 (Util.subst_typ [Inl(a1', Util.bvd_to_typ a1 k1')] t1')
     
       | Typ_uvar(uv, k), t1 
       | t1, Typ_uvar(uv,k) -> 
         unify_typ (uv, k) t1 

       | Typ_app _, _
       | Typ_dep _, _
       | _, Typ_app _
       | _, Typ_dep _  -> 
         let tc, args = Util.flatten_typ_apps t in
         let tc', args' = Util.flatten_typ_apps t' in
         if List.length args = List.length args' && aux norm tc tc'
         then List.zip args args' |> Util.for_all (function 
                | Inl t1, Inl t1' -> aux norm t1 t1'
                | Inr e1, Inr e1' -> exp_equiv env e1 e1'
                | _ -> false)
         else if not norm 
         then aux true (normalize env t) (normalize env t')
         else false

       | Typ_unknown, _ 
       | _, Typ_unknown -> failwith "Impossible"

       | _ -> false in
  aux false t t'

and exp_equiv env e e' = 
  let e, e' = compress_exp e, compress_exp e' in 
  match e.v, e'.v with 
    | Exp_bvar x1, Exp_bvar x1' -> Util.bvd_eq x1.v x1'.v
    | Exp_fvar (fv1, _), Exp_fvar (fv1', _) -> lid_equals fv1.v fv1'.v
    | Exp_constant s1, Exp_constant s1' -> const_eq s1 s1'

    | Exp_abs(x1, t1, e1), Exp_abs(x1', t1', e1') -> 
      if trel EQ env t1 t1'
      then let e1' = Util.subst_exp [Inr(x1', Util.bvd_to_exp x1 t1)] e1' in
           exp_equiv env e1 e1'
      else false

    | Exp_tabs(a1, k1, e1), Exp_tabs(a1', k1', e1') -> 
      if krel EQ env k1 k1' 
      then let e1' = Util.subst_exp [Inl(a1', Util.bvd_to_typ a1 k1)] e1' in
           exp_equiv env e1 e1'
      else false

    | Exp_app(e1, e2, _), Exp_app(e1', e2', _) -> 
      exp_equiv env e1 e1' && exp_equiv env e2 e2'

    | Exp_tapp(e1, t1), Exp_tapp(e1', t1') -> 
      exp_equiv env e1 e1' && trel EQ env t1 t1'

    | Exp_match(e1, pats), Exp_match(e1', pats') -> 
      if List.length pats = List.length pats' && exp_equiv env e1 e1'
      then 
        List.zip pats pats' |> Util.for_all (fun ((p, wopt, b), (p', wopt', b')) -> 
          let weq = match wopt, wopt' with 
            | None, None -> true
            | Some w, Some w' -> exp_equiv env w w'
            | _ -> false in
          pat_eq env p p' && weq && exp_equiv env b b')
      else false

    | Exp_ascribed(e1, _), Exp_ascribed(e1', _) -> 
      exp_equiv env e1 e1'

    | Exp_let((b, lbs), e1), Exp_let((b', lbs'), e1') when (b=b') -> 
      if List.length lbs = List.length lbs'
      then exp_equiv env e1 e1' && List.zip lbs lbs' |> Util.for_all (function
        | (Inl x, t, e), (Inl x', t', e') ->
          trel EQ env t t' && exp_equiv env e (Util.subst_exp [Inr(x', Util.bvd_to_exp x t)] e')
        | (Inr l, t, e), (Inr l', t', e') when lid_equals l l' -> 
          trel EQ env t t' && exp_equiv env e e'
        | _ -> false)
      else false

    | Exp_primop(id, el), Exp_primop(id', el') when (id.idText = id'.idText && List.length el = List.length el') -> 
      List.zip el el' |> Util.for_all (fun (e,e') -> exp_equiv env e e')

    | Exp_uvar(uv, t), _ -> unify_exp (uv, t) e'
    | _, Exp_uvar(uv, t) -> unify_exp (uv, t) e

    | _ -> false

and pat_eq env p p' = match p, p' with
  | Pat_cons(l, pats), Pat_cons(l', pats') when (lid_equals l l' && List.length pats = List.length pats') ->
    List.zip pats pats' |> Util.for_all (fun (p,p') -> pat_eq env p p')
  | Pat_var x, Pat_var x' -> Util.bvd_eq x x'
  | Pat_tvar a, Pat_var a' -> Util.bvd_eq a a'
  | Pat_constant s, Pat_constant s' -> const_eq s s'
  | Pat_disj pats, Pat_disj pats' when (List.length pats = List.length pats') -> 
    List.zip pats pats' |> Util.for_all (fun (p,p') -> pat_eq env p p')
  | Pat_wild, Pat_wild -> true
  | Pat_twild, Pat_twild -> true
  | _ -> false

and const_eq s1 s2 = match s1, s2 with 
  | Const_bytearray(b1, _), Const_bytearray(b2, _) -> b1=b2
  | Const_string(b1, _), Const_string(b2, _) -> b1=b2
  | _ -> s1=s2 

let keq env t k1 k2 = 
  if krel EQ env k1 k2
  then ()
  else match t with 
    | None -> raise (Error(Tc.Errors.incompatible_kinds k2 k1, Tc.Env.get_range env))
    | Some t -> raise (Error(Tc.Errors.expected_typ_of_kind k2 t k1, Tc.Env.get_range env))

let teq env t1 t2 = 
  if trel EQ env t1 t2
  then ()
  else raise (Error(Tc.Errors.basic_type_error t2 t1, Tc.Env.get_range env))

let check_and_ascribe (env:env) (e:exp) (t:typ) : exp =
  if not (trel SUB env e.sort t)
  then raise (Error(Tc.Errors.expected_expression_of_type t e.sort, e.p))
  else if trel EQ env e.sort t
  then e 
  else withinfo (Exp_ascribed(e, t)) t e.p

let destruct_function_typ (env:env) (t:typ) (f:exp) (imp_arg_follows:bool) : (typ * exp) = 
  let rec aux norm t f =
    let t = compress_typ t in 
    match t with 
      | Typ_uvar _ when (not imp_arg_follows) -> 
        let arg = new_tvar env Kind_star in
        let res = new_tvar env Kind_star in 
        let tf = Typ_fun(None, arg, res, false) in
        teq env t tf;
        (tf, f)

      | Typ_univ(a, k, t) -> 
        (* need to instantiate an implicit type argument *)
        let arg = new_tvar env k in
        let t' = Util.subst_typ [Inl(a, arg)] t in
        let g = withinfo (Exp_tapp(f, new_tvar env k)) t' f.p in
        aux norm t' g 

      | Typ_fun(_, _, _, false) when imp_arg_follows -> 
        (* function type wants an explicit argument, but we have an implicit arg expected *)
        raise (Error (Tc.Errors.unexpected_implicit_argument, Tc.Env.get_range env))
      
      | Typ_fun(Some x, t1, t2, imp_t1) when (imp_t1 && not imp_arg_follows) ->
        (* need to instantiate an implicit argument *)
        let arg = new_evar env t1 in
        let t2' = subst_typ [Inr(x, arg)] t2 in
        let g = withinfo (Exp_app(f, arg, true)) t2' f.p in
        aux norm t2' g

      | Typ_fun _ -> 
        (* either, we have an implicit function but with an explicit instantiation following;
           or, we have a function with an explicit argument and no implicit arg following *)
        (t, f)

      | _ when not norm -> 
        let t = normalize env t in 
        aux true t f 

      | _ -> 
        raise (Error (Tc.Errors.expected_function_typ t, Tc.Env.get_range env)) in
    aux false t f

let destruct_poly_typ (env:env) (t:typ) (f:exp) : (typ*exp) = 
  let rec aux norm t f =
    let t = compress_typ t in 
    match t with 
      | Typ_univ _ -> 
        (t, f)

      | Typ_fun(Some x, t1, t2, true) ->
        (* need to instantiate an implicit argument *)
        let arg = new_evar env t1 in
        let t2' = subst_typ [Inr(x, arg)] t2 in
        let g = withinfo (Exp_app(f, arg, true)) t2' f.p in
        aux norm t2' g

      | _ when not norm -> 
        let t = normalize env t in 
        aux true t f 

      | _ -> 
        raise (Error (Tc.Errors.expected_poly_typ t, Tc.Env.get_range env)) in
    aux false t f

let destruct_tcon_kind env k tt imp_arg_follows = 
  let rec aux t k = 
    let k = compress_kind k in 
    match k with 
     | Kind_uvar uv when not imp_arg_follows ->  (* inference never introduces a dependent function *)
          let k' = Kind_tcon(None, new_kvar env, new_kvar env, false) in
          keq env None k k';
          k', t
     | Kind_tcon(_, _, _, false) when not imp_arg_follows -> k, t
     | Kind_tcon(_, _, _, true) when imp_arg_follows -> k, t
     | Kind_tcon(Some a, k1, k2, true) -> 
       let targ = new_tvar env k1 in 
       let t' = Typ_app(t, targ, true) in
       aux t' (Util.subst_kind [Inl(a, targ)] k2)
     | Kind_dcon(Some x, t1, k1, true) -> 
       let earg = new_evar env t1 in 
       let t' = Typ_dep(t, earg, true) in 
       aux t' (Util.subst_kind [Inr(x, earg)] k1)
     | _ -> raise (Error(Tc.Errors.expected_tcon_kind tt k, Tc.Env.get_range env)) in
  aux tt k

let destruct_dcon_kind env k tt imp_arg_follows =
  let rec aux t k =  
    let k = compress_kind k in 
    match k with 
    | Kind_uvar uv when not imp_arg_follows ->  (* inference never introduces a dependent function *)
        let k' = Kind_dcon(None, new_tvar env Kind_star, new_kvar env, false) in
        keq env None k k';
        (k', t)
    | Kind_tcon(aopt, k, k', true) -> 
      let arg = new_tvar env k in
      let kres = match aopt with 
        | None -> k'
        | Some a -> Util.subst_kind [Inl(a, arg)] k' in
      aux (Typ_app(t, arg, true)) kres
    | Kind_dcon(_, _, _, b) when (b=imp_arg_follows) -> (k, t)
    | Kind_dcon(Some x, t1, k1, true) -> 
      let earg = new_evar env t1 in 
      let t' = Typ_dep(t, earg, true) in 
      aux t' (Util.subst_kind [Inr(x, earg)] k1)
    | _ -> raise (Error(Tc.Errors.expected_dcon_kind tt k, Tc.Env.get_range env)) in
  aux tt k

let pat_as_exps env p : list<exp> = 
  let single = function 
    | [p] -> p
    | _ -> failwith "Impossible" in
  let rec aux p = match p with
    | Pat_wild ->  [Inr (new_evar env (new_tvar env Kind_star))]
    | Pat_twild  -> [Inl (new_tvar env (new_kvar env))]
    | Pat_var x -> [Inr (Util.bvd_to_exp x (new_tvar env Kind_star))]
    | Pat_tvar a -> [Inl (Util.bvd_to_typ a (new_kvar env))]
    | Pat_constant c -> [Inr (withinfo (Exp_constant c) (typing_const env c) (Env.get_range env))]
    | Pat_cons(l, pats) -> 
      let args = List.map (fun p -> single (aux p)) pats in 
      [Inr (Util.mk_data l args)]
    | Pat_disj pats -> 
      pats |> List.map (fun p -> single <| aux p) in
  List.map (function 
    | Inl _ -> failwith "Impossible"
    | Inr e -> e) (aux p)    

let generalize uvars e t : (exp * typ) = 
    if not (is_value e) then e, t 
    else
      let uvars_t = (Util.uvars_in_typ t).uvars_t in
      let generalizable = uvars_t |> List.filter (fun (uv,_) -> not (uvars.uvars_t |> Util.for_some (fun (uv',_) -> Unionfind.equivalent uv uv'))) in 
      let tvars = generalizable |> List.map (fun (u,k) -> 
        let a = Util.new_bvd (Some e.p) in
        let t = Util.bvd_to_typ a k in
        unchecked_unify u t;
        (a,k)) in
      tvars |> List.fold_left (fun (e,t) (a,k) ->
        let t' = Typ_univ(a, k, t) in
        let e' = withinfo (Exp_tabs(a, k, e)) t' e.p in
        (e', t')) (e,t) 
