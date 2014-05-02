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
            
let t_unit = withkind Kind_star <| Typ_const (Util.withsort Const.unit_lid Kind_star)
let t_bool = withkind Kind_star <| Typ_const (Util.withsort Const.bool_lid Kind_star)
let t_int = withkind Kind_star <| Typ_const (Util.withsort Const.int_lid Kind_star)
let t_int64 = withkind Kind_star <| Typ_const (Util.withsort Const.int64_lid Kind_star)
let t_string = withkind Kind_star <| Typ_const (Util.withsort Const.string_lid Kind_star)
let t_float = withkind Kind_star <| Typ_const (Util.withsort Const.float_lid Kind_star)
let t_char = withkind Kind_star <| Typ_const(Util.withsort Const.char_lid Kind_star)

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
    | Kind_star, Kind_star -> true
    | Kind_tcon(_, k1, k2, _), Kind_tcon(_, k1', k2', _) -> pre_kind_compat k1 k1' && pre_kind_compat k2 k2'
    | Kind_dcon(_, _, k1, _), Kind_dcon(_, _, k1', _) -> pre_kind_compat k1 k1'
    | k1, k2 -> //Util.print_string (Util.format2 "Pre-kind-compat failed on %s and %s\n" (Print.kind_to_string k1) (Print.kind_to_string k2)); 
    false in
  let wf t tk =
    let tvs, xvs = Util.freevars_typ t in 
    let tvs', xvs' = Env.idents env in 
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    let freevars_in_env = Util.forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
    let err () = () in
//      printfn "Failed: Trying to unify uvar of kind %s with type %s of kind %s\n" (Print.kind_to_string k) (Print.typ_to_string t) (Print.kind_to_string tk);
//      printfn "freevars = %b; %A; %A\n" freevars_in_env tvs xvs in
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

let unchecked_unify uv t = Unionfind.change uv (Fixed t) (* used to be an alpha-convert t here *)

(**********************************************************************************************)
(* Reduction of types via the Krivine Abstract Machine (KN), with lazy
   reduction and strong reduction (under binders), as described in:

   Strongly reducing variants of the Krivine abstract machine
   Pierre Crégut
   Higher-Order Symb Comput (2007) 20: 209–230 *)
type step = 
  | Alpha
  | Delta
  | Beta
type config<'a> = {code:'a;
                   environment:environment;
                   stack:stack;
                   steps:list<step>}
and environment = list<env_entry>    
and stack = list<stack_entry>
and env_entry = 
  | T of (btvdef * tclos * memo<typ>)
  | V of (bvvdef * vclos * memo<exp>)
  | TDummy of btvdef
  | VDummy of bvvdef
and stack_entry = either<tclos,vclos> * bool
and tclos = (typ * environment * kind)
and vclos = (exp * environment * kind)
and memo<'a> = ref<option<'a>>

let push se config = {config with stack=se::config.stack}
let pop config = match config.stack with 
  | [] -> None, config
  | hd::tl -> Some hd, {config with stack=tl}
  
let rec sn tcenv (config:config<typ>) : config<typ> =
  let rebuild config  = 
    let rec aux out stack : typ = match stack with
      | [] -> out
      | (Inl (t,e,k), imp)::rest -> 
        let c = sn tcenv ({code=t; environment=e; stack=[]; steps=config.steps}) in 
        aux (withkind k <| Typ_app(out, c.code, imp)) rest 
      | (Inr (v,e,k), imp)::rest -> 
        let c = wne tcenv ({code=v; environment=e; stack=[]; steps=config.steps}) in 
        aux (withkind k <| Typ_dep(out, c.code, imp)) rest in
    {config with code=aux config.code config.stack; stack=[]} in

  let sn_prod xopt t1 t2 mk = 
    let c1 = sn tcenv ({config with code=t1; stack=[]}) in
    let c2 = match xopt with 
      | None -> {config with code=t2; stack=[]}
      | Some x -> {config with code=t2; environment=VDummy x::config.environment; stack=[]} in
    let c2 = sn tcenv c2 in 
    {config with code=mk c1.code c2.code} in

  let wk = withkind config.code.k in
  let config = {config with code=Util.compress_typ config.code} in
  match config.code.t with 
    | Typ_uvar(uv, k) ->
      rebuild config 

    | Typ_const fv ->
      if config.steps |> List.contains Delta
      then match Tc.Env.lookup_typ_abbrev tcenv fv.v with
          | None -> rebuild config 
          | Some t -> (* delta(); alpha ();  *)
            let t = if config.steps |> List.contains Alpha then Util.alpha_convert t else t in
            sn tcenv ({config with code=t})
      else rebuild config
        
    | Typ_btvar btv -> 
      begin match config.environment |> Util.find_opt (function | TDummy a | T (a, _, _) -> bvd_eq btv.v a | _ -> false) with 
        | None  (* possible for an open term *)
        | Some (TDummy _) -> rebuild config 
        | Some (T(_, (t,e,_), m)) -> 
          begin match !m with 
            | Some t -> (* nlazy();  *)
              sn tcenv ({config with code=t; environment=e}) 
            | None -> 
              let config' = {code=t; environment=e; stack=[]; steps=config.steps} in
              let c = sn tcenv config' in
              m := Some c.code;
              sn tcenv ({c with stack=config.stack})
          end
        | _ -> failwith "Impossible: expected a type"
      end

    | Typ_app(t1, t2, imp) -> 
      let se = Inl (t2, config.environment, config.code.k), imp in
      let config = push se ({config with code=t1}) in 
      sn tcenv config 
        
    | Typ_dep(t, v, imp) -> 
      let se = Inr (v, config.environment, config.code.k), imp in
      let config = push se ({config with code=t}) in 
      sn tcenv config 

    | Typ_lam(x, t1, t2) -> 
      let c1 = sn tcenv ({config with code=t1; stack=[]}) in
      begin match pop config with 
        | None, config -> (* stack is empty; reduce under lambda and return *)
          let c2 = sn tcenv ({config with 
            code=t2;
            environment=VDummy x::config.environment}) in
          {config with code=wk <| Typ_lam(x, c1.code, c2.code)} 
            
        | Some (Inr vclos, _), config -> (* beta(); *)
          sn tcenv ({config with 
            code=t2;
            environment=V(x,vclos,ref None)::config.environment})
            
        | _ -> failwith "Impossible: ill-typed redex"
      end
        
        
    | Typ_tlam(a, k, t) -> 
      let ck = snk tcenv ({code=k; environment=config.environment; stack=[]; steps=config.steps}) in
      begin match pop config with 
        | None, config  -> (* stack is empty; reduce under lambda and be done *)
          let c = sn tcenv ({config with 
            code=t;
            environment=TDummy a::config.environment}) in 
          {config with code=wk <| Typ_tlam(a, ck.code, c.code)}
            
        | Some (Inl tclos, _), config ->  (* beta();  type-level beta redex *)
          sn tcenv ({config with 
            code=t;
            environment=T(a,tclos,ref None)::config.environment})
            
        | _ -> failwith "Impossible: Ill-typed redex"
      end
  
    | Typ_ascribed(t, _) -> 
      sn tcenv ({config with code=t})

    (* In all remaining cases, the stack should be empty *)
    | Typ_fun(xopt, t1, t2, imp) -> 
      sn_prod xopt t1 t2 (fun t1 t2 -> wk <| Typ_fun(xopt, t1, t2, imp)) 
        
    | Typ_refine(x, t1, t2) -> 
      sn_prod (Some x) t1 t2 (fun t1 t2 -> wk <| Typ_refine(x, t1, t2)) 
  
    | Typ_univ(a, k, t) -> 
      let ck = snk tcenv ({code=k; environment=config.environment; stack=[]; steps=config.steps}) in 
      let ct = sn tcenv ({config with 
        code=t; 
        stack=[];
        environment=TDummy a::config.environment}) in 
      {config with code=wk <| Typ_univ(a, ck.code, ct.code)}

    | Typ_meta(Meta_pattern(t, ps)) -> (* no reduction in patterns *)
      let c = sn tcenv ({config with code=t}) in
      {c with code=wk <| Typ_meta(Meta_pattern(c.code, ps))}
    
    | Typ_meta(Meta_cases tl) -> 
      let cases = snl tcenv (tl |> List.map (fun t -> {config with code=t; stack=[]})) in
      let t = Typ_meta(Meta_cases (cases |> List.map (fun c -> c.code))) in
      {config with code=wk <| t}
        
    | Typ_meta(Meta_pos _) 
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
      let c1 = sn tcenv ({code=t1; environment=config.environment; stack=[]; steps=config.steps}) in
      let c2 = snk tcenv ({config with 
        code=k2;
        environment=(match xopt with 
          | None -> config.environment
          | Some x -> VDummy x::config.environment)}) in 
      {config with code=Kind_dcon(xopt, c1.code, c2.code, imp)}
        
    | Kind_unknown -> 
      failwith "Impossible"

(* The type checker never attempts to reduce expressions itself; but still need to do substitutions *)
and wne tcenv (config:config<exp>) : config<exp> = 
  let e = compress_exp config.code in
  match e with 
    | Exp_fvar _ 
    | Exp_constant _
    | Exp_uvar _  -> config

    | Exp_bvar x -> 
      begin match config.environment |> Util.find_opt (function VDummy y | V (y, _, _) -> bvd_eq x.v y | _ -> false) with 
        | None 
        | Some (VDummy _) -> config
        | Some (V(x, (vc, e, _), m)) -> 
          (match !m with 
            | Some v -> (* nlazy(); *)
              wne tcenv ({config with code=v; environment=e}) 
            | None -> 
              let config = {config with code=vc; environment=e} in 
              let c = wne tcenv config in 
              m:=Some c.code; 
              c)
        | _ -> failwith "Impossible: ill-typed term"
      end
    
    | Exp_primop(id, el) -> 
      let cl = List.map (wne tcenv) (el |> List.map (fun e -> {config with code=e})) in 
      {config with code=Exp_primop(id, cl |> List.map (fun c -> c.code))}

    | Exp_app(e1, e2, imp) -> 
      let c1 = wne tcenv ({config with code=e1}) in
      let c2 = wne tcenv ({config with code=e2}) in
      {config with code=Exp_app(c1.code, c2.code, imp)} 

    | Exp_tapp(e, t) -> 
      let c1 = wne tcenv ({config with code=e}) in
      let c2 = sn tcenv ({code=t; environment=config.environment; stack=[]; steps=config.steps}) in 
      {config with code=Exp_tapp(c1.code, c2.code)}
       
    | Exp_abs _
    | Exp_tabs _
    | Exp_match _
    | Exp_let  _ -> config // failwith (Util.format1 "NYI: %s" (Print.exp_to_string e))
    | Exp_meta _ 
    | Exp_ascribed _ -> failwith "impossible"

      
let normalize tcenv t = 
  let c = sn tcenv ({code=t; environment=[]; stack=[]; steps=[Delta;Alpha;Beta]}) in
  c.code

let norm_kind steps tcenv k = 
  let c = snk tcenv ({code=k; environment=[]; stack=[]; steps=steps}) in
  c.code

let norm_typ steps tcenv t = 
  let c = sn tcenv ({code=t; environment=[]; stack=[]; steps=steps}) in
  c.code

(**********************************************************************************************************************)
let unify_typ env (uv,k) t  = match Unionfind.find uv with 
  | Fixed _ -> failwith "impossible"
  | Uvar wf ->
    let rec aux retry t =
      let tk = t.k in 
      let uvars_in_t = (uvars_in_typ t).uvars_t |> List.map fst in 
      let occurs () = Util.for_some (Unionfind.equivalent uv) uvars_in_t in
      let doit t = match (compress_typ t).t with 
        | Typ_uvar (uv', _) -> Unionfind.union uv uv'; true
        | t' -> 
          if wf t tk && not (occurs ()) 
          then (unchecked_unify uv t; true)
          else false in
      doit t || (retry && aux false (normalize env t)) in
   aux true t
let unify_kind (uv, ()) k = match Unionfind.find uv with 
  | Fixed _ -> failwith "impossible"
  | Uvar wf -> 
    match compress_kind k with 
      | Kind_uvar uv' -> Unionfind.union uv uv'; true
      | k -> 
        let occurs = Util.for_some (Unionfind.equivalent uv) ((uvars_in_kind k).uvars_k) in
        if not occurs && wf k ()
        then (unchecked_unify uv k; true)
        else false
let unify_exp (uv, t) e = match Unionfind.find uv with 
  | Fixed _ -> failwith "impossible"
  | Uvar wf -> 
    match compress_exp e with 
      | Exp_uvar(uv', _) -> Unionfind.union uv uv'; true
      | e -> 
        let occurs = Util.for_some (Unionfind.equivalent uv) ((uvars_in_exp e).uvars_e |> List.map fst) in
        if not occurs && wf e t 
        then (unchecked_unify uv e; true)
        else false
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
      match t.t, t'.t with 
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
     
       | Typ_uvar(uv, _), Typ_uvar(uv', _) when Unionfind.equivalent uv uv' -> 
         true
       
       | Typ_uvar(uv, k), _ -> unify_typ env (uv, k) t'
       | _, Typ_uvar(uv,k) -> unify_typ env (uv, k) t

       | Typ_app _, _
       | Typ_dep _, _
       | _, Typ_app _
       | _, Typ_dep _  -> 
         let tc, args = Util.flatten_typ_apps t in
         let tc', args' = Util.flatten_typ_apps t' in
         let matches = 
          if List.length args = List.length args' && aux norm tc tc'
          then List.zip args args' |> Util.for_all (function 
                | Inl t1, Inl t1' -> aux true t1 t1'
                | Inr e1, Inr e1' -> exp_equiv env e1 e1'
                | _ -> false)
          else false in
         (matches || (not norm && aux true (normalize env t) (normalize env t')))

       | Typ_unknown, _ 
       | _, Typ_unknown -> failwith "Impossible"

       | _ -> false in
  aux false t t'

and exp_equiv env e e' = 
  let e, e' = compress_exp e, compress_exp e' in 
  match e, e' with 
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
  if krel EQ env (norm_kind [Beta] env k1) (norm_kind [Beta] env k2)
  then ()
  else match t with 
    | None -> raise (Error(Tc.Errors.incompatible_kinds k2 k1, Tc.Env.get_range env))
    | Some t -> raise (Error(Tc.Errors.expected_typ_of_kind k2 t k1, Tc.Env.get_range env))

let teq env t1 t2 = 
  if trel EQ env (norm_typ [Beta] env t1) (norm_typ [Beta] env t2)
  then ()
  else raise (Error(Tc.Errors.basic_type_error t2 t1, Tc.Env.get_range env))

let subtype env t1 t2 = 
  let t1' = (norm_typ [Beta] env t1) in
  let t2' =  (norm_typ [Beta] env t2) in
//  printfn "Normalized %s to %s\n" (Print.typ_to_string t2) (Print.typ_to_string t2');
 // printfn "Subtyping %s and %s\n" (Print.typ_to_string t1') (Print.typ_to_string t2');
  trel SUB env t1' t2'

let check_and_ascribe (env:env) (e:exp) (t1:typ) (t2:typ) : exp =
  if not (subtype env t1 t2)
  then (if env.is_pattern
        then raise (Error(Tc.Errors.expected_pattern_of_type t2 e t1, Tc.Env.get_range env))
        else 
          begin
            Util.print_string "subtyping failed\n";
            raise (Error(Tc.Errors.expected_expression_of_type t2 e t1, Tc.Env.get_range env))
          end)
  else if trel EQ env t1 t2
  then e 
  else Exp_ascribed(e, t2)

let maybe_instantiate env e t = 
  let rec aux norm t e = 
    let t = compress_typ t in 
    match t.t with 
      | Typ_univ(a, k, t) when env.instantiate_targs -> 
        let arg = new_tvar env k in
        let t' = Util.subst_typ [Inl(a, arg)] t in
        let f = Exp_tapp(e, arg) in
        aux norm t' f 

      | Typ_fun(Some x, t1, t2, true) when env.instantiate_vargs -> 
        let arg = new_evar env t1 in
        let t2' = subst_typ [Inr(x, arg)] t2 in
        let f = Exp_app(e, arg, true) in
        aux norm t2' f

      | _ when not norm -> 
        let t' = normalize env t in 
        begin match t'.t with 
          | Typ_fun _
          | Typ_univ _ -> aux true t' e
          | _ -> (e, t')
        end

      | _ -> (e, t) in
  aux false t e

let destruct_function_typ (env:env) (t:typ) (f:option<exp>) (imp_arg_follows:bool) : (typ * option<exp>) = 
  let rec aux norm t f =
    let t = compress_typ t in 
    match t.t with 
      | Typ_uvar _ when (not imp_arg_follows) -> 
        let arg = new_tvar env Kind_star in
        let res = new_tvar env Kind_star in 
        let tf = withkind Kind_star <| Typ_fun(None, arg, res, false) in
        teq env t tf;
        (tf, f)

      | Typ_univ(a, k, t) -> 
        (* need to instantiate an implicit type argument *)
        let arg = new_tvar env k in
        let t' = Util.subst_typ [Inl(a, arg)] t in
        let g = match f with 
          | None -> None
          | Some f -> Some <| Exp_tapp(f, new_tvar env k) in
        aux norm t' g 

      | Typ_fun(_, _, _, false) when imp_arg_follows -> 
        (* function type wants an explicit argument, but we have an implicit arg expected *)
        raise (Error (Tc.Errors.unexpected_implicit_argument, Tc.Env.get_range env))
      
      | Typ_fun(Some x, t1, t2, imp_t1) when (imp_t1 && not imp_arg_follows) ->
        (* need to instantiate an implicit argument *)
        let arg = new_evar env t1 in
        let t2' = subst_typ [Inr(x, arg)] t2 in
        let g = match f with 
          | None -> None
          | Some f -> Some <| Exp_app(f, arg, true) in
        aux norm t2' g

      | Typ_fun _ -> 
        (* either, we have an implicit function but with an explicit instantiation following;
           or, we have a function with an explicit argument and no implicit arg following *)
        (t, f)

      | _ when not norm -> 
        let t = normalize env t in 
        aux true t f 

      | _ -> 
        let _ = match f with 
          | Some e -> Util.print_string (Util.format1 "destruct function type failed on expression %s\n" (Print.exp_to_string e))
          | _ -> Util.print_string "Destruct function typ failed, no expression available" in
        raise (Error (Tc.Errors.expected_function_typ t, Tc.Env.get_range env)) in
    aux false t f

let destruct_poly_typ (env:env) (t:typ) (f:exp) targ : (typ*exp) = 
  let rec aux norm t f =
    let t = compress_typ t in 
    match t.t with 
      | Typ_univ _ -> 
        (t, f)

      | Typ_fun(Some x, t1, t2, true) ->
        (* need to instantiate an implicit argument *)
        let arg = new_evar env t1 in
        let t2' = subst_typ [Inr(x, arg)] t2 in
        let g = Exp_app(f, arg, true) in
        aux norm t2' g

      | _ when not norm -> 
        let t = normalize env t in 
        aux true t f 

      | _ -> 
        raise (Error (Tc.Errors.expected_poly_typ f t targ, Tc.Env.get_range env)) in
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
       let k2 = Util.subst_kind [Inl(a, targ)] k2 in
       let t' = withkind k2 <| Typ_app(t, targ, true) in
       aux t' k2
     | Kind_dcon(Some x, t1, k1, true) -> 
       let earg = new_evar env t1 in 
       let k1 = Util.subst_kind [Inr(x, earg)] k1 in
       let t' = withkind k1 <| Typ_dep(t, earg, true) in 
       aux t' k1
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
      aux (withkind kres <| Typ_app(t, arg, true)) kres
    | Kind_dcon(_, _, _, b) when (b=imp_arg_follows) -> (k, t)
    | Kind_dcon(Some x, t1, k1, true) -> 
      let earg = new_evar env t1 in 
      let k1 = Util.subst_kind [Inr(x, earg)] k1 in
      let t' = withkind k1 <| Typ_dep(t, earg, true) in 
      aux t' k1
    | _ -> raise (Error(Tc.Errors.expected_dcon_kind tt k, Tc.Env.get_range env)) in
  aux tt k

let pat_as_exps env p : list<exp> = 
  let single_arg = function 
    | [Inl p] -> Inl p
    | [Inr e] -> Inr (e, false)
    | _ -> failwith "Impossible" in
  let single = function 
    | [te] -> te
    | _ -> failwith "impossible" in
  let rec aux p = match p with
    | Pat_wild ->  [Inr (new_evar env (new_tvar env Kind_star))]
    | Pat_twild  -> [Inl (new_tvar env (new_kvar env))]
    | Pat_var x -> [Inr (Util.bvd_to_exp x (new_tvar env Kind_star))]
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

let generalize env e t : (exp * typ) = 
    if not (is_value e) then e, t 
    else
      let uvars = Env.uvars_in_env env in
      let uvars_t = (Util.uvars_in_typ t).uvars_t in
      let generalizable = uvars_t |> List.filter (fun (uv,_) -> not (uvars.uvars_t |> Util.for_some (fun (uv',_) -> Unionfind.equivalent uv uv'))) in 
      let tvars = generalizable |> List.map (fun (u,k) -> 
        let a = Util.new_bvd (Some <| Tc.Env.get_range env) in
        let t = Util.bvd_to_typ a k in
        unchecked_unify u t;
        (a,k)) in
      tvars |> List.fold_left (fun (e,t) (a,k) ->
        let t' = withkind Kind_star <| Typ_univ(a, k, t) in
        let e' = Exp_tabs(a, k, e) in
        (e', t')) (e,t) 

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
      let u = new_tvar env Kind_star in 
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
      | Typ_unknown -> new_tvar env Kind_star
      | _ -> t in
    let rec aux env e = match e with 
      | Exp_meta(Meta_info(e, _, _)) 
      | Exp_meta(Meta_desugared(e, _)) -> aux env e 
      | Exp_tabs(a, k, e) -> 
        let k = mk_kind env k in
        let env = Env.push_local_binding env (Binding_typ(a, k)) in
        withkind Kind_star <| Typ_univ(a, k, aux env e)
      | Exp_abs(x, t, e) -> 
        let t = mk_typ env t in
        let env = Env.push_local_binding env (Binding_var(x, t)) in
        withkind Kind_star <| Typ_fun(Some x, t, aux env e, false)
      | Exp_ascribed(e, t) -> t
      | _ -> new_tvar env Kind_star in 
    aux env e       
  | _ -> t
