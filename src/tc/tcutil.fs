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
        
let handle_err warning ret e = 
  match e with
    | Not_found_binding (env, Inl t) -> 
        Util.print_string (Util.format1 "(Compiler bug?) Type name not found: %s\n" (Print.typ_to_string t));
        ret
    | Not_found_binding (env, Inr e) -> 
        Util.print_string (Util.format1 "(Compiler bug?) Variable not found: %s\n" (Print.exp_to_string e));
        ret
    | Error(msg, r) ->
        Util.print_string (Util.format3 "%s : %s : %s\n" (Range.string_of_range r) (if warning then "Warning" else "Error") msg);
        ret
    | NYI s -> 
        Util.print_string (Util.format1 "Feature not yet implemented: %s" s); 
        ret
    | _ -> raise e
    
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

let typing_const (_:env) = function
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
and stack_entry = either<tclos,vclos>
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
      | Inl (t,e)::rest -> 
        let c = sn tcenv ({code=t; environment=e; stack=[]}) in 
        aux (Typ_app(out, c.code)) rest 
      | Inr (v,e)::rest -> 
        let c = wne tcenv ({code=v; environment=e; stack=[]}) in 
        aux (Typ_dep(out, c.code)) rest in
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

    | Typ_app(t1, t2) -> 
      let se = Inl (t2, config.environment) in
      let config = push se ({config with code=t1}) in 
      sn tcenv config 
        
    | Typ_dep(t, v) -> 
      let se = Inr (v, config.environment) in
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
            
        | Some (Inr vclos), config -> (* beta(); *)
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
            
        | Some (Inl tclos), config ->  (* beta();  type-level beta redex *)
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
    | Kind_tcon(aopt, k1, k2) -> 
      let c1 = snk tcenv ({config with code=k1}) in
      let c2 = snk tcenv ({config with 
        code=k2;
        environment=(match aopt with 
          | None -> config.environment
          | Some a -> TDummy a::config.environment)}) in 
      {config with code=Kind_tcon(aopt, c1.code, c2.code)}
        
    | Kind_dcon(xopt, t1, k2) -> 
      let c1 = sn tcenv ({code=t1; environment=config.environment; stack=[]}) in
      let c2 = snk tcenv ({config with 
        code=k2;
        environment=(match xopt with 
          | None -> config.environment
          | Some x -> VDummy x::config.environment)}) in 
      {config with code=Kind_dcon(xopt, c1.code, c2.code)}
        
    | Kind_unknown -> 
      failwith "Impossible"

(* The type checker never attempts to reduce expressions itself; rely on the solver for that *)
and wne tcenv (config:config<exp>) : config<exp> = config 
      
let normalize tcenv t = 
  let c = sn tcenv ({code=t; environment=[]; stack=[]}) in
  c.code

(**********************************************************************************************************************)

let rec kind_equiv env k k' : bool =
  let k, k' = compress_kind k, compress_kind k' in
  match k, k' with 
  | Kind_star, Kind_star -> true
  | Kind_tcon(aopt, k1, k2), Kind_tcon(bopt, k1', k2') -> 
    if kind_equiv env k1 k1'
    then match aopt, bopt with 
      | None, _
      | _, None -> kind_equiv env k2 k2'
      | Some a, Some b -> 
        let k2' = Util.subst_kind [Inl(b, Util.bvd_to_typ a k1)] k2' in
        kind_equiv env k2 k2'
    else false
  | Kind_dcon(xopt, t1, k1), Kind_dcon(yopt, t1', k1') -> 
    if typ_equiv env t1 t1'
    then match xopt, yopt with 
      | None, _
      | _, None -> kind_equiv env k1 k1'
      | Some x, Some y -> 
        let k1' = Util.subst_kind [Inr(y, Util.bvd_to_exp x t1)] k1' in
        kind_equiv env k1 k1'
    else false
  | Kind_uvar uv, k1  
  | k1 , Kind_uvar uv -> 
    unify_kind (uv, ()) k1
  | _ -> false 

and typ_equiv env t t' = 
  let t, t' = compress_typ t, compress_typ t' in
    match t, t' with 
     | Typ_ascribed(t, _), _
     | Typ_meta (Meta_pattern(t, _)), _
     | Typ_meta (Meta_pos(t, _)), _ -> typ_equiv env t t'

     | _, Typ_ascribed(t', _)
     | _, Typ_meta (Meta_pattern(t', _))
     | _, Typ_meta (Meta_pos(t', _)) -> typ_equiv env t t'

     | Typ_btvar a1, Typ_btvar a1' when Util.bvd_eq a1.v a1'.v -> true
     | Typ_const c1, Typ_const c1' when Util.fvar_eq c1 c1' -> true
     
     | Typ_fun(Some x, t1, t2, _), Typ_fun(Some x', t1', t2', _)  
     | Typ_lam(x, t1, t2), Typ_lam(x', t1', t2')  
     | Typ_refine(x, t1, t2), Typ_refine(x', t1', t2') -> 
       typ_equiv env t1 t1' && 
       typ_equiv env t2 (Util.subst_typ [Inr(x', Util.bvd_to_exp x t1)] t2')
      
     | Typ_fun(_, t1, t2, _), Typ_fun(_, t1', t2', _)  -> 
       typ_equiv env t1 t1' &&
       typ_equiv env t2 t2'
     
     | Typ_tlam(a1, k1, t1), Typ_tlam(a1', k1', t1')  
     | Typ_univ(a1, k1, t1), Typ_univ(a1', k1', t1') -> 
       kind_equiv env k1 k1' &&
       typ_equiv env t1 (Util.subst_typ [Inl(a1', Util.bvd_to_typ a1 k1)] t1')
     
     | Typ_app(t1, t2), Typ_app(t1', t2') -> 

       typ_equiv env t1 t1' &&
       typ_equiv env t2 t2'
         
     | Typ_dep(t1, e1), Typ_dep(t1', e1') -> 
       typ_equiv env t1 t1' &&
       exp_equiv env e1 e1'
       
     | Typ_uvar(uv1, k1), Typ_uvar(uv1', k1') -> 
       kind_equiv env k1 k1' && 
       unify_typ (uv1, k1) t'

     | Typ_unknown, _ 
     | _, Typ_unknown -> failwith "Impossible"

     | _ -> failwith "NYI"

and exp_equiv env e1 e2 = false


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

let subtype env t1 t2 = failwith "NYI"
let destruct_function_typ env t imp : option<typ> = failwith "NYI"
let destruct_poly_typ env t : option<typ> = failwith "NYI"

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
//          
//
//type subst = list<(list<uvar*kind> * option<typ>)>         
//let unify_subst_vars (subst:subst) = 
//  let unify_eq_class (uvl, topt) = match uvl with 
//    | [] -> raise (NYI "Unexpected empty equivalence class")
//    | (uv,_)::tl  -> 
//        List.iter (fun (uv',_) -> Unionfind.union uv uv') tl;
//        match topt with
//          | None -> ()
//          | Some t -> unify uv t in
//    List.iter unify_eq_class subst
//
//let mkTypApp t1 t2 = match t1.sort(* .u *)with 
//  | Kind_tcon(_, _, k2) -> 
//      twithsort (Typ_app(t1, t2)) (open_kind t1.sort t2)
//  | _ -> failwith "impossible"
//
//let mkTypDep t v = match t.sort(* .u *)with 
//  | Kind_dcon(_, _, k2) -> 
//      twithsort (Typ_dep(t, v)) (open_kind_with_exp t.sort v)
//  | _ -> failwith "impossible"
//
//let rec reduce_typ_delta_beta tenv t = 
//  let rec aux t = 
//    let t = expand_typ tenv t in 
//      match t.v with 
//        | Typ_dep(t1orig, e) -> 
//            let t1 = aux t1orig in
//              (match t1.v with 
//                 | Typ_lam(x, t1_a, t1_r) -> 
//                     let t1_r' = substitute_exp t1_r x e in 
//                       aux t1_r'
//                 | _ -> 
//                     if t1orig===t1 
//                     then t
//                     else twithinfo (Typ_dep(t1, e)) t.sort t.p)
//        | Typ_app(t1orig, t2orig) -> 
//            let t1 = aux t1orig in
//            let t2 = aux t2orig in
//              (match t1.v with 
//                 | Typ_tlam(a, t1_a, t1_r) -> 
//                     let t1_r' = substitute t1_r a t2 in
//                       aux t1_r'
//                 | _ -> 
//                     if t1orig===t1 && t2orig===t2 
//                     then t
//                     else twithinfo (Typ_app(t1, t2)) t.sort t.p)
//        | _ -> t in
//    aux t
//
//let rtdb tenv t = 
//  let rec rtdb i tenv t = 
//    let rec aux smap t =
//      let t = expand_typ tenv t in 
//        match t.v with 
//          | Typ_dep(t1orig, e) -> 
//              let smap, t1 = aux smap t1orig in
//                (match t1.v with 
//                   | Typ_lam(x, t1_a, t1_r) -> 
//                       let smap = Inr(x,(substitute_exp_typ_or_exp_l e smap))::smap in 
//                         aux smap t1_r
//                   | _ -> 
//                       if t1orig===t1 
//                       then smap, t
//                       else smap, twithinfo (Typ_dep(t1, e)) t.sort t.p)
//          | Typ_app(t1orig, t2orig) -> 
//              let smap, t1 = aux smap t1orig  in
//              let smap, t2 = aux smap t2orig in
//                (match t1.v with 
//                   | Typ_tlam(a, t1_a, t1_r) -> 
//                       let smap = Inl(a, (substitute_l_typ_or_exp t2 smap))::smap in 
//                         aux smap t1_r
//                   | _ -> 
//                       if t1orig===t1 && t2orig===t2 
//                       then smap, t
//                       else smap, twithinfo (Typ_app(t1, t2)) t.sort t.p)
//          | _ -> smap, t in
//    let smap, t = aux [] t in 
//      match smap with 
//        | [] -> (* pr "rtdb %d noop\n" i; *)
//            t
//        | _ -> 
//            (* pr "rtdb %d subst %d\n" i (List.length smap);  *)
//            rtdb (i+1) tenv (substitute_l_typ_or_exp t smap) in 
//    rtdb 0 tenv t

let generalize uvars e t : (exp * typ) = 
    if not (is_value e) then e, t 
    else
      let uvars_t = (Util.uvars_in_typ t).uvars_t in
      let generalizable = uvars_t |> List.filter (fun (uv,_) -> not (uvars |> Util.for_some (fun (uv',_) -> Unionfind.equivalent uv uv'))) in 
      let tvars = generalizable |> List.map (fun (u,k) -> 
        let a = Util.new_bvd (Some e.p) in
        let t = Util.bvd_to_typ a k in
        unchecked_unify u t;
        (a,k)) in
      tvars |> List.fold_left (fun (e,t) (a,k) ->
        let t' = Typ_univ(a, k, t) in
        let e' = withinfo (Exp_tabs(a, k, e)) t' e.p in
        (e', t')) (e,t) 
