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

module Microsoft.FStar.Tc.Normalize

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env


(**********************************************************************************************
 * Reduction of types via the Krivine Abstract Machine (KN), with lazy
 * reduction and strong reduction (under binders), as described in:
 *
 * Strongly reducing variants of the Krivine abstract machine
 * Pierre Crégut
 * Higher-Order Symb Comput (2007) 20: 209–230  
 **********************************************************************************************)

type step = 
  | Delta
  | DeltaHard
  | Beta
  | DeltaComp
  | Simplify
  | SNComp
and steps = list<step>

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
and tclos = (typ * environment * knd)
and vclos = (exp * environment * knd)
and memo<'a> = ref<option<'a>>

let push se config = {config with stack=se::config.stack}
let pop config = match config.stack with 
  | [] -> None, config
  | hd::tl -> Some hd, {config with stack=tl}
let with_code c e = {code=e; environment=c.environment; stack=[]; steps=c.steps}
     
let rec sn tcenv (cfg:config<typ>) : config<typ> =
  let rebuild config  = 
    let rec aux out stack : typ = match stack with
      | [] -> out
      | (Inl (t,e,k), imp)::rest -> 
        let c = sn tcenv ({code=t; environment=e; stack=[]; steps=config.steps}) in 
        aux (mk_Typ_app(out, c.code, imp) k out.pos) rest
      | (Inr (v,e,k), imp)::rest -> 
        let c = wne tcenv ({code=v; environment=e; stack=[]; steps=config.steps}) in 
        aux (mk_Typ_dep(out, c.code, imp) k out.pos) rest in
    {config with code=aux config.code config.stack; stack=[]} in

  let sn_prod xopt t1 t2 mk = 
    let c1 = sn tcenv ({cfg with code=t1; stack=[]}) in
    let c2 = match xopt with 
      | None -> {cfg with code=t2; stack=[]}
      | Some x -> {cfg with code=t2; environment=VDummy x::cfg.environment; stack=[]} in
    let c2 = sn tcenv c2 in 
    {cfg with code=mk c1.code c2.code} in

  let wk f = f cfg.code.tk cfg.code.pos in
  let config = match cfg.environment with 
    | [] -> {cfg with code=Util.compress_typ cfg.code} 
    | _ -> {cfg with code=Util.alpha_typ cfg.code} in //Util.alpha_typ cfg.code} in
  match config.code.n with
    | Typ_delayed _ -> failwith "Impossible"
     
    | Typ_uvar _ -> 
      rebuild config 

    | Typ_const fv ->
      if config.steps |> List.contains DeltaHard 
        || (config.steps |> List.contains Delta && List.length config.stack <> 0)
      then match Tc.Env.lookup_typ_abbrev tcenv fv.v with
          | None -> rebuild config 
          | Some t -> (* delta(); *)
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
      let se = Inl (t2, config.environment, config.code.tk), imp in
      let config = push se ({config with code=t1}) in 
      sn tcenv config 
        
    | Typ_dep(t, v, imp) -> 
      let se = Inr (v, config.environment, config.code.tk), imp in
      let config = push se ({config with code=t}) in 
      sn tcenv config 

    | Typ_lam(x, t1, t2) -> 
      let c1 = sn tcenv ({config with code=t1; stack=[]}) in
      begin match pop config with 
        | None, config -> (* stack is empty; reduce under lambda and return *)
          let c2 = sn tcenv ({config with 
            code=t2;
            environment=VDummy x::config.environment}) in
          {config with code=wk <| mk_Typ_lam(x, c1.code, c2.code)} 
            
        | Some (Inr vclos, _), config -> (* beta(); *)
          sn tcenv ({config with 
            code=t2;
            environment=V(x,vclos,Util.mk_ref None)::config.environment})
            
        | _ -> failwith "Impossible: ill-typed redex"
      end
        
        
    | Typ_tlam(a, k, t) -> 
      let ck = snk tcenv (with_code config k) in
      begin match pop config with 
        | None, config  -> (* stack is empty; reduce under lambda and be done *)
          let c = sn tcenv ({config with 
            code=t;
            environment=TDummy a::config.environment}) in 
          {config with code=wk <| mk_Typ_tlam(a, ck.code, c.code)}
            
        | Some (Inl tclos, _), config ->  (* beta();  type-level beta redex *)
          sn tcenv ({config with 
            code=t;
            environment=T(a,tclos,Util.mk_ref None)::config.environment})
            
        | _ -> failwith "Impossible: Ill-typed redex"
      end
  
    | Typ_ascribed(t, _) -> 
      sn tcenv ({config with code=t})

    (* In all remaining cases, the stack should be empty *)
    | Typ_refine(x, t1, t2) -> 
      sn_prod (Some x) t1 t2 (fun t1 t2 -> wk <| mk_Typ_refine(x, t1, t2)) 
  
    | Typ_fun(xopt, t1, comp, imp) -> 
      let c1 = sn tcenv (with_code config t1) in
      let c2 = match xopt with 
      | None -> with_code config comp
      | Some x -> with_code ({config with environment=VDummy x::config.environment}) comp in
      let c2 = sncomp tcenv c2 in 
      {config with code=wk <| mk_Typ_fun(xopt, c1.code, c2.code, imp)} 

    | Typ_univ(a, k, comp) -> 
      let ck = snk tcenv (with_code config k) in
      let ct = sncomp tcenv (with_code ({config with environment=TDummy a::config.environment}) comp) in
      {config with code=wk <| mk_Typ_univ(a, ck.code, ct.code)}

    | Typ_meta(Meta_pattern(t, ps)) -> (* no reduction in patterns *)
      let c = sn tcenv ({config with code=t}) in
      {c with code=wk <| mk_Typ_meta'(Meta_pattern(c.code, ps))}
    
    | Typ_meta(Meta_named _)    
    | Typ_unknown -> failwith "impossible"
            
and snl tcenv configs : list<config<typ>> =
  List.map (sn tcenv) configs

and sncomp tcenv (cfg:config<comp>) : config<comp> = 
  let m = cfg.code in 
  match (compress_comp m).n with 
    | Comp ct -> 
      let ctconf = sncomp_typ tcenv (with_code cfg ct) in
      {cfg with code=mk_Comp ctconf.code}
    | Total t -> 
      if List.contains DeltaComp cfg.steps 
      then sncomp tcenv <| with_code cfg (mk_Comp <| force_comp (mk_Total t))
      else let t = sn tcenv (with_code cfg t) in
           with_code cfg (mk_Total t.code)
    | Flex(u, t) -> 
      let tconf = sn tcenv (with_code cfg t) in 
      {cfg with code=mk_Flex(u, tconf.code)}

and sncomp_typ tcenv (cfg:config<comp_typ>) : config<comp_typ> = 
  let remake l args = 
    let r, eargs = match args with
      | Inl r::rest -> r, rest
      | _ -> failwith "impossible" in
    let c = {effect_name=l; result_typ=r; effect_args=eargs; flags=cfg.code.flags} in
    {cfg with code=c} in
  let m = cfg.code in 
  let res = (sn tcenv (with_code cfg m.result_typ)).code in
  let args = m.effect_args in
  let args = if List.contains SNComp cfg.steps then Inl res::snl_either tcenv (with_code cfg ()) args else Inl res::args in
  if not <| List.contains DeltaComp cfg.steps
  then remake m.effect_name args
  else match Tc.Env.lookup_typ_abbrev tcenv m.effect_name with
        | None -> remake m.effect_name args
        | Some t -> 
          let t = Util.mk_typ_app_explicit t args in
          let tc, args = Util.flatten_typ_apps (sn tcenv (with_code cfg t)).code in 
          let n = match (Util.compress_typ tc).n with
            | Typ_const fv -> remake fv.v args 
            | _ ->  failwith (Util.format3 "Got a computation %s with constructor %s and kind %s" (Print.sli m.effect_name) (Print.typ_to_string tc) (Print.kind_to_string tc.tk)) in
          n
    
and snl_either tcenv config args = 
  args |> List.map (function 
    | Inl t -> let c = sn tcenv (with_code config t) in Inl c.code
    | Inr e -> let c = wne tcenv (with_code config e) in Inr c.code)

and snk tcenv (cfg:config<knd>) : config<knd> =
  let w f = f cfg.code.pos in
  match (Util.compress_kind cfg.code).n with
    | Kind_delayed _ -> failwith "Impossible"
    | Kind_uvar _ 
    | Kind_type
    | Kind_effect -> cfg
    | Kind_abbrev(kabr, k) -> 
      let c1 = snk tcenv ({cfg with code=k}) in
      let args = snl_either tcenv (with_code cfg ()) (snd kabr) in
      {cfg with code=w <| mk_Kind_abbrev((fst kabr, args), c1.code)}
    | Kind_tcon(aopt, k1, k2, imp) -> 
      let c1 = snk tcenv ({cfg with code=k1}) in
      let c2 = snk tcenv ({cfg with 
        code=k2;
        environment=(match aopt with 
          | None -> cfg.environment
          | Some a -> TDummy a::cfg.environment)}) in 
      {cfg with code=w <| mk_Kind_tcon(aopt, c1.code, c2.code, imp)}
        
    | Kind_dcon(xopt, t1, k2, imp) -> 
      let c1 = sn tcenv ({code=t1; environment=cfg.environment; stack=[]; steps=cfg.steps}) in
      let c2 = snk tcenv ({cfg with 
        code=k2;
        environment=(match xopt with 
          | None -> cfg.environment
          | Some x -> VDummy x::cfg.environment)}) in 
      {cfg with code=w <| mk_Kind_dcon(xopt, c1.code, c2.code, imp)}
        
    | Kind_unknown -> 
      failwith "Impossible"

(* The type checker never attempts to reduce expressions itself; but still need to do substitutions *)
and wne tcenv (cfg:config<exp>) : config<exp> = 
  let e = compress_exp cfg.code in
  let w f = f cfg.code.tk cfg.code.pos in
  let config = with_code cfg e in
  match e.n with 
    | Exp_delayed _ -> failwith "Impossible"
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

    | Exp_app(e1, e2, imp) -> 
      let c1 = wne tcenv ({config with code=e1}) in
      let c2 = wne tcenv ({config with code=e2}) in
      {config with code=w <| mk_Exp_app(c1.code, c2.code, imp)} 

    | Exp_tapp(e, t) -> 
      let c1 = wne tcenv ({config with code=e}) in
      let c2 = sn tcenv (with_code config t) in
      {config with code=w <| mk_Exp_tapp(c1.code, c2.code)}
       
    | Exp_abs(x, t, e) -> 
      let t = sn tcenv (with_code config t) in
      let e = wne tcenv ({config with environment=VDummy x::config.environment; code=e}) in
      {config with code=w <| mk_Exp_abs(x, t.code, e.code)}

    | Exp_tabs(a, k, e) -> 
      let k = snk tcenv (with_code config k) in 
      let e = wne tcenv ({config with environment=TDummy a::config.environment; code=e}) in
      {config with code=w <| mk_Exp_tabs(a, k.code, e.code)}

    | Exp_match _
    | Exp_let  _ -> config // failwith (Util.format1 "NYI: %s" (Print.exp_to_string e))
    | Exp_meta _ 
    | Exp_ascribed _ -> failwith "impossible"

(************************************************************************************)
(* External interface *)
(************************************************************************************)

let rec weak_norm_comp env c =
  let tt0 = Util.comp_result c in 
  let c = force_comp c in
  let n = match Tc.Env.lookup_typ_abbrev env c.effect_name with
    | None -> c
    | Some t -> 
      let args = Inl c.result_typ::c.effect_args in
      let out, subst = List.fold_left (fun (out, subst) arg -> match (compress_typ out).n, arg with 
        | Typ_tlam(a, _, out), Inl t -> (out, Inl(a, t)::subst)
        | Typ_lam(x, _, out), Inr e -> (out, Inr(x, e)::subst)
        | _ -> failwith "Ill-kinded comp type") (t, []) args in
      let t = Util.subst_typ (mk_subst subst) out in 
      let tc, args = Util.flatten_typ_apps t in
      let n = match (Util.compress_typ tc).n, args with
        | Typ_const fv, Inl result::rest -> 
          weak_norm_comp env (mk_Comp ({effect_name=fv.v;
                                     result_typ=result;
                                     effect_args=rest;
                                     flags=c.flags}))
        | _ ->  failwith (Util.format3 "Got a computation %s with constructor %s and kind %s" (Print.sli c.effect_name) (Print.typ_to_string tc) (Print.kind_to_string tc.tk)) in
      //let _ = printfn "Normalized %s\nto %s\n" (Print.comp_typ_to_string m) (Print.comp_typ_to_string n.code) in
      n in
  //check_sharing (Util.compress_typ tt0) (Util.compress_typ n.result_typ) "weak_norm_comp";
  n
      
       
let norm_kind steps tcenv k = 
  let c = snk tcenv ({code=k; environment=[]; stack=[]; steps=steps}) in
  c.code

let norm_typ steps tcenv t = 
  let c = sn tcenv ({code=t; environment=[]; stack=[]; steps=steps}) in
  c.code

let norm_comp steps tcenv c = 
  let c = sncomp tcenv ({code=c; environment=[]; stack=[]; steps=steps}) in
  force_comp c.code

let normalize_kind tcenv k = 
  let steps = [Delta;Beta] in
  norm_kind steps tcenv k

let normalize_comp tcenv c = 
  let steps = [Delta;Beta;SNComp;DeltaComp] in
  norm_comp steps tcenv c

let normalize tcenv t = norm_typ [DeltaHard;Beta] tcenv t

