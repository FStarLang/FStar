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
  | WHNF
  | Eta
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
and stack = {
    args:list<(arg * environment)>;
    k:knd
}
and env_entry = 
  | T of (btvdef * tclos * memo<typ>)
  | V of (bvvdef * vclos * memo<exp>)
  | TDummy of btvar
  | VDummy of bvvar
and tclos = (typ * environment)
and vclos = (exp * environment)
and memo<'a> = ref<option<'a>>

let empty_stack k = {
    args=[];
    k=k
}
let rec subst_of_env env = 
    env |> List.collect (function
        | T (a, (t,env'), m) -> 
            [begin match !m with
                | Some t -> Inl(a, t)
                | None -> Inl(a, Util.subst_typ (subst_of_env env') t)
             end]
        | V (x, (v,env'), m) -> 
            [begin match !m with 
                | Some v -> Inr(x, v)
                | None -> Inr(x, Util.subst_exp (subst_of_env env') v)
             end]
        | _ -> []) 

let with_new_code k c e = {code=e; environment=c.environment; stack=empty_stack k; steps=c.steps}

let rec eta_expand tcenv t = 
    let k = Util.compress_kind t.tk in
    match k.n with 
    | Kind_type 
    | Kind_effect
    | Kind_uvar _ -> t
    | Kind_abbrev(_, k) -> 
        eta_expand tcenv ({t with tk=k})
    | Kind_arrow(binders, k') ->
        let binders, args = Util.args_of_binders binders in 
        let body = mk_Typ_app(t, args) k' t.pos in
        mk_Typ_lam(binders, body) k t.pos
    | Kind_lam _
    | Kind_delayed _ -> failwith "Impossible"
    | Kind_unknown -> failwith (Util.format2 "%s: Impossible: Kind_unknown: %s" (Tc.Env.get_range tcenv |> Range.string_of_range) (Print.typ_to_string t))
         
let is_var t = match Util.compress_typ t with
    | {n=Typ_btvar _} -> true
    | _ -> false

let rec eta_expand_exp (tcenv:Tc.Env.env) (e:exp) : exp = failwith "NYI"
let no_eta = List.filter (function Eta -> false | _ -> true)
let no_eta_cfg c = {c with steps=no_eta c.steps}
let whnf_only config = config.steps |> List.contains WHNF
let is_stack_empty config = match config.stack.args with 
    | [] -> true
    | _ -> false
let has_eta cfg = cfg.steps |> List.contains Eta

let rec sn_aux tcenv (cfg:config<typ>) : config<typ> =
  let rebuild config  = 
    let emp = is_stack_empty config in
    let eta = has_eta config in 
    if emp && not eta 
    then config
    else if emp
    then {config with code=eta_expand tcenv config.code} 
    else let s' = no_eta config.steps in
         let args = if whnf_only config
         then config.stack.args |> List.map (function 
            | (Inl t, imp), env -> Inl <| Util.subst_typ (subst_of_env env) t, imp
            | (Inr v, imp), env -> Inr <| Util.subst_exp (subst_of_env env) v, imp)
         else config.stack.args |> List.map (function 
            | (Inl t, imp), env -> Inl <| (sn_aux tcenv ({code=t; environment=env; stack=empty_stack t.tk; steps=s'})).code, imp
            | (Inr v, imp), env -> Inr <| (wne    tcenv ({code=v; environment=env; stack=empty_stack kun; steps=s'})).code, imp) in
         let t = mk_Typ_app(config.code, args) config.stack.k config.code.pos in
         let t = if eta then eta_expand tcenv t else t in
         {config with code=t} in

  let wk f = f cfg.code.tk cfg.code.pos in

  let config = match cfg.environment with 
    | [] -> {cfg with code=Util.compress_typ cfg.code} 
    | _ -> {cfg with code=Util.alpha_typ cfg.code} in

  begin match config.code.n with
    | Typ_delayed _ -> failwith "Impossible"
     
    | Typ_uvar _ -> 
      rebuild config 

    | Typ_meta(Meta_comp c) -> 
      let cfg = sncomp tcenv (with_new_code keffect config c) in
      {config with code=mk_Typ_meta'(Meta_comp(cfg.code)) config.code.tk config.code.pos}

    | Typ_meta(Meta_uvar_t_app(t, (uv,k))) ->
      let cfg = sn tcenv ({config with code=t}) in
      {cfg with code=mk_Typ_meta'(Meta_uvar_t_app(cfg.code, (uv,k))) cfg.code.tk cfg.code.pos}
   
    | Typ_const fv ->
      if config.steps |> List.contains DeltaHard 
        || (config.steps |> List.contains Delta && is_stack_empty config)
      then match Tc.Env.lookup_typ_abbrev tcenv fv.v with
          | None -> rebuild config 
          | Some t -> (* delta(); *)
            sn tcenv ({config with code=t})
      else rebuild config
        
    | Typ_btvar a -> 
      begin match config.environment |> Util.find_opt (function TDummy b -> bvar_eq a b | T (b, _, _) -> bvd_eq a.v b | _ -> false) with 
        | None -> rebuild config (* possible for an open term *)
        | Some (TDummy a) -> rebuild ({config with code=btvar_to_typ a})
        | Some (T(_, (t,e), m)) -> 
          begin match !m with 
            | Some t -> (* nlazy();  *)
              sn tcenv ({config with code=t; environment=e}) 
            | None -> 
              let c = sn tcenv ({code=t; environment=e; stack=empty_stack t.tk; steps=config.steps}) in //eval in empty stack to memo-ize
              m := Some c.code;
              match config.stack.args with 
                | [] -> c
                | _ -> sn tcenv ({c with stack=config.stack}) //then evaluate any redexes
          end
        | _ -> failwith "Impossible: expected a type"
      end

    | Typ_app(head, args) -> 
      let stack = {config.stack with args=(args |> List.map (fun a -> a, config.environment)) @ config.stack.args} in 
      sn tcenv ({config with code=head; stack=stack})

    | Typ_lam(binders, t2) -> 
      begin match config.stack.args with 
        | [] -> 
          if whnf_only config (* only want WHNF ... don't enter *)
          then {config with code=Util.subst_typ (subst_of_env config.environment) config.code}
          else (* Want full normal: reduce under lambda and return *)
               let binders, environment = sn_binders tcenv binders config.environment config.steps in
               let c2 = sn tcenv ({config with code=t2; environment=environment}) in
               {config with code=wk <| mk_Typ_lam(binders, c2.code)}
        | args -> (* beta *)
          
          let rec beta env binders args = match binders, args with 
            | [], _ -> (* fully applied, or more actuals (extra currying) *)
              sn tcenv ({config with code=t2; environment=env; stack={config.stack with args=args}})

            | _, [] -> (* more formals (partially applied) *)
              let t = mk_Typ_lam(binders, t2) (mk_Kind_arrow(binders, t2.tk) t2.pos) t2.pos in
              sn tcenv ({config with code=t; environment=env; stack=empty_stack config.stack.k})
  
            | formal::rest, actual::rest' -> 
              let m = match formal, actual with 
                | (Inl a, _), ((Inl t, _), env) -> T(a.v, (t,env), Util.mk_ref None)
                | (Inr x, _), ((Inr v, _), env) -> V(x.v, (v,env), Util.mk_ref None)
                | _ -> failwith "Impossible: ill-typed redex" in
              beta (m::env) rest rest' in

           beta config.environment binders args
      end

    | Typ_ascribed(t, _) -> 
      sn tcenv ({config with code=t})

    | _ -> 
        if whnf_only config
        then {config with code=Util.subst_typ (subst_of_env config.environment) config.code}
        else match config.code.n with
            (* In all remaining cases, the stack should be empty *)
            | Typ_fun(bs, comp) -> 
              let binders, environment = sn_binders tcenv bs config.environment config.steps in
              let c2 = sncomp tcenv ({code=comp; environment=environment; stack=empty_stack keffect; steps=config.steps}) in
              {config with code=wk <| mk_Typ_fun(binders, c2.code)}

            | Typ_refine(x, t) -> 
              begin match sn_binders tcenv [v_binder x] config.environment config.steps with
                | [Inr x, _], env -> 
                  let c2 = sn tcenv ({code=t; environment=env; stack=empty_stack t.tk; steps=config.steps}) in
                  {config with code=wk <| mk_Typ_refine(x, c2.code)}
                | _ -> failwith "Impossible"
              end

            | Typ_meta(Meta_pattern(t, ps)) -> (* no reduction in patterns *)
              let c = sn tcenv ({config with code=t}) in
              {c with code=wk <| mk_Typ_meta'(Meta_pattern(c.code, ps))}
    
            | Typ_meta(Meta_named _)    
            | Typ_unknown
            | _ -> failwith (Util.format3 "(%s) Unexpected type (%s): %s" (Env.get_range tcenv |> Range.string_of_range) (Print.tag_of_typ config.code) (Print.typ_to_string config.code))
  end

and sn_binders tcenv binders env steps = 
 let rec aux out env = function 
    | (Inl a, imp)::rest -> 
       let c = snk tcenv ({code=a.sort; stack=empty_stack kun; steps=steps; environment=env}) in
       let a = {a with sort=c.code} in
       let env = TDummy a::env in
       aux ((Inl a, imp)::out) env rest

    | (Inr x, imp)::rest -> 
       let c = sn tcenv ({code=x.sort; stack=empty_stack x.sort.tk; steps=steps; environment=env}) in
       let x = {x with sort=c.code} in
       let env = VDummy x::env in 
       aux ((Inr x, imp)::out) env rest

    | [] -> List.rev out, env in
 aux [] env binders

and sn tcenv cfg = 
    sn_aux tcenv ({cfg with steps=Eta::cfg.steps})

and sncomp tcenv (cfg:config<comp>) : config<comp> = 
  let m = cfg.code in 
  match (compress_comp m).n with 
    | Rigid t -> 
      let c = sn tcenv (with_new_code t.tk cfg t) in
      (match c.code.n with
        | Typ_meta(Meta_comp c) -> sncomp tcenv (with_new_code keffect cfg c)
        | _ -> failwith "Impossible")
    | Comp ct -> 
      let ctconf = sncomp_typ tcenv (with_new_code keffect cfg ct) in
      {cfg with code=mk_Comp ctconf.code}
    | Total t -> 
      if List.contains DeltaComp cfg.steps 
      then sncomp tcenv <| with_new_code keffect cfg (mk_Comp <| comp_to_comp_typ (mk_Total t))
      else let t = sn tcenv (with_new_code t.tk cfg t) in
           with_new_code keffect cfg (mk_Total t.code)
    | Flex(u, t) -> 
      let tconf = sn tcenv (with_new_code t.tk cfg t) in 
      {cfg with code=mk_Flex(u, tconf.code)}

and sncomp_typ tcenv (cfg:config<comp_typ>) : config<comp_typ> = 
  let remake l r eargs = 
    let c = {effect_name=l; result_typ=r; effect_args=eargs; flags=cfg.code.flags} in
    {cfg with code=c} in
  let m = cfg.code in 
  let res = (sn tcenv (with_new_code m.result_typ.tk cfg m.result_typ)).code in
  let args = 
    if List.contains SNComp cfg.steps 
    then sn_args tcenv cfg.environment cfg.steps m.effect_args 
    else m.effect_args in 
  if not <| List.contains DeltaComp cfg.steps
  then remake m.effect_name res args
  else match Tc.Env.lookup_typ_abbrev tcenv m.effect_name with
        | None -> remake m.effect_name res args
        | Some t -> 
          let t = mk_Typ_app(t, (Inl res, false)::args) keffect res.pos in
          let c = sn tcenv (with_new_code keffect cfg t) in
          match c.code.n with
            | Typ_app({n=Typ_const fv}, (Inl res, _)::args) -> remake fv.v res args
            | _ ->  failwith (Util.format2 "Got a computation %s, normalized unexpectedly to %s" (Print.sli m.effect_name) (Print.typ_to_string c.code))
       
and sn_args tcenv env steps args = 
   args |> List.map (function 
     | Inl t, imp -> Inl <| (sn_aux tcenv ({code=t; stack=empty_stack t.tk; environment=env; steps=steps})).code, imp
     | Inr e, imp -> Inr <| (wne tcenv ({code=e; stack=empty_stack kun; environment=env; steps=steps})).code, imp)

and snk tcenv (cfg:config<knd>) : config<knd> =
  let w f = f cfg.code.pos in
  match (Util.compress_kind cfg.code).n with
    | Kind_delayed _ 
    | Kind_lam _ -> failwith "Impossible"
    | Kind_type
    | Kind_effect -> cfg
    | Kind_uvar(uv, args) -> 
      let args = sn_args tcenv cfg.environment (no_eta cfg.steps) args in
      {cfg with code=w <| mk_Kind_uvar(uv, args)}  
//    | Kind_abbrev(kabr, k) -> 
//      let c1 = snk tcenv ({cfg with code=k}) in
//      let args = sn_args tcenv cfg.environment (no_eta cfg.steps) (snd kabr) in
//      {cfg with code=w <| mk_Kind_abbrev((fst kabr, args), c1.code)}
    | Kind_abbrev(_, k) -> 
      snk tcenv ({cfg with code=k}) 
    | Kind_arrow(bs, k) -> 
      let bs, env = sn_binders tcenv bs cfg.environment cfg.steps in
      let c2 = snk tcenv ({code=k; steps=cfg.steps; environment=env; stack=empty_stack kun}) in
      let bs, rhs = match c2.code.n with 
        | Kind_arrow(bs', k) -> bs@bs', k
        | _ -> bs, c2.code in
      {cfg with code=w <| mk_Kind_arrow(bs, rhs)}
    | Kind_unknown -> 
      failwith "Impossible"

(* The type checker never attempts to reduce expressions itself; but still need to do substitutions *)
and wne tcenv (cfg:config<exp>) : config<exp> = 
  let e = compress_exp cfg.code in
  let w f = f cfg.code.tk cfg.code.pos in
  let config = with_new_code kun cfg e in
  match e.n with 
    | Exp_delayed _ -> failwith "Impossible"
    | Exp_fvar _ 
    | Exp_constant _
    | Exp_uvar _  -> config

    | Exp_meta(Meta_uvar_e_app(e, (uv,t))) ->
      let cfg = wne tcenv ({config with code=e}) in
      {cfg with code=mk_Exp_meta'(Meta_uvar_e_app(cfg.code, (uv,t))) cfg.code.tk cfg.code.pos}
 
    | Exp_bvar x -> 
      begin match config.environment |> Util.find_opt (function VDummy y -> bvar_eq x y | V (y, _, _) -> bvd_eq x.v y | _ -> false) with 
        | None -> config 
        | Some (VDummy x) -> {config with code=bvar_to_exp x}
        | Some (V(x, (vc, e), m)) -> 
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

    | Exp_app(e, args) ->
      let c1 = wne tcenv ({config with code=e}) in
      let args = sn_args tcenv config.environment config.steps args in
      {config with code=w <| mk_Exp_app(c1.code, args)} 
 
    | Exp_abs(bs, e) -> 
      let bs, _ = sn_binders tcenv bs config.environment config.steps in
      {config with code=w <| mk_Exp_abs(bs, e)}

    | Exp_match _
    | Exp_let  _ -> //TODO: not implemented yet
      config // failwith (Util.format1 "NYI: %s" (Print.exp_to_string e))
    | Exp_meta _ 
    | Exp_ascribed _ -> failwith "impossible"

(************************************************************************************)
(* External interface *)
(************************************************************************************)
let norm_kind steps tcenv k = 
  let c = snk tcenv ({code=k; environment=[]; stack=empty_stack kun; steps=steps}) in
  c.code

let norm_typ steps tcenv t = 
  let c = sn_aux tcenv ({code=t; environment=[]; stack=empty_stack t.tk; steps=steps}) in
  c.code

let whnf tcenv t = 
    let t = Util.compress_typ t in
    match t.n with 
        | Typ_fun _
        | Typ_refine _ -> t
        | Typ_btvar _
        | Typ_const _ 
        | Typ_uvar _
        | Typ_app({n=Typ_const _}, _)
        | Typ_app({n=Typ_btvar _}, _)
        | Typ_app({n=Typ_uvar _}, _) -> eta_expand tcenv t
        | _ -> norm_typ [WHNF;Beta;Eta] tcenv t

let rec comp_comp env c = 
    let c = Util.compress_comp c in
    match c.n with
    | Rigid t -> 
        (match (norm_typ [Beta] env t).n with
            | Typ_meta(Meta_comp c) -> comp_comp env c
            | _ -> failwith "Impossible")
    | _ -> c

let force_flex_comp (env:Tc.Env.env) (def:typ -> comp) (c:comp) =
    let c = comp_comp env c in
    match c.n with
        | Rigid _  -> failwith "Impossible"
        | Comp _
        | Total _ -> c 
        | Flex({n=Typ_meta(Meta_uvar_t_app(_, (u,k)))}, res_t) -> 
          let def = def res_t in
          let tdef = k |> close_for_kind (mk_Typ_meta(Meta_comp def)) in
          Unionfind.change u (Fixed tdef);
          def
        | Flex _ -> failwith "Impossible" 
let flex_to_ml env c = force_flex_comp env (fun res_t -> Util.ml_comp res_t (Env.get_range env)) c
let flex_to_total env c = force_flex_comp env mk_Total c

let rec weak_norm_comp env comp =
  let c = comp_to_comp_typ (flex_to_ml env comp) in
  match Tc.Env.lookup_typ_abbrev env c.effect_name with
    | None -> c
    | Some t -> 
      let t = mk_Typ_app(t, (targ c.result_typ)::c.effect_args) keffect comp.pos in
      let t = norm_typ [DeltaHard; WHNF] env t in
      match t.n with 
        | Typ_app({n=Typ_const eff}, (Inl res, _)::rest) ->
           {effect_name=eff.v;
            result_typ=res;
            effect_args=rest;
            flags=c.flags}

        | _ ->  failwith (Util.format2 "Got a computation %s which normalized unexpectedly to %s" (Print.sli c.effect_name) (Print.typ_to_string t))
      //let _ = printfn "Normalized %s\nto %s\n" (Print.comp_typ_to_string m) (Print.comp_typ_to_string n.code) in
     //check_sharing (Util.compress_typ tt0) (Util.compress_typ n.result_typ) "weak_norm_comp";
 
             
let norm_comp steps tcenv c = 
  let c = sncomp tcenv ({code=c; environment=[]; stack=empty_stack keffect; steps=steps}) in
  c.code

let normalize_kind tcenv k = 
  let steps = [Delta;Beta] in
  norm_kind steps tcenv k

let normalize_comp tcenv c = 
  let steps = [Delta;Beta;SNComp;DeltaComp] in
  norm_comp steps tcenv c

let normalize tcenv t = norm_typ [DeltaHard;Beta;Eta] tcenv t

