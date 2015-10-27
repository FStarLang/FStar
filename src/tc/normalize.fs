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

module FStar.Tc.Normalize

open FStar
open FStar.Tc
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Util
open FStar.Util
open FStar.Tc.Env


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
  | EtaArgs
  | Delta
  | DeltaHard
  | Beta
  | DeltaComp
  | Simplify
  | SNComp
  | Unmeta
  | Unlabel
and steps = list<step>

type config<'a> = {code:'a;
                   environment:environment;
                   stack:stack;
                   close:option<('a -> 'a)>;
                   steps:list<step>}
and environment = {
    context:list<env_entry>;//Tried using Util.smap<env_entry> and FStar.Util.map<env_entry>; lists are still the fastest by about 12.5% end-to-end time
    label_suffix:list<(option<bool> * Range.range)>
}
and stack = {
    args:list<(arg * environment)>;
}
and env_entry =
  | T of (btvdef * tclos)
  | V of (bvvdef * vclos)
and tclos = (typ * environment)
and vclos = (exp * environment)
and memo<'a> = ref<option<'a>>

let empty_env = {
    context=[];
    label_suffix=[]
}
let extend_env' env b = {env with context=b::env.context}
let extend_env env bindings = {env with context=List.append bindings env.context}
let lookup_env env key = env.context |> Util.find_opt (function
    | T(a, _) -> a.realname.idText=key
    | V(x, _) -> x.realname.idText=key)
let fold_env env f acc =
    List.fold_left (fun acc v -> match v with
        | T(a, _) -> f a.realname.idText v acc
        | V(x, _) -> f x.realname.idText v acc) acc env.context
let empty_stack = {
    args=[];
}

(* Explicit tail recursion for OCaml backend -- do not use List.collect! *)
let rec subst_of_env' env =
    fold_env env (fun _ v acc -> match v with
        | T (a, (t,env'))  ->
          Inl(a, Util.subst_typ (subst_of_env' env') t)::acc

        | V (x, (v,env')) ->
          Inr(x, Util.subst_exp (subst_of_env' env') v)::acc) []
let subst_of_env tcenv env = subst_of_env' env

let with_new_code c e = {
    code=e;
    environment=c.environment;
    stack=empty_stack;
    steps=c.steps;
    close=None
}

let rec eta_expand tcenv t =
    let k = Recheck.recompute_kind t |> Util.compress_kind in
    let rec aux t k = match k.n with
        | Kind_type
        | Kind_effect
        | Kind_uvar _ -> t
        | Kind_abbrev(_, k) -> aux t k
        | Kind_arrow(binders, k') ->
            begin match (unascribe_typ t).n with
                | Typ_lam(real, body) ->
                    let rec aux real expected = match real, expected with
                        | _::real, _::expected -> aux real expected
                        | [], [] -> (* no need to add any *) t
                        | _::_, [] -> (* too many binders ... ill-kinded *)
                          failwith "Ill-kinded type"
                        | [], more ->
                          let more, args = Util.args_of_binders more in
                          let body = mk_Typ_app(body, args) None body.pos in
                          mk_Typ_lam(binders@more, body) None body.pos in
                    aux real binders

                | _  ->
                    //if debug tcenv then printfn "(%s) eta-expanding %s" (Range.string_of_range t.pos) (Print.typ_to_string t);
                    let binders, args = Util.args_of_binders binders in
                    let body = mk_Typ_app(t, args) None t.pos in
                    mk_Typ_lam(binders, body) None t.pos
            end
        | Kind_lam _
        | Kind_delayed _ -> failwith "Impossible"
        | Kind_unknown -> failwith (Util.format2 "%s: Impossible: Kind_unknown: %s" (Tc.Env.get_range tcenv |> Range.string_of_range) (Print.typ_to_string t)) in
    aux t k

let is_var t = match Util.compress_typ t with
    | {n=Typ_btvar _} -> true
    | _ -> false

let rec eta_expand_exp (tcenv:Tc.Env.env) (e:exp) : exp =
    let t = Recheck.recompute_typ e |> Util.compress_typ in
    match t.n with
        | Typ_fun(bs, c) ->
            begin match (Util.compress_exp e).n with
                | Exp_abs(bs', body) ->
                    if (List.length bs = List.length bs')
                    then e
                    else failwith "NYI"
                | _ ->
                  let bs, args = Util.args_of_binders bs in
                  mk_Exp_abs(bs, mk_Exp_app(e, args) None e.pos) (Some t) e.pos
            end
        | _ -> e

let no_eta s = s |> List.filter (function Eta -> false | _ -> true)
let no_eta_cfg c = {c with steps=no_eta c.steps}
let whnf_only config = config.steps |> List.contains WHNF
let unmeta config = config.steps |> List.contains Unmeta
let unlabel config = unmeta config || config.steps |> List.contains Unlabel
let is_stack_empty config = match config.stack.args with
    | [] -> true
    | _ -> false
let has_eta cfg = cfg.steps |> List.contains Eta

let rec weak_norm_comp env comp =
  let c = comp_to_comp_typ comp in
  match Tc.Env.lookup_effect_abbrev env c.effect_name with
    | None -> c
    | Some (binders, cdef) ->
      //alpha-convert c first
      let binders' = List.map (function
        | Inl b, imp -> Inl (Util.freshen_bvar b), imp
        | Inr b, imp -> Inr (Util.freshen_bvar b), imp) binders in
      let subst = Util.subst_of_list binders (Util.args_of_binders binders' |> snd) in
      let cdef = Util.subst_comp subst cdef in
      let subst = subst_of_list binders' (targ c.result_typ::c.effect_args) in
      let c1 = Util.subst_comp subst cdef in
      let c = {Util.comp_to_comp_typ c1 with flags=c.flags} |> mk_Comp in
      weak_norm_comp env c

let t_config code env steps =
    {close=None;
     code=code;
     environment=env;
     steps=steps;
     stack=empty_stack}
let k_config code env steps =
    {close=None;
     code=code;
     environment=env;
     steps=steps;
     stack=empty_stack}
let e_config code env steps =
    {close=None;
     code=code;
     environment=env;
     steps=steps;
     stack=empty_stack}
let c_config code env steps =
    {close=None;
     code=code;
     environment=env;
     steps=steps;
     stack=empty_stack
     }

let close_with_config = //: config<'a> -> ('a -> 'a) -> option<('a -> 'a)> =
  fun cfg f -> Some (fun t ->
                       let t = f t in
                       match cfg.close with
                        | None -> t
                        | Some g -> g t)

let rec is_head_symbol t = match (compress_typ t).n with
    | Typ_const _
    | Typ_lam _ -> true
    | Typ_meta(Meta_refresh_label(t, _, _)) -> is_head_symbol t
    | _ -> false

let simplify_then_apply steps head args pos =
    let fallback () = mk_Typ_app(head, args) None pos in
    let simp_t t = match t.n with
        | Typ_const fv when lid_equals fv.v Const.true_lid ->  Some true
        | Typ_const fv when lid_equals fv.v Const.false_lid -> Some false
        | _ -> None in
    let simplify arg = match fst arg with
        | Inl t -> (simp_t t, arg)
        | _ -> (None, arg) in
    if not <| List.contains Simplify steps
    then fallback()
    else match head.n with
            | Typ_const fv ->
              if lid_equals fv.v Const.and_lid
              then match args |> List.map simplify with
                     | [(Some true, _); (_, (Inl arg, _))]
                     | [(_, (Inl arg, _)); (Some true, _)] -> arg
                     | [(Some false, _); _]
                     | [_; (Some false, _)] -> Util.t_false
                     | _ -> fallback()
              else if lid_equals fv.v Const.or_lid
              then match args |> List.map simplify with
                     | [(Some true, _); _]
                     | [_; (Some true, _)] -> Util.t_true
                     | [(Some false, _); (_, (Inl arg, _))]
                     | [(_, (Inl arg, _)); (Some false, _)] -> arg
                     | _ -> fallback()
              else if lid_equals fv.v Const.imp_lid
              then match args |> List.map simplify with
                     | [_; (Some true, _)]
                     | [(Some false, _); _] -> Util.t_true
                     | [(Some true, _); (_, (Inl arg, _))] -> arg
                     | _ -> fallback()
              else if lid_equals fv.v Const.not_lid
              then match args |> List.map simplify with
                     | [(Some true, _)] -> Util.t_false
                     | [(Some false, _)] -> Util.t_true
                     | _ -> fallback ()
              else if  lid_equals fv.v Const.forall_lid
                    || lid_equals fv.v Const.allTyp_lid
                    || lid_equals fv.v Const.exists_lid
                    || lid_equals fv.v Const.exTyp_lid
              then match args with
                     | [(Inl t, _)]
                     | [_; (Inl t, _)] ->
                       begin match (Util.compress_typ t).n with
                                | Typ_lam([_], body) ->
                                   (match simp_t body with
                                        | Some true -> Util.t_true
                                        | Some false -> Util.t_false
                                        | _ -> fallback())
                                | _ -> fallback()
                       end
                    | _ -> fallback()
              else fallback()
            | _ -> fallback()

let rec sn_delay tcenv (cfg:config<typ>) : config<typ> =
    let aux () = (sn tcenv cfg).code in
    let t = mk_Typ_delayed' (Inr aux) None cfg.code.pos in
    {cfg with code=t; stack=empty_stack}

and sn tcenv (cfg:config<typ>) : config<typ> =
    let rebuild config  =
        let rebuild_stack config =
            if is_stack_empty config then config
            else let s' = if List.contains EtaArgs config.steps
                          then config.steps
                          else no_eta config.steps in
                 let args = config.stack.args |> List.map (function
                        | (Inl t, imp), env -> Inl <| (sn tcenv (t_config t env s')).code, imp
                        | (Inr v, imp), env -> Inr <| (wne tcenv (e_config v env s')).code, imp) in
                 let t = simplify_then_apply config.steps config.code args config.code.pos in
                 {config with code=t; stack=empty_stack} in

        let config = rebuild_stack config in
        let t = match config.close with
            | None -> config.code
            | Some f -> f config.code in
        if has_eta config
        then {config with code=eta_expand tcenv t}
        else {config with code=t} in


  let wk f = match !cfg.code.tk with
    | Some ({n=Kind_type}) -> f (Some ktype) cfg.code.pos
    | _ -> f None cfg.code.pos in

  let config = {cfg with code=Util.compress_typ cfg.code} in
  begin match config.code.n with
    | Typ_delayed _ -> failwith "Impossible"

    | Typ_uvar _ ->
      rebuild config

    | Typ_const fv ->
      if config.steps |> List.contains DeltaHard
        || (config.steps |> List.contains Delta && not <| is_stack_empty config) //delta only if reduction is blocked
      then match Tc.Env.lookup_typ_abbrev tcenv fv.v with
          | None -> rebuild config
          | Some t -> (* delta(); *)
            sn tcenv ({config with code=t})
      else rebuild config

    | Typ_btvar a ->
      begin match lookup_env config.environment a.v.realname.idText with
        | None -> rebuild config (* possible for an open term *)
        | Some (T(_, (t,e))) -> sn tcenv ({config with code=t; environment=e})
        | _ -> failwith "Impossible: expected a type"
      end

    | Typ_app(head, args) ->
      let args = List.fold_right (fun a out -> (a, config.environment)::out) args config.stack.args in
      let stack = {config.stack with args=args} in
      sn tcenv ({config with code=head; stack=stack})

    | Typ_lam(binders, t2) ->
      begin match config.stack.args with
        | [] ->
          (* Need to substitute under lambdas even if we don't want a full normal form *)
          let binders, environment = sn_binders tcenv binders config.environment config.steps in
          let mk_lam t =
            let lam = wk <| mk_Typ_lam(binders, t) in
            match cfg.close with
                | None -> lam
                | Some f -> f lam in
          let t2_cfg = sn_delay tcenv ({code=t2;
                                        close=None;
                                        stack=empty_stack;
                                        environment=environment;
                                        steps=no_eta config.steps}) in
          {t2_cfg with code=mk_lam t2_cfg.code}

        | args -> (* beta *)
          let rec beta env_entries binders args = match binders, args with
            | [], _ -> (* fully applied, or more actuals (extra currying) *)
                let env = extend_env config.environment env_entries in
                sn tcenv ({config with code=t2; environment=env; stack={config.stack with args=args}})

            | _, [] -> (* more formals (partially applied) *)
                let t = mk_Typ_lam(binders, t2) None t2.pos in
                let env = extend_env config.environment env_entries in
                sn tcenv ({config with code=t; environment=env; stack=empty_stack})

            | formal::rest, actual::rest' ->
                let m = match formal, actual with
                | (Inl a, _), ((Inl t, _), env) -> T(a.v, (t,env))
                | (Inr x, _), ((Inr v, _), env) -> V(x.v, (v,env))
                | _ -> failwith (Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n"
                                            (Range.string_of_range (argpos <| fst actual))
                                            (Print.binder_to_string formal)
                                            (Print.arg_to_string <| fst actual)) in
                beta (m::env_entries) rest rest' in


          beta [] binders args
      end

    | Typ_ascribed(t, _) ->
      sn tcenv ({config with code=t})

    | _ ->
        match config.code.n with
                (* In all remaining cases, the stack should be empty *)
                | Typ_fun(bs, comp) ->
                  let binders, environment = sn_binders tcenv bs config.environment config.steps in
                  let c2 = sncomp tcenv (c_config comp environment config.steps) in
                  {config with code=wk <| mk_Typ_fun(binders, c2.code)}

                | Typ_refine(x, t) ->
                  begin match sn_binders tcenv [v_binder x] config.environment config.steps with
                    | [(Inr x, _)], env ->
                      let refine t = wk <| mk_Typ_refine(x, t) in
                      sn tcenv ({close=close_with_config config refine;
                                 code=t;
                                 environment=env;
                                 stack=empty_stack;
                                 steps=config.steps})
                    | _ -> failwith "Impossible"
                  end

                | Typ_meta(Meta_pattern(t, ps)) -> (* no reduction in patterns *)
                  if unmeta config then
                    sn tcenv ({config with code=t})
                  else
                    let pat t =
                        let ps = ps |> List.map (sn_args true tcenv config.environment config.steps) in
                        wk <| mk_Typ_meta'(Meta_pattern(t, ps)) in
                    sn tcenv ({config with code=t; close=close_with_config config pat})

                | Typ_meta(Meta_labeled(t, l, r, b)) ->
                  if unlabel config then
                    sn tcenv ({config with code=t})
                  else
                    let lab t = match t.n with
                        | Typ_const fv when (lid_equals fv.v Const.true_lid && config.steps |> List.contains Simplify) -> t
                        | _ ->
                          match config.environment.label_suffix with
                              | (b', sfx)::_ ->
                                  if b'=None || Some b=b'
                                  then (if Tc.Env.debug tcenv Options.Low then Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l (Range.string_of_range sfx); t)
                                  else (if Tc.Env.debug tcenv Options.Low then Util.fprint1 "Normalizer refreshing label: %s\n" (Range.string_of_range sfx);
                                        wk <| mk_Typ_meta'(Meta_labeled(t, l, sfx, b)))
                              | _ -> wk <| mk_Typ_meta'(Meta_labeled(t, l, r, b))  in
                    sn tcenv ({config with code=t; close=close_with_config config lab})

                | Typ_meta(Meta_refresh_label(t, b, r)) ->
                  if unmeta config then
                    sn tcenv ({config with code=t})
                  else
                   let sfx = match b with Some false -> r | _ -> dummyRange in
                   let config = {config with code=t; environment={config.environment with label_suffix=(b, sfx)::config.environment.label_suffix}} in
                   sn tcenv config

                | Typ_meta(Meta_slack_formula(t1, t2, flag)) ->
                  if !flag
                  then sn tcenv ({config with code=Util.mk_conj t1 t2})
                  else let c1 = sn tcenv (t_config t1 config.environment config.steps) in
                       let c2 = sn tcenv (t_config t2 config.environment config.steps) in
                       rebuild ({config with code=mk_Typ_meta (Meta_slack_formula(c1.code, c2.code, flag))})

                | Typ_meta(Meta_named _)
                | Typ_unknown
                | _ -> failwith (Util.format3 "(%s) Unexpected type (%s): %s" (Env.get_range tcenv |> Range.string_of_range) (Print.tag_of_typ config.code) (Print.typ_to_string config.code))
  end

and sn_binders tcenv binders env steps =
 let rec aux out env = function
    | (Inl a, imp)::rest ->
       let c = snk tcenv (k_config a.sort env steps) in
       let b = Util.bvd_to_bvar_s (Util.freshen_bvd a.v) c.code in
       let btyp = Util.btvar_to_typ b in
       let b_for_a = T(a.v, (btyp, empty_env)) in
       aux ((Inl b, imp)::out) (extend_env' env b_for_a) rest

    | (Inr x, imp)::rest ->
       let c = sn_delay tcenv (t_config x.sort env steps) in
       let y = Util.bvd_to_bvar_s (Util.freshen_bvd x.v) c.code in
       let yexp = Util.bvar_to_exp y in
       let y_for_x = V(x.v, (yexp, empty_env)) in
       aux ((Inr y, imp)::out) (extend_env' env y_for_x) rest

    | [] -> List.rev out, env in
 aux [] env binders

and sncomp tcenv (cfg:config<comp>) : config<comp> =
  let m = cfg.code in
  match m.n with
    | Comp ct ->
      let ctconf = sncomp_typ tcenv (with_new_code cfg ct) in
      {cfg with code=mk_Comp ctconf.code}

    | Total t ->
      if List.contains DeltaComp cfg.steps
      then sncomp tcenv <| with_new_code cfg (mk_Comp <| comp_to_comp_typ (mk_Total t))
      else let t = sn tcenv (with_new_code cfg t) in
           with_new_code cfg (mk_Total t.code)

and sncomp_typ tcenv (cfg:config<comp_typ>) : config<comp_typ> =
  let m = cfg.code in
  let norm () =
    let remake l r eargs flags =
        let c = {effect_name=l; result_typ=r; effect_args=eargs; flags=flags} in
        {cfg with code=c} in
    let res = (sn tcenv (with_new_code cfg m.result_typ)).code in
    let sn_flags flags =
    flags |> List.map (function
        | DECREASES e ->
            let e = (wne tcenv (e_config e cfg.environment cfg.steps)).code in
            DECREASES e
        | f -> f) in
    let flags, args = sn_flags m.flags, sn_args true tcenv cfg.environment cfg.steps m.effect_args in
    remake m.effect_name res args flags  in

  if List.contains DeltaComp cfg.steps
  then match Tc.Env.lookup_effect_abbrev tcenv m.effect_name with
        | Some _ ->
            let c = weak_norm_comp tcenv (mk_Comp m) in
            sncomp_typ tcenv ({cfg with code=c})
        | _ -> norm()
  else norm()

and sn_args delay tcenv env steps (args:args) =
   args |> List.map (function
     | Inl t, imp when delay -> Inl <| (sn_delay tcenv (t_config t env steps)).code, imp
     | Inl t, imp -> Inl <| (sn tcenv (t_config t env steps)).code, imp
     | Inr e, imp -> Inr <| (wne tcenv (e_config e env steps)).code, imp)

and snk tcenv (cfg:config<knd>) : config<knd> =
  let w f = f cfg.code.pos in
  match (Util.compress_kind cfg.code).n with
    | Kind_delayed _
    | Kind_lam _ -> failwith "Impossible"
    | Kind_type
    | Kind_effect -> cfg
    | Kind_uvar(uv, args) ->
      let args = sn_args false tcenv cfg.environment (no_eta cfg.steps) args in
      {cfg with code=w <| mk_Kind_uvar(uv, args)}
    | Kind_abbrev((l, args), {n=Kind_unknown}) ->
      let (_, binders, body) = Tc.Env.lookup_kind_abbrev tcenv l in
      let subst = Util.subst_of_list binders args in
      snk tcenv ({cfg with code=Util.subst_kind subst body})
    | Kind_abbrev(_, k) ->
      snk tcenv ({cfg with code=k})
    | Kind_arrow(bs, k) ->
      let bs, env = sn_binders tcenv bs cfg.environment cfg.steps in
      let c2 = snk tcenv (k_config k env cfg.steps) in
      let bs, rhs = match c2.code.n with
        | Kind_arrow(bs', k) -> bs@bs', k
        | _ -> bs, c2.code in
      {cfg with code=w <| mk_Kind_arrow(bs, rhs)}
    | Kind_unknown ->
      failwith "Impossible"

and wne tcenv (cfg:config<exp>) : config<exp> =
  let e = compress_exp cfg.code in
  let config = {cfg with code = e} in
   let rebuild config  =
        if is_stack_empty config then config
        else let s' =
                if List.contains EtaArgs config.steps
                then config.steps
                else no_eta config.steps in
             let args =
                 config.stack.args |> List.map (function
                    | (Inl t, imp), env -> Inl <| (sn  tcenv (t_config t env s')).code, imp
                    | (Inr v, imp), env -> Inr <| (wne tcenv (e_config v env s')).code, imp) in
             {config with code=mk_Exp_app(config.code, args) None config.code.pos; stack=empty_stack} in

  match e.n with
    | Exp_delayed _ -> failwith "Impossible"

    | Exp_fvar _
    | Exp_constant _
    | Exp_uvar _  -> config |> rebuild

    | Exp_bvar x ->
      begin match lookup_env config.environment x.v.realname.idText with
        | None -> config  |> rebuild (* possible for open terms, or for let-rec bound names *)
        | Some (V(_, (vc, env))) -> wne tcenv ({config with code=vc; environment=env})
        | _ -> failwith "Impossible: ill-typed term"
      end

    | Exp_app(head, args) ->
      let args = List.fold_right (fun a out -> (a, config.environment)::out) args config.stack.args in
      let stack = {config.stack with args=args} in
      wne tcenv ({config with code=head; stack=stack})

    | Exp_abs(binders, body) ->
      let rec beta entries binders args = match binders, args with
        | [], _ -> (* fully applied, or more actuals (extra currying) *)
            let env = extend_env config.environment entries in
            wne tcenv ({config with code=body;
                                    environment=env;
                                    stack={config.stack with args=args}})

        | _, [] -> (* more formals (partially applied) *)
            let env = extend_env config.environment entries in
            let binders, env = sn_binders tcenv binders env config.steps in
            let mk_abs t = mk_Exp_abs(binders, t) None body.pos in
            let c = wne tcenv ({config with code=body;
                                            environment=env;
                                            stack={config.stack with args=[]};
                                            steps=no_eta config.steps}) in
            {c with code=mk_abs c.code}

        | formal::rest, actual::rest' ->
            let m = match formal, actual with
            | (Inl a, _), ((Inl t, _), env) -> T(a.v, (t,env))
            | (Inr x, _), ((Inr v, _), env) -> V(x.v, (v,env))
            | _ -> failwith (Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n"
                                        (Range.string_of_range (argpos <| fst actual))
                                        (Print.binder_to_string formal)
                                        (Print.arg_to_string <| fst actual)) in
            beta (m::entries) rest rest' in

      beta [] binders config.stack.args

    | Exp_match(e1, eqns) ->
      let c_e1 = wne tcenv ({config with code=e1; stack=empty_stack}) in
      let wn_eqn (pat, w, body) =
        let rec pat_vars p = match p.v with
            | Pat_disj [] -> []
            | Pat_disj (p::_) -> pat_vars p
            | Pat_cons (_, _, pats) -> List.collect (fun (x, _) -> pat_vars x) pats
            | Pat_var x  -> [v_binder x]
            | Pat_tvar a -> [t_binder a]
            | Pat_wild _
            | Pat_twild _
            | Pat_constant _
            | Pat_dot_term _
            | Pat_dot_typ _ -> [] in

        let vars = pat_vars pat in //Not alpha-converting patterns. TODO: OK?
        let norm_bvvar x =
            let t = sn tcenv (t_config x.sort config.environment config.steps) in
            {x with sort=t.code} in

        let norm_btvar a =
            let k = snk tcenv (k_config a.sort config.environment config.steps) in
            {a with sort=k.code} in

        let rec norm_pat p = match p.v with
            | Pat_disj pats -> withinfo (Pat_disj (List.map norm_pat pats)) None p.p

            | Pat_cons (fv, q, pats) -> withinfo (Pat_cons(fv, q, List.map (fun (x, i) -> norm_pat x, i) pats)) None p.p

            | Pat_var x ->
              withinfo (Pat_var(norm_bvvar x)) None p.p

            | Pat_tvar a ->
              withinfo (Pat_tvar (norm_btvar a)) None p.p

            | Pat_wild x  ->
              withinfo (Pat_wild(norm_bvvar x)) None p.p

            | Pat_twild a ->
              withinfo (Pat_twild (norm_btvar a)) None p.p

            | Pat_constant _ -> p

            | Pat_dot_term(x, e) ->
              let e = wne tcenv (e_config e config.environment config.steps) in
              withinfo (Pat_dot_term(norm_bvvar x, e.code)) None p.p

            | Pat_dot_typ(a, t) ->
              let t = sn tcenv (t_config t config.environment config.steps) in
              withinfo (Pat_dot_typ(norm_btvar a, t.code)) None p.p in

        let env_entries = List.fold_left (fun entries b -> match fst b with
            | Inl a ->
              let atyp = Util.btvar_to_typ a in
              T(a.v, (atyp,empty_env))::entries

            | Inr x ->
              let xexp = Util.bvar_to_exp x in
              V(x.v, (xexp,empty_env))::entries) [] vars in
        let env = extend_env config.environment env_entries in
        let w = match w with
            | None -> None
            | Some w ->
              let c_w = wne tcenv ({config with code=w; environment=env; stack=empty_stack}) in
              Some (c_w.code) in
        let c_body = wne tcenv ({config with code=body; environment=env; stack=empty_stack}) in
        (norm_pat pat, w, c_body.code) in
      let eqns = List.map wn_eqn eqns in
      let e = mk_Exp_match(c_e1.code, eqns) None e.pos in
      {config with code=e} |> rebuild

    | Exp_let((is_rec, lbs), body) ->
      let env, lbs = lbs |> List.fold_left (fun (env, lbs) ({lbname=x; lbeff=eff; lbtyp=t; lbdef=e}) ->
        let c = wne tcenv ({config with code=e; stack=empty_stack}) in
        let t = sn tcenv (t_config t config.environment config.steps) in
        let y, env = match x with
            | Inl x ->
              let y = Util.bvd_to_bvar_s (if is_rec then x else Util.freshen_bvd x) t.code in
              let yexp = Util.bvar_to_exp y in
              let y_for_x = V(x, (yexp, empty_env)) in
              Inl y.v, extend_env' env y_for_x
            | _ -> x, env in
        env, mk_lb (y, eff, t.code, c.code)::lbs) (config.environment, []) in
      let lbs = List.rev lbs in
      let c_body = wne tcenv ({config with code=body; stack=empty_stack; environment=env}) in
      let e = mk_Exp_let((is_rec, lbs), c_body.code) None e.pos in
      {config with code=e} |> rebuild

    | Exp_ascribed (e, t, l) ->
      let c = wne tcenv ({config with code=e}) in
      if is_stack_empty config
      then let t = sn tcenv (t_config t config.environment config.steps) in
           rebuild ({config with code=mk_Exp_ascribed(c.code, t.code, l) None e.pos})
      else c

    | Exp_meta(Meta_desugared(e, info)) ->
      let c = wne tcenv ({config with code=e}) in
      if is_stack_empty config
      then rebuild ({config with code=mk_Exp_meta(Meta_desugared(c.code, info))})
      else c

(************************************************************************************)
(* External interface *)
(************************************************************************************)
let norm_kind steps tcenv k =
  let c = snk tcenv (k_config k empty_env steps) in
  Util.compress_kind c.code

let norm_typ steps tcenv t =
  let c = sn tcenv (t_config t empty_env steps) in
  c.code

let norm_exp steps tcenv e =
  let c = wne tcenv (e_config e empty_env steps) in
  c.code

let norm_sigelt tcenv = function
    | Sig_let(lbs, r, l, b) ->
      let e = mk_Exp_let(lbs, mk_Exp_constant(Syntax.Const_unit) None r) None r in
      let e = norm_exp [Beta] tcenv e in
      begin match e.n with
        | Exp_let(lbs, _) -> Sig_let(lbs, r, l, b)
        | _ -> failwith "Impossible"
      end
    | s -> s

let whnf tcenv t =
    let t = Util.compress_typ t in
    match t.n with
        | Typ_fun _
        | Typ_refine _ -> t
        | Typ_btvar _
        | Typ_const _
        | Typ_uvar _
        | Typ_app({n=Typ_const _}, _)
        | Typ_app({n=Typ_btvar _}, _) -> eta_expand tcenv t |> Util.compress_typ
        | Typ_app({n=Typ_uvar _}, _)
        | _ -> norm_typ [WHNF;Beta;Eta] tcenv t

let norm_comp steps tcenv c =
  let c = sncomp tcenv (c_config c empty_env steps) in
  c.code

let normalize_kind tcenv k =
  let steps = [Eta;Delta;Beta] in
  norm_kind steps tcenv k

let normalize_comp tcenv c =
  let steps = [Eta;Delta;Beta;SNComp;DeltaComp] in
  norm_comp steps tcenv c

let normalize tcenv t = norm_typ [DeltaHard;Beta;Eta] tcenv t

(* Functions for normalization and printing *)
let exp_norm_to_string tcenv e =
  Print.exp_to_string (norm_exp [Beta;SNComp;Unmeta] tcenv e)

let typ_norm_to_string tcenv t =
  Print.typ_to_string (norm_typ [Beta;SNComp;Unmeta] tcenv t)

let kind_norm_to_string tcenv k =
  Print.kind_to_string (norm_kind [Beta;SNComp;Unmeta] tcenv k)

let formula_norm_to_string tcenv f =
  Print.formula_to_string (norm_typ [Beta;SNComp;Unmeta] tcenv f)

let comp_typ_norm_to_string tcenv c =
  Print.comp_typ_to_string (norm_comp [Beta;SNComp;Unmeta] tcenv c)

let normalize_refinement env t0 =
   let t = norm_typ [Beta; WHNF; DeltaHard] env t0 in
   let rec aux t =
    let t = Util.compress_typ t in
    match t.n with
       | Typ_refine(x, phi) ->
            let t0 = aux x.sort in
            begin match t0.n with
              | Typ_refine(y, phi1) ->
                mk_Typ_refine(y, Util.mk_conj phi1 (Util.subst_typ [Inr(x.v, Util.bvar_to_exp y)] phi)) (Some ktype) t0.pos
              | _ -> t
            end
       | _ -> t in
   aux t
