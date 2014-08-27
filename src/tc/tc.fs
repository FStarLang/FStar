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
module Microsoft.FStar.Tc.Tc

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Tc.Rel

let syn' env k = syn (Tc.Env.get_range env) k
let log env = !Options.log_types && not(lid_equals Const.prims_lid (Env.current_module env))
let rng env = Tc.Env.get_range env
let instantiate_both env = {env with Env.instantiate_targs=true; Env.instantiate_vargs=true}

let maybe_push_binding env = function
  | Inl(Some a, k) ->
    let b = Tc.Env.Binding_typ(a, k) in
    Env.push_local_binding env b, [b]
  | Inr(Some x, t) -> 
    let b = Tc.Env.Binding_var(x, t) in
    Env.push_local_binding env b, [b]
  | _ -> env, []

let maybe_make_subst = function 
  | Inl(Some a, t) -> [Inl(a,t)]
  | Inr(Some x, e) -> [Inr(x,e)]
  | _ -> []

let maybe_extend_subst s = function
  | Inl(Some a, t) -> extend_subst (Inl(a,t)) s
  | Inr(Some x, e) -> extend_subst (Inr(x,e)) s
  | _ -> s

let value_check_expected_typ env e tc : exp * comp =
  let c = match tc with 
    | Inl t -> if Util.is_function_typ t
               then mk_Total t
               else Tc.Util.return_value env t e
    | Inr c -> c in
  let t = Util.comp_result c in
  match Env.expected_typ env with 
   | None -> e, c
   | Some t' -> 
     let e, g = Tc.Util.check_and_ascribe env e t t' in
     let c = Tc.Util.strengthen_precondition env c g in
     e, Util.set_result_typ c t'

let comp_check_expected_typ env e c : exp * comp = 
  match Env.expected_typ env with 
   | None -> e, c
   | Some t -> Tc.Util.weaken_result_typ env e c t

let check_expected_effect env (copt:option<comp>) (e, c) : exp * comp * guard = 
  match copt with 
    | None -> e, c, Trivial
    | Some c' -> Tc.Util.check_comp env e c c' 
    
let no_guard env (te, kt, f) = match f with
  | Trivial -> te, kt
  | NonTrivial f -> raise (Error(Tc.Errors.unexpected_non_trivial_precondition_on_term f, Env.get_range env)) 

let binding_of_lb x t = match x with 
  | Inl bvd -> Env.Binding_var(bvd, t)
  | Inr lid -> Env.Binding_lid(lid, t)

let rec tc_kind env k : knd * guard = 
  let k = Util.compress_kind k in 
  let w f = f k.pos in
  match k.n with
  | Kind_lam _ 
  | Kind_delayed _ -> failwith "impossible"

  | Kind_type
  | Kind_effect -> k, Trivial
  | Kind_uvar (u, args) -> 
    let args = args |> List.map (function 
        | Inl t -> Inl(tc_typ_trivial env t |> fst)
        | Inr e -> Inr(let e, _, _ = tc_total_exp env e in e)) in
    w <| mk_Kind_uvar(u, args), Trivial //TODO: collect up formulae?

  | Kind_abbrev(kabr, k) -> 
    let k, f = tc_kind env k in 
    let kabr = (fst kabr, snd kabr |> List.map (function 
        | Inl t -> Inl(tc_typ_trivial env t |> fst)
        | Inr e -> Inr(let e, _, _ = tc_total_exp env e in e))) in
    w <| mk_Kind_abbrev(kabr, k), f

  | Kind_tcon (aopt, k1, k2, imp) -> 
    let k1, f1 = tc_kind env k1 in 
    let env', bindings = maybe_push_binding env (Inl(aopt, k1)) in
    let k2, f2 = tc_kind env' k2 in
    let f2 = Tc.Util.close_guard bindings f2 in
    w <| mk_Kind_tcon(aopt, k1, k2, imp), Rel.conj_guard f1 f2

  | Kind_dcon (xopt, t1, k2, imp) ->
    let t1, _, f1 = tc_typ env t1 in
    let env', bindings = maybe_push_binding env (Inr(xopt, t1)) in
    let k2, f2 = tc_kind env' k2 in
    let f2 = Tc.Util.close_guard bindings f2 in
    w <| mk_Kind_dcon(xopt, t1, k2, imp), Rel.conj_guard f1 f2

  | Kind_unknown -> 
    Tc.Util.new_kvar env, Trivial

and tc_comp env c = 
  let c = Normalize.comp_comp env c in
  match c.n with 
    | Flex(u, t) -> 
      let t, g = tc_typ_check env t ktype in
      let u, _ = tc_typ_check env u (mk_Kind_tcon(None, ktype, keffect, false) t.pos) in
      mk_Flex(u, t), g

    | Total t -> 
      let t, g = tc_typ_check env t ktype in
      mk_Total t, g

    | Comp ct -> 
      let ct, g = tc_comp_typ env ct in 
      mk_Comp ct, g

    | Rigid _
    | Flex _ -> failwith "Impossible"

    
and tc_comp_typ env c : comp_typ * guard = 
  let keff = Tc.Env.lookup_typ_lid env c.effect_name in 
  let result, f0 = tc_typ_check env c.result_typ ktype in 
  let k, subst = match keff.n with 
    | Kind_tcon(Some a, {n=Kind_type}, k, _) -> k, [Inl(a, result)]  
    | _ -> raise (Error(Tc.Errors.ill_kinded_effect c.effect_name keff, range_of_lid c.effect_name)) in
  let rec tc_args subst k args : list<either<typ,exp>> * guard = 
    match k.n, args with 
      | Kind_tcon(aopt, ka, k, _), Inl t::rest -> 
        let ka = Util.subst_kind subst ka in 
        let t, f = tc_typ_check env t ka in
        let subst = maybe_extend_subst subst <| Inl(aopt, t) in
        let rest, frest = tc_args subst k rest in
        Inl t::rest, Rel.conj_guard f frest
      | Kind_dcon(xopt, t, k, _), Inr e::rest -> 
        let t = Util.subst_typ subst t in
        let e, _, f = tc_total_exp (Tc.Env.set_expected_typ env t) e in
        let subst = maybe_extend_subst subst <| Inr(xopt, e) in 
        let rest, frest = tc_args subst k rest in
        Inr e::rest, Rel.conj_guard f frest 
      | Kind_effect, [] -> [], Trivial 
      | _, _ -> raise (Error(Tc.Errors.ill_kinded_effect c.effect_name k, range_of_lid c.effect_name)) in
  let args, f = tc_args (mk_subst subst) k c.effect_args in 
  {c with 
      result_typ=result;
      effect_args=args}, Rel.conj_guard f0 f

and tc_typ env (t:typ) : typ * knd * guard = 
  let env = Tc.Env.set_range env t.pos in
  let w k = syn t.pos k in
  match t.n with 
  | Typ_delayed _ -> 
    tc_typ env (compress_typ t) 
  
  | Typ_btvar a -> 
    let k = Env.lookup_btvar env a in
    w k <| mk_Typ_btvar a, k, Trivial

  | Typ_const i when (lid_equals i.v Const.allTyp_lid || lid_equals i.v Const.exTyp_lid) -> 
    (* Special treatment for ForallTyp and ExistsTyp, giving them polymorphic kinds *)
    let k = Tc.Util.new_kvar env in
    let qk = mk_Kind_tcon(None, mk_Kind_tcon(None, k, ktype, false) t.pos, ktype, false) t.pos in
    {t with tk=qk}, qk, Trivial 
    
  | Typ_const i -> 
    let k = Env.lookup_typ_lid env i.v in 
    {t with tk=k}, k, Trivial
     
  | Typ_fun(xopt, t1, cod, imp) -> 
    let t1, f1 = tc_typ_check env t1 ktype in
    let env', bindings = maybe_push_binding env <| Inr(xopt, t1) in
    let cod, f2 = tc_comp env' cod in
    w ktype <| mk_Typ_fun(xopt, t1, cod, imp), ktype, Rel.conj_guard f1 (Tc.Util.close_guard bindings f2)

  | Typ_univ(a, k1, cod) -> 
    let k1, f1 = tc_kind env k1 in 
    let env', bindings = maybe_push_binding env <| Inl(Some a, k1) in
    let cod, f2 = tc_comp env' cod in 
    w ktype <| mk_Typ_univ(a, k1, cod), ktype, Rel.conj_guard f1 (Tc.Util.close_guard bindings f2) 

  | Typ_refine(x, t1, t2) -> 
    let t1, f1 = tc_typ_check env t1 ktype in
    let env', bindings = maybe_push_binding env <| Inr(Some x, t1) in
    let t2, f2 = tc_typ_check env' t2 ktype in
    w ktype <| mk_Typ_refine(x, t1, t2), ktype, Rel.conj_guard f1 (Tc.Util.close_guard bindings f2)

  | Typ_app(t1, t2, imp) -> 
    let t1, k1, f1 = tc_typ env t1 in 
    let aopt, karg, kres, t1 = match Tc.Util.destruct_tcon_kind env k1 t1 imp with 
      | {n=Kind_tcon(aopt, karg, kres, _)}, t1 -> aopt, karg, kres, t1
      | _ -> failwith "impossible" in
    let t2, f2 = tc_typ_check env t2 karg in
    let k2 = Util.subst_kind' (maybe_make_subst <| Inl(aopt, t2)) kres in
    w k2 <| mk_Typ_app(t1, t2, imp), k2, Rel.conj_guard f1 f2
    
  | Typ_dep(t1, e1, imp) -> 
    let t1, k1, f1 = tc_typ env t1 in
    if debug env then printfn "Kind is %s" (Print.kind_to_string k1);
    let xopt, targ, kres, t1' = match Tc.Util.destruct_dcon_kind env k1 t1 imp with 
      | {n=Kind_dcon(xopt, targ, kres, _)}, t1 -> xopt, targ, kres, t1
      | _ -> failwith "impossible" in
    if debug env then printfn "Setting expected type to %s : %s" (Print.typ_to_string targ) (Print.kind_to_string targ.tk);
    let e1, _, f2 = tc_total_exp (Env.set_expected_typ env targ) e1 in
    let k2 = Util.subst_kind' (maybe_make_subst <| Inr(xopt, e1)) kres in
    w k2 <| mk_Typ_dep(t1, e1, imp), k2, Rel.conj_guard f1 f2
  
  | Typ_lam(x, t1, t2) -> 
    let t1, k1, f1 = tc_typ env t1 in 
    let env', bindings = maybe_push_binding env <| Inr(Some x, t1) in
    let t2, k2, f2 = tc_typ env' t2 in
    let k = mk_Kind_dcon(Some x, t1, k2, false) t.pos in
    w k <| mk_Typ_lam(x, t1, t2), k, Rel.conj_guard f1 <| Tc.Util.close_guard bindings f2

  | Typ_tlam(a, k1, t1) -> 
    let k1, f1 = tc_kind env k1 in 
    let env', bindings = maybe_push_binding env <| Inl(Some a, k1) in
    let t1, k2, f2 = tc_typ env' t1 in 
    let k = mk_Kind_tcon(Some a, k1, k2, false) t.pos in
    w k <| mk_Typ_tlam(a, k1, t1), k, Rel.conj_guard f1 <| Tc.Util.close_guard bindings f2

  | Typ_ascribed(t1, k1) -> 
    let k1, f1 = tc_kind env k1 in 
    let t1, f2 = tc_typ_check env t1 k1 in
    w k1 <| mk_Typ_ascribed'(t1, k1), k1, Rel.conj_guard f1 f2

  | Typ_meta(Meta_uvar_t_app(t, (uv,k))) -> 
    let t, kk, f = tc_typ env t in
    let k, _ = tc_kind env k in 
    w kk <| mk_Typ_meta'(Meta_uvar_t_app(t, (uv,k))), kk, f

  | Typ_uvar(u, k1) -> 
    let s = compress_typ t in 
    (match s.n with 
        | Typ_uvar _ -> 
          let k1, g = tc_kind env k1 in
          w k1 <| mk_Typ_uvar'(u, k1), k1, g
        | _ -> tc_typ env s)
        
  | Typ_meta (Meta_named(t, l)) -> 
    let env' = Env.set_range env (range_of_lid l) in
    let t, k, f = tc_typ env' t in 
    mk_Typ_meta(Meta_named(t, l)), k, f

  | Typ_meta (Meta_pattern(quant, pats)) -> 
    let quant, k, f = tc_typ env quant in 
    let pat_env = Env.quantifier_pattern_env env quant in
    let pats = List.map (function 
      | Inl t -> Inl <| fst (no_guard env <| tc_typ pat_env t)
      | Inr e -> Inr <| fst (no_guard env <| tc_total_exp pat_env e)) pats in
    mk_Typ_meta(Meta_pattern(quant, pats)), k, f

  | Typ_unknown -> 
    let k = Tc.Util.new_kvar env in 
    let t = Tc.Util.new_tvar env k in 
    t, k, Trivial

  | _ -> failwith (Util.format1 "Unexpected type : %s\n" (Print.typ_to_string t)) 

and tc_typ_check env t (k:knd) : typ * guard = 
  let t', k', f = tc_typ env t in
  let f' = Tc.Rel.keq env (Some t') k' k in
  t', Rel.conj_guard f f'       

and tc_value env e : exp * comp = 
  let env = Env.set_range env e.pos in
  match e.n with
  | Exp_uvar(u, t1) -> 
    value_check_expected_typ env e (Inl t1)
  | Exp_bvar x -> 
    let t = Env.lookup_bvar env x in
    let e, c = Tc.Util.maybe_instantiate env e t in
    value_check_expected_typ env e (Inr c)

  | Exp_fvar(v, dc) -> 
    let t = Env.lookup_lid env v.v in
    let e, c = Tc.Util.maybe_instantiate env e t in 
    //printfn "Instantiated type of %s to %s\n" (Print.exp_to_string e) (Print.typ_to_string t);
    if dc && not(Env.is_datacon env v.v)
    then raise (Error(Util.format1 "Expected a data constructor; got %s" v.v.str, Tc.Env.get_range env))
    else value_check_expected_typ env e (Inr c)

  | Exp_constant c -> 
    let t = Tc.Util.typing_const env c in
    value_check_expected_typ env e (Inl t)

  | Exp_abs _ 
  | Exp_tabs _ -> (* More efficient to handle curried functions by uncurrying them first, and then re-currying. 
                     This is the dual of the treatment of application ... see the Exp_app/Exp_tapp cases below. *)
    let t0 = Tc.Env.expected_typ env in
    let topt_to_string t0 = match t0 with 
        | None -> () 
        | Some t -> if debug env then Util.fprint1 "\n\tExpected type is %s\n" (Print.typ_to_string t) else () in
    if debug env then (Util.fprint1 "Typechecking abstraction\n\t%s\n" (Print.exp_to_string e); (topt_to_string t0));
    //FYI: local lets are not generalized in F* 
    let err env tc = match t0, tc with
        | Some t, _
        | None, Inl t -> raise (Error(Tc.Errors.expected_a_term_of_type_t_got_a_function t e, rng env)) 
        | _, Inr c -> raise (Error(Tc.Errors.expected_effect_1_got_effect_2 Const.tot_effect_lid (Util.comp_to_comp_typ c).effect_name, rng env)) in
    let rec tcfun env e topt : exp * typ = match e.n, compress_typ_opt topt with 
        | Exp_abs(x, _, _), None -> 
            tcfun env e (Some <| Tc.Util.new_function_typ env (Some x) None)
        
        | Exp_tabs(a, _, _), None -> 
            let nt = Tc.Util.new_poly_typ env a in
            tcfun env e (Some <| nt)

        | Exp_abs(x, _, _), Some ({n=Typ_uvar _}) -> 
            let ft = Tc.Util.uvar_as_function_typ env topt (Some x) None in
            if debug env then Util.fprint1 "Settting expected type to %s\n" (Print.typ_to_string ft);
            topt_to_string t0;
            let res = tcfun env e (Some ft) in
            if debug env then Util.fprint1 "After checking body type is %s\n" (Print.typ_to_string ft);
            topt_to_string t0;
            res
        | Exp_abs _, Some ({n=Typ_univ(a, k, c)}) -> 
            let b = Env.Binding_typ(a, k) in
            let c = Tc.Normalize.flex_to_total env c in 
            let tres = if Util.is_total_comp c then Util.comp_result c else err env (Inr c) in
            let envbody = Tc.Env.set_expected_typ (Env.push_local_binding env b) tres in
            let e, _ = tcfun envbody e (Some tres) in
            let t = Util.must topt in
            syn e.pos t <| mk_Exp_tabs(a, k, e), t

        | Exp_abs(x, t1, body), Some ({n=Typ_fun(xopt, t1', c1, _)}) ->
            let t1 = tc_typ_check_trivial env t1 ktype in
            let _ = trivial <| Tc.Rel.teq env t1 t1' in
            let c1 = match xopt with 
            | None -> c1 
            | Some x' ->
                if Util.bvd_eq x x' then c1
                else Util.subst_comp' [Inr(x',  Util.bvd_to_exp x t1)] c1 in
            let envbody = Tc.Env.set_expected_typ (Tc.Env.push_local_binding env (Binding_var(x, t1))) (Util.comp_result c1) in
            if is_fun body
            then let c1 = Tc.Normalize.flex_to_total env c1 in
                 let tbody = if Util.is_total_comp c1 then Util.comp_result c1 else err env (Inr c1) in
                 let body, _ = tcfun envbody body (Some tbody) in
                 let t = topt |> Util.must in
                 mk_Exp_abs(x, t1, body) t e.pos, t
            else let body, c = tc_exp envbody body in 
                 let body, _, guard = check_expected_effect envbody (Some c1) (body, c) in
                 Tc.Util.discharge_guard envbody guard;
                 let t = Util.must topt in
                 syn e.pos t <| mk_Exp_abs(x, t1, body), t
        
        | Exp_tabs(a, k1, body), Some ({n=Typ_univ(b, k1', c1)}) ->  
            let k1 = tc_kind_trivial env k1 in
            let _ = trivial <| Tc.Rel.keq env None k1 k1' in
            let c1 = if Util.bvd_eq a b 
                     then c1 
                     else Util.subst_comp' [Inl(b,  Util.bvd_to_typ a k1)] c1 in
//            let _ = printfn "Introducing %s at kind %s .... typ is %s\n" (Print.strBvd a) (Print.kind_to_string k1) (Print.typ_to_string aa) in
//            let _ = printfn "Expected type for body is %s\n" (Print.typ_to_string (Util.comp_result c1)) in
            let envbody = Tc.Env.set_expected_typ (Tc.Env.push_local_binding env (Binding_typ(a, k1))) (Util.comp_result c1) in
            if is_fun body
            then let c1 = Tc.Normalize.flex_to_total env c1 in 
                 let tbody = if Util.is_total_comp c1 then Util.comp_result c1 else err env (Inr c1) in
                 let body, _ = tcfun envbody body (Some tbody) in
                 let t = Util.must topt in
                 syn e.pos t <| mk_Exp_tabs(a, k1, body), t
            else let body, c = tc_exp envbody body in 
                 let body, _, guard = check_expected_effect envbody (Some c1) (body, c) in
                 Tc.Util.discharge_guard envbody guard;
                 let t = Util.must topt in
                 syn e.pos t <| mk_Exp_tabs(a, k1, body), t
        
        | e, Some t -> let _ = err env (Inl t) in failwith "impossible" 
        | _, None -> failwith "Impossible" in
 
    let env = instantiate_both env in 
    let e, t = tcfun env e t0 in
    if debug env then (Util.fprint2 "Done typechecked abstraction\n\t%s\n\tComputed type=%s\n" (Print.exp_to_string e) (Print.typ_to_string t);
                      (topt_to_string t0));
    e, mk_Total t
        
  | _ -> 
    failwith (Util.format1 "Unexpected value: %s" (Print.exp_to_string e))

and tc_exp env e : exp * comp = 
  let env = if e.pos=dummyRange then env else Env.set_range env e.pos in
  let w c = syn e.pos (Util.comp_result c) in
  match e.n with
  | Exp_delayed _ -> tc_exp env (compress_exp e)

  | Exp_uvar _ 
  | Exp_bvar _  
  | Exp_fvar _ 
  | Exp_constant _  
  | Exp_abs _ 
  | Exp_tabs _ -> tc_value env e 

  | Exp_ascribed(e1, t1) -> 
    let t1, f = tc_typ_check env t1 ktype in 
    let e1, c = tc_exp (Env.set_expected_typ env t1) e1 in
    comp_check_expected_typ env (w c <| mk_Exp_ascribed'(e1, t1)) (Tc.Util.strengthen_precondition env c f)

  | Exp_meta(Meta_uvar_e_app(e, (u,t))) -> 
    let e, c = tc_exp env e in 
    mk_Exp_meta(Meta_uvar_e_app(e, (u,t))), c
    

  | Exp_meta(Meta_desugared(e, Data_app)) -> 
    (* These are (potentially) values, but constructor types 
       already have an (Tot) effect annotation on their co-domain. 
       So, we can treat them as normal applications. Except ...  *)
    let env = instantiate_both env in
    let env1, topt = Env.clear_expected_typ env in 
    let d, args = Util.uncurry_app e in 
    (* The main subtlety with bidirectional typing is here:
       Consider typing (e1, e2) as (x:t * t')
       It is desugared to (MkTuple2 '_u1 '_u2 e1 e2), and we have to compute the instantiations for '_u1 and '_u2.
       The idea is to push the result type (Tuple2 t (\x:t. t')) down to the constructor MkTuple2
       and then instantiating MkTuple2's arguments using the expected type.
       That's what the Meta_datainst(d, topt) does ... below. 
       Once we compute good instantiations for '_u1 and '_u2, the rest follows as usual. *)
    let d = mk_Exp_meta(Meta_datainst(d, topt)) in
    let e = Util.mk_curried_app d args in
    let e, c = tc_exp env1 e in
    comp_check_expected_typ env (mk_Exp_meta(Meta_desugared(e, Data_app))) c

  | Exp_meta(Meta_desugared(e, Sequence)) -> 
    begin match (compress_exp e).n with 
        | Exp_let((_,[(x, _, e1)]), e2) -> 
          let e2 = match (compress_exp e2).n with 
            | Exp_match(_, [(_, _, e2)]) -> e2
            | _ -> failwith "Impossible" in
          let e1, c1 = tc_exp (Env.set_expected_typ env Tc.Util.t_unit) e1 in 
          let e2, c2 = tc_exp env e2 in 
          let c = Tc.Util.bind env c1 (None, c2) in
          mk_Exp_meta(Meta_desugared(w c <| mk_Exp_let((false, [x, Tc.Util.t_unit, e1]), e2), Sequence)), c
        | _ -> 
          let e, c = tc_exp env e in
          mk_Exp_meta(Meta_desugared(e, Sequence)), c     
    end

  | Exp_meta(Meta_desugared(e, i)) -> 
    let e, c = tc_exp env e in
    mk_Exp_meta(Meta_desugared(e, i)), c

  | Exp_meta(Meta_datainst(dc, topt)) -> 
    (* This is where we process the type annotation on data constructors populated by the Data_app case above. *) 
    let err tres t = raise (Error(Tc.Errors.constructor_builds_the_wrong_type e tres t, rng env))  in 

    (* For compatibility with ML: dtuples without a type annotation default to their non-dependent versions *)
    let maybe_default_dtuple_type env tres topt : bool = 
      let tconstr, args = Util.flatten_typ_apps tres in
      if Util.is_dtuple_constructor tconstr 
      then let tup = Tc.Util.mk_basic_dtuple_type env (List.length args) in
            let _ = match topt with 
            | None -> ()
            | Some t -> Tc.Rel.trivial_subtype env None t tup in
            Tc.Rel.trivial_subtype env None tres tup; true
      else false in
     
    let dc, c_dc = tc_value env dc in 
    let t_dc = Util.comp_result c_dc in
    let _, tcod = Util.collect_formals t_dc in
    let tres = Util.comp_result tcod in
    let norm = match topt with 
      | None -> 
       (* There's no type annotation from the context ... not much to do, except in the case of tuples.
          For dependent tuples, default to a simple (non-dependent) tuple type. *)
        maybe_default_dtuple_type env tres None
       
      | Some t_expected -> 
        let t = Tc.Normalize.norm_typ [Normalize.Beta] env t_expected in
        match t.n with 
        | Typ_uvar _ -> (* We have a type from the context; but it is non-informative. So, default tuples if applicable *)
          maybe_default_dtuple_type env tres (Some t_expected)
       
        | _ -> (* Finally, we have some useful info from the context; use it to instantiate the result type of dc *)
          Tc.Rel.trivial_subtype env None tres t_expected; false in        
    dc, c_dc (* NB: Removed the Meta_datainst tag on the way up---no other part of the compiler sees Meta_datainst *)

  | Exp_app _
  | Exp_tapp _ -> 
    let fvcheck kt fvs = 
      let rec aux retry kt = 
        let fvs_kt = match kt with 
          | Inl k -> (Util.freevars_kind k).fxvs
          | Inr t -> (Util.freevars_typ t).fxvs in
        match fvs |> Util.find_opt (fun (x, _, _) -> Util.set_mem (bvd_to_bvar_s x tun) fvs_kt) with
          | None -> kt
          | Some (x, arg, carg) ->  
            if retry
            then let kt = match kt with 
                          | Inl k -> Inl (Normalize.normalize_kind env k)
                          | Inr t -> Inr (Normalize.normalize env t) in
                 aux false kt
            else raise (Error(Tc.Errors.expected_pure_expression arg carg, arg.pos)) in
        aux true kt in
    let env0 = env in
    let f, args = Util.uncurry_app e in
    let env, _ = Env.clear_expected_typ env in
    let env = match List.hd args with 
      | Inl _ -> {env with Tc.Env.instantiate_targs=false}
      | Inr (_, imp) -> {env with Tc.Env.instantiate_vargs=not imp} in
    let f, cf = tc_exp env f in
//    if debug env then Util.print_string <| Util.format2 "Checked function LHS %s at type %s\n" (Print.exp_to_string f) (norms env cf);//Print.comp_typ_to_string cf);
    let is_primop = Util.is_primop f in
    let rec aux (f, tf, (cs:list<Tc.Util.comp_with_binder>), guard, fvs) args = match args with 
      | Inl targ::rest -> 
        let targ, k, g = tc_typ env targ in 
        begin match Tc.Util.destruct_poly_typ env tf f targ with
          | {n=Typ_univ(a, ka, c2)}, e1' ->
              let ka = left <| fvcheck (Inl ka) fvs in
              let g' = Tc.Rel.keq env (Some targ) k ka in 
              let c2 = Util.subst_comp' [Inl(a, targ)] c2 in
              let cs = (None, c2)::cs in
              let tf = Util.comp_result c2 in
              aux (mk_Exp_tapp(f, targ) tun f.pos, tf, cs, Rel.conj_guard g (Rel.conj_guard g' guard), fvs) rest
          | _ -> failwith "impossible"
        end
        
      | Inr (arg, imp)::rest -> 
        let default_effect = match rest with 
            | [] -> Const.ml_effect_lid
            | _ -> Const.tot_effect_lid in 
        begin match Tc.Util.destruct_function_typ env tf None (Some f) imp (Some default_effect) with 
            | {n=Typ_fun(xopt, targ, cres, _)}, Some f -> 
              let tt = syn' env ktype <| mk_Typ_fun(xopt, targ, cres, false) in
              let targ = right <| fvcheck (Inr targ) fvs in
              let arg, carg = tc_exp (instantiate_both (Env.set_expected_typ env targ)) arg in 
//              if debug env then 
//              (Util.print_string <| Util.format2 "Checked arg %s at type %s" (Print.exp_to_string arg) (Print.comp_typ_to_string carg);
//               printfn "Result type is %s" (Print.comp_typ_to_string cres);
//               printfn "Formal is %s\n" (match xopt with None -> "none" | Some x -> Print.strBvd x));
              begin match xopt with 
                | None -> 
                  let cs = (None, cres)::(None, carg)::cs in
                  let tf = Util.comp_result cres in
                  aux (mk_Exp_app(f, arg, imp) tun f.pos, tf, cs, guard, fvs) rest
                | Some x -> 
                   if Tc.Util.is_pure env carg 
                   then let cres = Util.subst_comp' [Inr(x, arg)] cres in
                        let cs = (None, cres)::(None, carg)::cs in
                        let tf = Util.comp_result cres in
                        aux (mk_Exp_app(f, arg, imp) tun f.pos, tf, cs, guard, fvs) rest
                   else let cs = (Some (Env.Binding_var(x, targ)), cres)::(None, carg)::cs in
                        let tf = Util.comp_result cres in
                        aux (mk_Exp_app(f, arg, imp) tun f.pos, tf, cs, guard, (x, arg, carg)::fvs) rest
              end 
            | _ -> failwith "impossible"
        end

      | [] -> 
        let tf = right <| fvcheck (Inr tf) fvs in
//        if debug env 
//        then (cs |> List.iter (fun (_, c) -> printfn "Comp: %s" (Print.comp_typ_to_string c)));
        let tail = List.fold_left (fun accum cb -> (fst cb, Tc.Util.bind env (snd cb) accum)) (List.hd cs) (List.tl cs) in
        let c0 = Tc.Util.bind env cf tail in
        let c = Tc.Util.strengthen_precondition env c0 guard in
        let c = if !Options.verify && (is_primop || Util.is_total_comp c0)
                then Tc.Util.maybe_assume_result_eq_pure_term env f c 
                else c in
        comp_check_expected_typ env0 f c in
    aux (f, Util.comp_result cf, [], Trivial, []) args
              
  | Exp_match(e1, eqns) -> 
    let env1, topt = Env.clear_expected_typ env in 
    let env1 = instantiate_both env1 in
    let e1, c1 = tc_exp env1 e1 in
    let env_branches, res_t = match topt with
      | Some t -> env, t
      | None -> 
        let res_t = Tc.Util.new_tvar env ktype in
        Env.set_expected_typ env res_t, res_t in
    let guard_x = Util.new_bvd (Some <| e1.pos) in
//    let _ = if debug env then printfn "New guard exp %s\n" (Print.strBvd guard_x) in
    let t_eqns = eqns |> List.map (tc_eqn guard_x (Util.comp_result c1) env_branches) in
    let c_branches = 
      let cases = List.fold_right (fun (_, f, c) caccum -> (f, c)::caccum) t_eqns [] in 
      Tc.Util.bind_cases env res_t cases in (* bind_cases adds an exhaustiveness check *)
    let cres = Tc.Util.bind env c1 (Some <| Env.Binding_var(guard_x, Util.comp_result c1), c_branches) in
    w cres <| mk_Exp_match(e1, List.map (fun (f, _, _) -> f) t_eqns), cres

  | Exp_let((false, [(x, t, e1)]), e2) -> 
    let env = instantiate_both env in
    let t = Tc.Util.extract_lb_annotation false env t e1 in
    printfn "Type-checking let-binding annot: %s" (Print.typ_to_string t);
    let t, f = tc_typ_check env t ktype in
    let env1, topt = Env.clear_expected_typ env in 
    let env1 = Tc.Env.set_expected_typ env1 t in
    let e1, c1 = tc_exp env1 e1 in 
    let c1 = Tc.Util.strengthen_precondition env c1 f in
    let _, e1, c1 = match x with 
        | Inl _ -> x, e1, c1 (* don't generalize inner lets *) 
        | _ -> List.hd <| Tc.Util.generalize env1 [x, e1, c1] (* only generalize top-level lets *) in
    let b = binding_of_lb x (Util.comp_result c1) in
    let e2, c2 = tc_exp (Env.push_local_binding env b) e2 in
    let cres = Tc.Util.bind env c1 (Some b, c2) in
    let e = w cres <| mk_Exp_let((false, [(x, Util.comp_result c1, e1)]), e2) in
    begin match topt, x with 
      | None, Inl bvd -> 
         let fvs = Util.freevars_typ (Util.comp_result cres) in
         if Util.set_mem (bvd_to_bvar_s bvd t) fvs.fxvs 
         then raise (Error(Tc.Errors.inferred_type_causes_variable_to_escape t bvd, rng env))
         else e, cres
      | _ -> e, cres
    end       
    
  | Exp_let((false, _), _) -> 
    failwith "impossible"

  | Exp_let((true, lbs), e1) ->
    let env = instantiate_both env in
    let env0, topt = Env.clear_expected_typ env in 
    let lbs, env' = lbs |> List.fold_left (fun (xts, env) (x, t, e) -> 
      let t = Tc.Util.extract_lb_annotation true env t e in 
      let t = tc_typ_check_trivial env0 t ktype in
      let env = Env.push_local_binding env (binding_of_lb x t) in
      (x, t, e)::xts, env) ([], env0)  in 
    let lbs = lbs |> List.map (fun (x, t, e) -> 
      let env' = Env.set_expected_typ env' t in
      let e, t = no_guard env <| tc_total_exp env' e in 
      (x, t, e)) in  
    let gen_lbs = 
        let ecs = Tc.Util.generalize env (lbs |> List.map (fun (x, t, e) -> (x, e, Util.total_comp t <| range_of_lb (x,t,e)))) in //fishy
        List.map (fun (x, e, c) -> x, Util.comp_result c, e) ecs in
    let lbs, bindings, env = gen_lbs |> List.fold_left (fun (lbs, bindings, env) (x, t, e) -> 
      let b = binding_of_lb x t in
      let env = Env.push_local_binding env b in
      (x, t, e)::lbs, b::bindings, env) ([], [], env) in
    let e1, cres = tc_exp env e1 in 
    let cres = Tc.Util.close_comp env bindings cres in
    let e = w cres <| mk_Exp_let((true, lbs), e1) in
    begin match topt with 
      | Some _ -> e, cres
      | None -> 
         let fvs = Util.freevars_typ <| Util.comp_result cres in
         match lbs |> List.tryFind (function 
                | (Inr _, _, _) -> false
                | (Inl x, _, _) -> Util.set_mem (bvd_to_bvar_s x tun) fvs.fxvs) with
            | Some (Inl y, _, _) -> raise (Error(Tc.Errors.inferred_type_causes_variable_to_escape (Util.comp_result cres) y, rng env))
            | _ -> e, cres
    end

and tc_eqn (guard_x:bvvdef) pat_t env (pattern, when_clause, branch) : (pat * option<exp> * exp) * option<formula> * comp =
  (* 
     guard_x is the scrutinee;  pat_t is the expected pattern typ; 
     Returns: (pattern, when_clause, branch) --- typed
              option<formula> -- guard condition for this branch, propagated up for exhaustiveness check
              comp            -- the computation type of the branch
  *)
  let rec tc_pat (pat_t:typ) env p : list<Env.binding> * Env.env * list<exp> = 
    let pvar_eq x y = match x, y with 
      | Inl a, Inl b -> bvd_eq a b
      | Inr x, Inr y -> bvd_eq x y
      | _ -> false in
    let pvar_of_binding = function
      | Binding_typ(a, _) -> Inl a
      | Binding_var(x, _) -> Inr x
      | _ -> failwith "impossible" in
    let binding_exists bindings x = bindings |> Util.for_some (fun b -> pvar_eq (pvar_of_binding b) x) in
    let rec pat_bindings bindings p = match p with 
      | Pat_wild 
      | Pat_twild
      | Pat_constant _ -> bindings, []
      | Pat_withinfo(p, _) -> pat_bindings bindings p
      | Pat_var x -> 
        if binding_exists bindings (Inr x) 
        then raise (Error(Tc.Errors.nonlinear_pattern_variable x, Util.range_of_bvd x))
        else Env.Binding_var(x, Tc.Util.new_tvar env ktype) :: bindings , [Inr x]
      | Pat_tvar a -> 
        if binding_exists bindings (Inl a) 
        then raise (Error(Tc.Errors.nonlinear_pattern_variable a, Util.range_of_bvd a))
        else Env.Binding_typ(a, Tc.Util.new_kvar env)::bindings, [Inl a]
      | Pat_cons(_, pats) -> 
        List.fold_left (fun (bindings, out) p -> 
            let b, o = pat_bindings bindings p in 
            b, o@out) (bindings,[]) pats
      | Pat_disj [] -> failwith "impossible"
      | Pat_disj (p::pats) -> 
        let b, o = pat_bindings bindings p in 
        pats |> List.iter (fun p -> 
          let _, o' = pat_bindings bindings p in 
          if not (Util.multiset_equiv pvar_eq o o')
          then raise (Error(Tc.Errors.disjunctive_pattern_vars o o', Tc.Env.get_range env))
          else ());
        b, o in
    let bindings = fst <| pat_bindings [] p in
    let pat_env = List.fold_left Env.push_local_binding env bindings in
    let exps = Tc.Util.pat_as_exps env p in
    let env, _ = Tc.Env.clear_expected_typ pat_env in 
    let env = {env with Env.is_pattern=true} in //{(Tc.Env.set_expected_typ pat_env pat_t) with Env.is_pattern=true} in
    let res = bindings, pat_env, List.map (fun e -> 
        let e, t = no_guard env <| tc_total_exp env e in
        //printfn "Trying pattern subtype %s <: %s" (Print.typ_to_string pat_t) (Print.typ_to_string t);
        Tc.Rel.trivial_subtype env None pat_t t; //the type of the pattern must be at least as general as the type of the scrutinee
        e) exps in
    res in

  let bindings, pat_env, disj_exps = tc_pat pat_t env pattern in //disj_exps, an exp for each arm of a disjunctive pattern
  let when_clause = match when_clause with 
    | None -> None
    | Some e -> Some (fst <| (no_guard env <| tc_total_exp (Env.set_expected_typ pat_env Tc.Util.t_bool) e)) in
  let branch, c = tc_exp pat_env branch in
  let guard_exp = Util.bvd_to_exp guard_x pat_t in
  let guard_env = Env.push_local_binding env (Env.Binding_var(guard_x, pat_t)) in
  let c = 
    let eqs = disj_exps |> List.fold_left (fun fopt e -> 
        let e = compress_exp e in
        match e.n with 
            | Exp_uvar _
            | Exp_constant _ 
            | Exp_fvar _ -> fopt (* Equation for non-binding forms are handled with the discriminators below *)
            | _ -> 
              let clause = Util.mk_eq guard_exp e in
                match fopt with
                 | None -> Some clause
                 | Some f -> Some <| Util.mk_disj clause f) None in 
    let c = match eqs, when_clause with
      | None, None -> c
      | Some f, None -> Tc.Util.weaken_precondition env c (NonTrivial f)
      | Some f, Some w -> Tc.Util.weaken_precondition env c (NonTrivial <| Util.mk_conj f (Util.mk_eq w Const.exp_true_bool)) 
      | None, Some w -> Tc.Util.weaken_precondition env c (NonTrivial <| Util.mk_eq w Const.exp_true_bool) in
    Tc.Util.close_comp env bindings c in
  let discriminate f = 
    let disc = Util.mk_discriminator f.v in 
    let disc = Util.mk_curried_app (Util.fvar disc (range_of_lid f.v)) [Inr (guard_exp, false)] in
    let e, _, _ = tc_total_exp (Env.set_expected_typ guard_env Tc.Util.t_bool) disc in
    Util.mk_eq e Const.exp_true_bool in
  let gg =
    let discs = disj_exps |> List.collect (fun e -> 
      let e = compress_exp e in 
      match e.n with 
      | Exp_uvar _
      | Exp_meta(Meta_uvar_e_app _)
      | Exp_bvar _ -> [Util.ftv Const.true_lid ktype]
      | Exp_constant c -> [Util.mk_eq guard_exp e]
      | Exp_fvar(f, _) -> [discriminate f]
      | Exp_app _ 
      | Exp_tapp _ -> 
        let f, _ = Util.uncurry_app e in
        (match f.n with 
          | Exp_fvar(f, _) -> [discriminate f]
          | _ -> failwith "Impossible")
      | _ -> failwith (Util.format2 "tc_eqn: Impossible (%s) %s" (Range.string_of_range e.pos) (Print.exp_to_string e))) in
    List.fold_left (fun fopt f -> match fopt with 
      | None -> Some f
      | Some g -> Some (Util.mk_disj f g)) None discs in
  (pattern, when_clause, branch), gg, c 

and tc_kind_trivial env k : knd = 
  match tc_kind env k with 
    | k, Trivial -> k
    | _ -> raise (Error(Tc.Errors.kind_has_a_non_trivial_precondition k, Env.get_range env))

and tc_typ_trivial env t : typ * knd = 
  let t, k, g = tc_typ env t in
  match g with 
    | Trivial -> t, k
    | _ -> raise (Error(Tc.Errors.type_has_a_non_trivial_precondition t ^ " 1: " ^ (guard_to_string env g), t.pos))

and tc_typ_check_trivial env t (k:knd) = 
  let t, f = tc_typ_check env t k in
  match f with 
    | Trivial -> t
    | _ -> raise (Error(Tc.Errors.type_has_a_non_trivial_precondition t ^ " 2: " ^ (guard_to_string env f), t.pos))

and tc_total_exp env e : exp * typ * guard = 
  let e, c = tc_exp env e in
  if is_total_comp c 
  then e, Util.comp_result c, Trivial
  else match Tc.Rel.sub_comp env c (Util.total_comp (Util.comp_result c) (Env.get_range env)) with 
    | Some g -> e, Util.comp_result c, g
    | _ -> raise (Error(Tc.Errors.expected_pure_expression e c, e.pos))


(*****************Type-checking the signature of a module*****************************)

let tc_tparams env tps : (list<tparam> * Env.env) = 
	let tps', env = List.fold_left (fun (tps, env) tp -> match tp with 
	  | Tparam_typ(a, k) -> 
				let k = tc_kind_trivial env k in 
				let env = Tc.Env.push_local_binding env (Env.Binding_typ(a, k)) in
				Tparam_typ(a,k)::tps, env
	  | Tparam_term(x, t) -> 
				let t, _ = tc_typ_trivial env t in 
				let env = Tc.Env.push_local_binding env (Env.Binding_var(x, t)) in
				Tparam_term(x, t)::tps, env) ([], env) tps in
		List.rev tps', env 

let kt k1 k2 = mk_Kind_tcon(None, k1, k2, false) k2.pos
let kd t k = mk_Kind_dcon(None, t, k, false) k.pos
let a_kwp_a m s = match s.n with 
  | Kind_tcon(Some a, {n=Kind_type}, {n=Kind_tcon(None, kwp, {n=Kind_tcon(None, kwlp, {n=Kind_effect}, false)}, false)}, false) -> a, kwp
  | _ -> raise (Error(Tc.Errors.unexpected_signature_for_monad m s, range_of_lid m))

let rec tc_monad_decl env m =  
  let mk = tc_kind_trivial env m.signature in 
  let a, kwp_a = a_kwp_a m.mname mk in 
  let a_typ = Util.bvd_to_typ a ktype in
  let b = Util.new_bvd (Some <| range_of_lid m.mname) in 
  let b_typ = Util.bvd_to_typ b ktype in
  let kwp_b = Util.subst_kind' [Inl(a, b_typ)] kwp_a in
  let kwlp_a = kwp_a in
  let kwlp_b = kwp_b in
  let w k = k (range_of_lid m.mname) in
  let ret = 
    let expected_k = w <| mk_Kind_tcon(Some a, ktype, kd a_typ kwp_a, false)  in
    tc_typ_check_trivial env m.ret expected_k in
  let bind_wp =
    let expected_k = w <| mk_Kind_tcon(Some a, ktype, w <| mk_Kind_tcon(Some b, ktype, kt kwp_a (kt kwlp_a (kt (kd a_typ kwp_b) (kt (kd a_typ kwlp_b) kwp_b))), false), false)  in
    tc_typ_check_trivial env m.bind_wp expected_k in
  let bind_wlp = 
   let expected_k = w <| mk_Kind_tcon(Some a, ktype, w <| mk_Kind_tcon(Some b, ktype, kt kwlp_a (kt (kd a_typ kwlp_b) kwp_b), false), false) in
   tc_typ_check_trivial env m.bind_wlp expected_k in
  let ite_wp =
    let expected_k = w <| mk_Kind_tcon(Some a, ktype, kt kwlp_a (kt kwp_a kwp_a), false) in
    tc_typ_check_trivial env m.ite_wp expected_k in
  let ite_wlp =
    let expected_k = w <| mk_Kind_tcon(Some a, ktype, kt kwlp_a kwlp_a, false) in
    tc_typ_check_trivial env m.ite_wlp expected_k in
  let wp_binop = 
    let expected_k = w <| mk_Kind_tcon(Some a, ktype, kt kwp_a (kt (kt ktype (kt ktype ktype)) (kt kwp_a kwp_a)), false) in
    tc_typ_check_trivial env m.wp_binop expected_k in
  let wp_as_type = 
    let expected_k = w <| mk_Kind_tcon(Some a, ktype, kt kwp_a ktype, false) in
    tc_typ_check_trivial env m.wp_as_type expected_k in
  let close_wp = 
    let b = Util.new_bvd None in
    let expected_k = 
      w <| mk_Kind_tcon(Some a, ktype, 
        w <| mk_Kind_tcon(Some b, ktype, 
          w <| mk_Kind_tcon(None, w <| mk_Kind_dcon(None, Util.bvd_to_typ b ktype, kwp_a, false), 
                          kwp_a, false), false), false) in
    tc_typ_check_trivial env m.close_wp expected_k in
  let close_wp_t = 
    let expected_k = 
      w <| mk_Kind_tcon(Some a, ktype, 
          w <| mk_Kind_tcon(None, w <| mk_Kind_tcon(None, ktype, kwp_a, false), 
                          kwp_a, false), false) in
    tc_typ_check_trivial env m.close_wp_t expected_k in
  let assert_p, assume_p = 
    let expected_k = 
      w <| mk_Kind_tcon(Some a, ktype, kt ktype (kt kwp_a kwp_a), false) in
    tc_typ_check_trivial env m.assert_p expected_k, tc_typ_check_trivial env m.assume_p expected_k in
  let null_wp = 
      let expected_k = w <| mk_Kind_tcon(Some a, ktype, kwp_a, false) in
      tc_typ_check_trivial env m.null_wp expected_k in
  let trivial =
      let expected_k = w <| mk_Kind_tcon(Some a, ktype, kt kwp_a ktype, false) in
      tc_typ_check_trivial env m.trivial expected_k in
  let menv = Tc.Env.push_sigelt env (Sig_tycon(m.mname, [], mk, [], [], [], range_of_lid m.mname)) in
  let menv, abbrevs = m.abbrevs |> List.fold_left (fun (env, out) (ma:sigelt) -> 
    let ma, env = tc_decl env ma in 
     env, ma::out) (menv, []) in 
  let m = { 
    mname=m.mname;
    total=m.total; 
    signature=mk;
    abbrevs=abbrevs;
    ret=ret;
    bind_wp=bind_wp;
    bind_wlp=bind_wlp;
    ite_wp=ite_wp;
    ite_wlp=ite_wlp;
    wp_binop=wp_binop;
    wp_as_type=wp_as_type;
    close_wp=close_wp;
    close_wp_t=close_wp_t;
    assert_p=assert_p;
    assume_p=assume_p;
    null_wp=null_wp;
    trivial=trivial} in 
   let _ = Tc.Env.lookup_typ_lid menv m.mname in
    menv, m 

and tc_decl env se = match se with 
    | Sig_monads(mdecls, mlat, r) -> 
      let env = Env.set_range env r in 
     //TODO: check downward closure of totality flags
      let menv, mdecls = mdecls |> List.fold_left (fun (env, out) m ->
        let env, m = tc_monad_decl env m in 
        env, m::out) (env, []) in
      let lat = mlat |> List.map (fun (o:monad_order) -> 
        let a, kwp_a_src = a_kwp_a o.source (Tc.Env.lookup_typ_lid menv o.source) in
        let b, kwp_b_tgt = a_kwp_a o.target (Tc.Env.lookup_typ_lid menv o.target) in
        let kwp_a_tgt = Util.subst_kind' [Inl(b, Util.bvd_to_typ a ktype)] kwp_b_tgt in
        let expected_k = r |> mk_Kind_tcon(Some a, ktype, kt kwp_a_src kwp_a_tgt, false) in
        let lift = tc_typ_check_trivial menv o.lift expected_k in
        {source=o.source; 
          target=o.target;
          lift=lift}) in
      let se = Sig_monads(List.rev mdecls, lat, r) in
      let menv = Tc.Env.push_sigelt menv se in 
      se, menv

    | Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> 
      let env = Tc.Env.set_range env r in 
      let tps, env = tc_tparams env tps in 
      let k = tc_kind_trivial env k in 
      let se = Sig_tycon(lid, tps, k, _mutuals, _data, tags, r) in
      let _ = match compress_kind k with
        | {n=Kind_uvar _} -> Rel.trivial <| Tc.Rel.keq env None k ktype
        | _ -> () in 
      let env = Tc.Env.push_sigelt env se in
      se, env
  
    | Sig_typ_abbrev(lid, tps, k, t, tags, r) -> 
      let env = Tc.Env.set_range env r in
      let tps, env' = tc_tparams env tps in
      let t, k1 = tc_typ_trivial env' t in 
      let k2 = tc_kind_trivial env' k in 
      Rel.trivial <| Rel.keq env' (Some t) k1 k2;
      let se = Sig_typ_abbrev(lid, tps, k1, t, tags, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
  
    | Sig_datacon(lid, t, tname, quals, r) -> 
      let env = Tc.Env.set_range env r in
      let t = tc_typ_check_trivial env t ktype in 
      let args, cod = Util.collect_formals t in
      let result_t = Util.comp_result cod in
      let constructed_t, _ = Util.flatten_typ_apps result_t in (* TODO: check that the tps in tname are the same as here *)
      let _ = match destruct constructed_t tname with 
        | Some _ -> ()
        | _ -> raise (Error (Tc.Errors.constructor_builds_the_wrong_type (Util.fvar lid (range_of_lid lid)) constructed_t (Util.ftv tname kun), range_of_lid lid)) in
      let t = Tc.Util.refine_data_type env lid args result_t in
      let se = Sig_datacon(lid, t, tname, quals, r) in 
      let env = Tc.Env.push_sigelt env se in 
      if log env then Util.print_string <| Util.format2 "data %s : %s\n" lid.str (Print.typ_to_string t);
      se, env
  
    | Sig_val_decl(lid, t, quals, r) -> 
      let env = Tc.Env.set_range env r in
      let t = tc_typ_check_trivial env t ktype in 
      Tc.Util.check_uvars r t;
      let se = Sig_val_decl(lid, t, quals, r) in 
      let env = Tc.Env.push_sigelt env se in 
      if log env then Util.print_string <| Util.format2 "val %s : %s\n" lid.str (Print.typ_to_string t);
      se, env
  
    | Sig_assume(lid, phi, quals, r) ->
      let env = Tc.Env.set_range env r in
      let phi = tc_typ_check_trivial env phi ktype in 
      Tc.Util.check_uvars r phi;
      let se = Sig_assume(lid, phi, quals, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
   
    | Sig_let(lbs, r) -> 
      let is_rec = fst lbs in
      let env = Tc.Env.set_range env r in
      let lbs' = snd lbs |> List.fold_left (fun lbs lb -> 
        let lb = match lb with 
          | (Inl _, _, _) -> failwith "impossible"
          | (Inr l, t, e) -> 
            let (lb, t, e) = match Tc.Env.try_lookup_val_decl env l with 
              | None -> 
                let t = Tc.Util.extract_lb_annotation is_rec env t e in
                (Inr l, t, e)
              | Some t' -> match t.n with 
                  | Typ_unknown -> 
                    (Inr l, t', e)
                  | _ -> 
                    Util.print_string <| Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation" (Range.string_of_range r);
                    (Inr l, t', e) in
             (lb, t, e) in
        lb::lbs) [] in
      let lbs' = List.rev lbs' in
      let e = mk_Exp_let((fst lbs, lbs'), syn' env Tc.Util.t_unit <| mk_Exp_constant(Syntax.Const_unit)) tun r in
      let se = match tc_exp env e with 
        | {n=Exp_let(lbs, _)}, _ -> Sig_let(lbs, r)
        | _ -> failwith "impossible" in
      let env = Tc.Env.push_sigelt env se in 
      se, env

    | Sig_main(e, r) ->
      let env = Tc.Env.set_range env r in
      let env = Tc.Env.set_expected_typ env Util.t_unit in
      let e, _ = tc_exp env e in 
      let se = Sig_main(e, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env

    | Sig_bundle(ses, r) -> 
      let env = Tc.Env.set_range env r in
      let tycons, rest = ses |> List.partition (function Sig_tycon _ -> true | _ -> false) in
      let abbrevs, rest = rest |> List.partition (function Sig_typ_abbrev _ -> true | _ -> false) in
      let recs = abbrevs |> List.map (function 
        | Sig_typ_abbrev(lid, tps, k, t, [], r) ->
           let k = match k.n with 
            | Kind_unknown -> Tc.Util.new_kvar env 
            | _ -> k in
           Sig_tycon(lid, tps, k, [], [], [], r), t
        | _ -> failwith "impossible") in
      let recs, abbrev_defs = List.split recs in
      let tycons = fst <| tc_decls env tycons in 
      let recs = fst <| tc_decls env recs in
      let env1 = Tc.Env.push_sigelt env (Sig_bundle(tycons@recs, r)) in
      let rest = fst <| tc_decls env1 rest in
      let abbrevs = List.map2 (fun se t -> match se with 
        | Sig_tycon(lid, tps, k, [], [], [], r) -> 
          let tt = Util.close_with_lam tps (mk_Typ_ascribed(t, k) t.pos) in
          let tt, _ = tc_typ_trivial env1 tt in
          let tps, t = 
            let rec aux tps t =
            let t = compress_typ t in 
             match tps, t.n with 
              | Tparam_typ _::tl, Typ_tlam(a, k, t) -> 
                let tps, t = aux tl t in
                Tparam_typ(a, k)::tps, t
              | Tparam_term _::tl, Typ_lam(x, t1, t2) -> 
                let tps, t = aux tl t2 in
                Tparam_term(x, t1)::tps, t
              | [], _ -> [], t
              | _ -> failwith "impossible" in
             aux tps tt in 
           Sig_typ_abbrev(lid, tps, compress_kind k, t, [], r)
         | _ -> failwith "impossible") recs abbrev_defs in    
      let se = Sig_bundle(tycons@abbrevs@rest, r) in 
      let env = Tc.Env.push_sigelt env se in
      se, env

and tc_decls (env:Tc.Env.env) ses = 
  let ses, env = List.fold_left (fun (ses, (env:Tc.Env.env)) se ->
  if debug env
  then Util.print_string (Util.format1 "Checking sigelt\t%s\n" (Print.sigelt_to_string_short se));
  let se, env = tc_decl env se in 
  if debug env
  then Util.print_string (Util.format1 "Checked sigelt\n\t%s\n" (Print.sigelt_to_string se));
  se::ses, env) ([], env) ses in
  List.rev ses, env 

let get_exports env modul decls = 
    if modul.is_interface then decls
    else let exports = Util.find_map (Tc.Env.modules env) (fun m -> 
            if (m.is_interface && Syntax.lid_equals modul.name m.name)
            then Some (m.exports)
            else None) in
         match exports with 
            | None -> decls //TODO: filter decls to exclude the private ones, once we add private qualifiers
            | Some e -> e

let tc_modul env modul = 
  let env = Tc.Env.set_current_module env modul.name in 
  let ses, env = tc_decls env modul.declarations in 
  let exports = get_exports env modul ses in

  let modul = {name=modul.name; declarations=ses; exports=exports; is_interface=modul.is_interface} in 
  let env = Tc.Env.finish_module env modul in
  modul, env

let check_modules (s:solver_t) mods = 
   let fmods, _ = mods |> List.fold_left (fun (mods, env) m -> 
    if List.length !Options.debug <> 0
    then Util.fprint2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.sli m.name);
    let m, env = tc_modul env m in 
    if m.is_interface 
    then mods, env
    else m::mods, env) ([], Tc.Env.initial_env s Const.prims_lid) in
   List.rev fmods
 
