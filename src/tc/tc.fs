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
  | Inl(Some a, t) -> Inl(a,t)::s
  | Inr(Some x, e) -> Inr(x,e)::s
  | _ -> s

let value_check_expected_typ env e t1 : exp * typ * guard = 
  match Env.expected_typ env with 
   | None -> e, t1, Trivial
   | Some t2 -> 
    let e, g = Tc.Util.check_and_ascribe env e t1 t2 in
    e, t2, g

let comp_check_expected_typ env e c : exp * comp_typ = 
  match Env.expected_typ env with 
   | None -> e, c
   | Some t -> Tc.Util.weaken_result_typ env e c t

let check_expected_effect env (copt:option<comp_typ>) (e, c) : exp * comp_typ * guard = 
  match copt with 
    | None -> e, c, Trivial
    | Some c' -> Tc.Util.check_comp_typ env e c c' 
    
let no_guard env (te, kt, f) = match f with
  | Trivial -> te, kt
  | _ -> raise (Error(Tc.Errors.unexpected_non_trivial_precondition_on_term, Env.get_range env)) 

let binding_of_lb x t = match x with 
  | Inl bvd -> Env.Binding_var(bvd, t)
  | Inr lid -> Env.Binding_lid(lid, t)

let rec tc_kind env k : knd * guard = 
  let k = Util.compress_kind k in 
  match k with
  | Kind_uvar _
  | Kind_type
  | Kind_effect -> k, Trivial

  | Kind_abbrev(kabr, k) -> 
    let k, f = tc_kind env k in 
    Kind_abbrev(kabr, k), f

  | Kind_tcon (aopt, k1, k2, imp) -> 
    let k1, f1 = tc_kind env k1 in 
    let env', bindings = maybe_push_binding env (Inl(aopt, k1)) in
    let k2, f2 = tc_kind env' k2 in
    let f2 = Tc.Util.close_guard bindings f2 in
    Kind_tcon(aopt, k1, k2, imp), Rel.conj_guard f1 f2

  | Kind_dcon (xopt, t1, k2, imp) ->
    let t1, _, f1 = tc_typ env t1 in
    let env', bindings = maybe_push_binding env (Inr(xopt, t1)) in
    let k2, f2 = tc_kind env' k2 in
    let f2 = Tc.Util.close_guard bindings f2 in
    Kind_dcon(xopt, t1, k2, imp), Rel.conj_guard f1 f2

  | Kind_unknown -> 
    Tc.Util.new_kvar env, Trivial

and tc_comp_typ env c : comp_typ * guard = 
  let _ = printfn "Checking comp_typ %s\n" (Print.comp_typ_to_string c) in
  let keff = Tc.Env.lookup_typ_lid env c.effect_name in 
  let result, f0 = tc_typ_check env c.result_typ Kind_type in 
  let k, subst = match keff with 
    | Kind_tcon(Some a, Kind_type, k, _) -> k, [Inl(a, result)]  
    | _ -> raise (Error(Tc.Errors.ill_kinded_effect c.effect_name keff, range_of_lid c.effect_name)) in
  let rec tc_args subst k args : list<either<typ,exp>> * guard = 
    match k, args with 
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
    let args, f = tc_args subst k c.effect_args in 
  {c with 
      result_typ=result;
      effect_args=args}, Rel.conj_guard f0 f

and tc_typ' env (t:typ) : typ' * knd * guard = 
  let env = Tc.Env.set_range env (Util.range_of_typ t (Tc.Env.get_range env)) in
  let t = Util.compress_typ t in
  match t.t with 
  | Typ_btvar a -> 
    let k = Env.lookup_btvar env a in
    t.t, k, Trivial

  | Typ_const i when (lid_equals i.v Const.allTyp_lid || lid_equals i.v Const.exTyp_lid) -> 
    (* Special treatment for ForallTyp and ExistsTyp, giving them polymorphic kinds *)
    let k = Tc.Util.new_kvar env in
    let qk = Kind_tcon(None, Kind_tcon(None, k, Kind_type, false), Kind_type, false) in
    t.t, qk, Trivial 
    
  | Typ_const i -> 
    let k = Env.lookup_typ_lid env i.v in 
    t.t, k, Trivial
     
  | Typ_fun(xopt, t1, cod, imp) -> 
    let t1, f1 = tc_typ_check env t1 Kind_type in
    let env', bindings = maybe_push_binding env <| Inr(xopt, t1) in
    let cod, f2 = tc_comp_typ env' cod in
    Typ_fun(xopt, t1, cod, imp), Kind_type, Rel.conj_guard f1 (Tc.Util.close_guard bindings f2)

  | Typ_univ(a, k1, cod) -> 
    let k1, f1 = tc_kind env k1 in 
    let env', bindings = maybe_push_binding env <| Inl(Some a, k1) in
    let cod, f2 = tc_comp_typ env' cod in 
    Typ_univ(a, k1, cod), Kind_type, Rel.conj_guard f1 (Tc.Util.close_guard bindings f2) 

  | Typ_refine(x, t1, t2) -> 
    let t1, f1 = tc_typ_check env t1 Kind_type in
    let env', bindings = maybe_push_binding env <| Inr(Some x, t1) in
    let t2, f2 = tc_typ_check env' t2 Kind_type in
    Typ_refine(x, t1, t2), Kind_type, Rel.conj_guard f1 (Tc.Util.close_guard bindings f2)

  | Typ_app(t1, t2, imp) -> 
    let t1, k1, f1 = tc_typ env t1 in 
    let aopt, karg, kres, t1 = match Tc.Util.destruct_tcon_kind env k1 t1 imp with 
      | Kind_tcon(aopt, karg, kres, _), t1 -> aopt, karg, kres, t1
      | _ -> failwith "impossible" in
    let t2, f2 = tc_typ_check env t2 karg in
    let k2 = Util.subst_kind (maybe_make_subst <| Inl(aopt, t2)) kres in
    Typ_app(t1, t2, imp), k2, Rel.conj_guard f1 f2
    
  | Typ_dep(t1, e1, imp) -> 
    let t1, k1, f1 = tc_typ env t1 in
    let xopt, targ, kres, t1' = match Tc.Util.destruct_dcon_kind env k1 t1 imp with 
      | Kind_dcon(xopt, targ, kres, _), t1 -> xopt, targ, kres, t1
      | _ -> failwith "impossible" in
    let e1, _, f2 = tc_total_exp (Env.set_expected_typ env targ) e1 in
    let k2 = Util.subst_kind (maybe_make_subst <| Inr(xopt, e1)) kres in
    Typ_dep(t1, e1, imp), k2, Rel.conj_guard f1 f2
  
  | Typ_lam(x, t1, t2) -> 
    let t1, k1, f1 = tc_typ env t1 in 
    let env', bindings = maybe_push_binding env <| Inr(Some x, t1) in
    let t2, k2, f2 = tc_typ env' t2 in
    Typ_lam(x, t1, t2), Kind_dcon(Some x, t1, k2, false), Rel.conj_guard f1 <| Tc.Util.close_guard bindings f2

  | Typ_tlam(a, k1, t1) -> 
    let k1, f1 = tc_kind env k1 in 
    let env', bindings = maybe_push_binding env <| Inl(Some a, k1) in
    let t1, k2, f2 = tc_typ env' t1 in 
    Typ_tlam(a, k1, t1), Kind_tcon(Some a, k1, k2, false), Rel.conj_guard f1 <| Tc.Util.close_guard bindings f2

  | Typ_ascribed(t1, k1) -> 
    let k1, f1 = tc_kind env k1 in 
    let t1, f2 = tc_typ_check env t1 k1 in
    Typ_ascribed(t1, k1), k1, Rel.conj_guard f1 f2

  | Typ_uvar(u, k1) -> 
    t.t, k1, Trivial

  | Typ_meta (Meta_pos(t, r)) -> 
    let env' = Env.set_range env r in
    let t, k, f = tc_typ env' t in 
    Typ_meta(Meta_pos(t, r)), k, f

  | Typ_meta (Meta_pattern(quant, pats)) -> 
    let quant, k, f = tc_typ env quant in 
    let pat_env = Env.quantifier_pattern_env env quant in
    let pats = List.map (function 
      | Inl t -> Inl <| fst (no_guard env <| tc_typ pat_env t)
      | Inr e -> Inr <| fst (no_guard env <| tc_total_exp pat_env e)) pats in
    Typ_meta(Meta_pattern(quant, pats)), k, f

  | Typ_unknown -> 
    let k = Tc.Util.new_kvar env in 
    let t = Tc.Util.new_tvar env k in 
    t.t, k, Trivial

  | _ -> failwith (Util.format1 "Unexpected type : %s\n" (Print.typ_to_string t)) 

and tc_typ env t : typ * knd * guard = 
  let t, k, f = tc_typ' env t in 
  match t with
    | Typ_meta(Meta_pos _) 
    | Typ_btvar _
    | Typ_const _ -> withkind k t, k, f
    | _ -> withkind k <| Typ_meta(Meta_pos(withkind k t, rng env)), k, f

and tc_typ_check env t k : typ * guard = 
  let t', k', f = tc_typ env t in
  let f' = Tc.Rel.keq env (Some t') k' k in
  t', Rel.conj_guard f f'       

and tc_value env e : exp * typ * guard = match e with
  | Exp_uvar(u, t1) -> 
    value_check_expected_typ env e t1

  | Exp_bvar x -> 
    let t = Env.lookup_bvar env x in
    let e, t = Tc.Util.maybe_instantiate env e t in
    value_check_expected_typ env e t 

  | Exp_fvar(v, dc) -> 
    let t = Env.lookup_lid env v.v in
    let e, t = Tc.Util.maybe_instantiate env e t in
    if dc && not(Env.is_datacon env v.v) && not(Env.is_logic_function env v.v)
    then raise (Error(Util.format1 "Expected a data constructor; got %s" v.v.str, Tc.Env.get_range env))
    else value_check_expected_typ env e t

  | Exp_constant c -> 
    let t = Tc.Util.typing_const env c in
    value_check_expected_typ env e t

  | Exp_abs(x, t1, e1) -> 
    let destruct_expected_typ env = 
      let err t =  raise (Error(Tc.Errors.expected_a_term_of_type_t_got_a_function t e, rng env)) in
      let rec aux norm env t = 
        let t = compress_typ t in 
        match t.t with
         | Typ_uvar _ ->
           aux norm env (fst <| Tc.Util.destruct_function_typ env t None false)
         
         | Typ_fun(xopt, targ, cod, implicit) -> 
           let cod = cod |> Util.subst_comp_typ (maybe_make_subst <| Inr(xopt,  Util.bvd_to_exp x targ)) in
           Some targ, Some cod, env, (fun x -> x)
         
         | Typ_univ(a, k, cod) -> 
            if not <| Util.is_total_comp cod then err t 
            else let env = Tc.Env.push_local_binding env (Env.Binding_typ(a, k)) in 
                 let targ, cod, env, gen = aux norm env cod.result_typ in
                 targ, cod, env, (fun x -> Exp_tabs(a, k, gen x))
         
         | _ when not norm ->
            aux true env (Tc.Normalize.normalize env t)
        
         | _ -> err t in

      match Tc.Env.expected_typ env with
        | None -> None, None, env, (fun x -> x) 
        | Some t -> 
          let targ, tres, env, gen = aux false env t in
          targ, tres, env, (fun (x,_) -> gen x, t) in
    
    let targ, tres, env, gen = destruct_expected_typ env in 
    printfn "Destructed expected type into %s and %s\n" (match targ with None -> "-" | Some t -> Print.typ_to_string t) (match tres with None -> "-" | Some t -> Print.comp_typ_to_string t);
    let tx, k1, f1 = tc_typ env t1 in
    let f2 = match targ with 
      | None -> Trivial
      | Some targ -> Tc.Rel.teq env tx targ in (* yes, really want this to be teq *)
    let envbody = match tres with 
      | None -> instantiate_both <| env
      | Some t -> instantiate_both <| Tc.Env.set_expected_typ env t.result_typ in 
    let b = Env.Binding_var(x, tx) in
    let envbody = Env.push_local_binding envbody b in
    let e1, tres, fbody = check_expected_effect envbody tres <| tc_exp envbody e1 in 
    let (_, xvars) = Util.freevars_comp_typ tres in
    let dom = match xvars |> Util.find_opt (fun (y:bvvar) -> bvd_eq x y.v) with
      | None -> None
      | Some _ -> Some x in 
    let t = withkind Kind_type <| Typ_fun(dom, tx, tres, false) in
    let e, t = gen (Exp_abs(x, tx, e1), t) in
    e, t, Rel.conj_guard f1 (Rel.conj_guard f2 (Tc.Util.close_guard [b] fbody))
   
  | Exp_tabs(a, k1, e1) -> 
    let err t = raise (Error(Tc.Errors.expected_a_term_of_type_t_got_a_function t e, rng env)) in
    let k1, f1 = tc_kind env k1 in 
    let env, topt = Env.clear_expected_typ env in
    let karg, copt, env', f2 = match topt with 
      | Some t -> 
        let rec aux norm t = 
          let t = compress_typ t in 
          match t.t with 
            | Typ_univ(b, karg, tres) -> 
              let f2 = Tc.Rel.keq env None karg k1 in 
              let tres = Util.subst_comp_typ [Inl(b, Util.bvd_to_typ a karg)] tres in
              karg, Some tres, Env.set_expected_typ env tres.result_typ, f2
            | _ when not norm -> aux true (Tc.Normalize.normalize env t)
            | _ -> 
               raise (Error(Tc.Errors.expected_a_term_of_type_t_got_a_function t e, rng env)) in
        aux false t
      | None -> 
        k1, None, env, Trivial in
    let env' = instantiate_both env' in
    let b = Env.Binding_typ(a, karg) in
    let envbody = Env.push_local_binding env' b in
    let e1', tres, fbody = check_expected_effect envbody copt <| tc_exp envbody e1 in
    let t = withkind Kind_type <| Typ_univ(a, karg, tres) in
    Exp_tabs(a, karg, e1'), t, Rel.conj_guard f1 (Rel.conj_guard f2 (Tc.Util.close_guard [b] fbody))

  | Exp_meta(Meta_info(e, _, p)) -> 
    let env = Tc.Env.set_range env p in
    let e, t, g = tc_value env e in
    Exp_meta(Meta_info(e, t, p)), t, g
  
  | v -> 
    printfn "Unexpected value %A\n" v;
    failwith (Util.format1 "Unexpected value: %s" (Print.exp_to_string v))

and tc_exp env e : exp * comp_typ = match e with
  | Exp_meta(Meta_info(e, _, p)) -> 
    let env = Tc.Env.set_range env p in
    let e, c = tc_exp env e in
    Exp_meta(Meta_info(e, c.result_typ, p)), c  

  | Exp_uvar _ 
  | Exp_bvar _  
  | Exp_fvar _ 
  | Exp_constant _ 
  | Exp_abs _ 
  | Exp_tabs _ -> 
    let v, t, f = tc_value env e in
    v, Tc.Util.strengthen_precondition env (Util.total_comp t (Env.get_range env)) f

  | Exp_meta(Meta_desugared(e, Sequence)) -> 
    let e, c = tc_exp env e in
    Exp_meta(Meta_desugared(e, Sequence)), c

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
    let d = Exp_meta(Meta_datainst(d, topt)) in
    let e = Util.mk_curried_app d args in
    let e, c = tc_exp env1 e in
    comp_check_expected_typ env (Exp_meta(Meta_desugared(e, Data_app))) c

  | Exp_meta(Meta_datainst(dc, topt)) -> 
    (* This is where we process the type annotation on data constructors populated by the Data_app case above. *) 
    let err tres t = raise (Error(Tc.Errors.constructor_builds_the_wrong_type e tres t, rng env))  in 

    (* For compatibility with ML: tuples without a type annotation default to their non-dependent versions *)
    let maybe_default_tuple_type env tres topt = 
      let tconstr, args = Util.flatten_typ_apps tres in
      if Util.is_tuple_constructor tconstr 
      then let tup = Tc.Util.mk_basic_tuple_type env (List.length args) in
            let _ = match topt with 
            | None -> ()
            | Some t -> Tc.Rel.trivial_subtype env t tup in
            Tc.Rel.trivial_subtype env tres tup
      else () in
     
    let dc, t_dc, _ = tc_value env dc in 
    let _, tres = Util.collect_formals t_dc in
    printfn "Computed type %s for dc %s; tres is %s\n" (Print.typ_to_string t_dc) (Print.exp_to_string dc) (Print.typ_to_string tres);
    let _ = match topt with 
      | None -> 
       (* There's no type annotation from the context ... not much to do, except in the case of tuples.
          For tuples, default to a simple (non-dependent) tuple type. *)
        maybe_default_tuple_type env tres None
       
      | Some t_expected -> 
        let t = Tc.Normalize.norm_typ [Normalize.Beta] env t_expected in
        match t.t with 
        | Typ_uvar _ -> (* We have a type from the context; but it is non-informative. So, default tuples if applicable *)
          maybe_default_tuple_type env tres (Some t_expected)
       
        | tt -> (* Finally, we have some useful info from the context; use it to instantiate the result type of dc *)
          Tc.Rel.trivial_subtype env tres t_expected in        
    dc, Util.total_comp t_dc (Env.get_range env) (* NB: Remove the Meta_datainst tag on the way up---no other part of the compiler sees Meta_datainst *)

  | Exp_app(e1, e2, imp) -> 
    let env1, _ = Env.clear_expected_typ env in
    let e1, c1 = tc_exp ({env1 with Tc.Env.instantiate_vargs=not imp}) e1 in
    let xopt, targ, cres, e1 = match Tc.Util.destruct_function_typ env c1.result_typ (Some e1) imp with 
      | {t=Typ_fun(xopt, targ, tres, _)}, Some e1 -> 
        xopt, targ, tres, e1
      | _ -> failwith "impossible" in 
    let e2, c2 = tc_exp (instantiate_both (Env.set_expected_typ env targ)) e2 in 
    let x_cres, c2, f = match xopt with 
      | None -> (None, cres), c2, Trivial
      | Some x -> 
        let total_c2 = Util.total_comp c2.result_typ (range_of_bvd x) in
        match Tc.Rel.sub_comp_typ env c2 total_c2 with 
         | None -> 
              if Util.for_some (fun y -> bvd_eq y.v x) <| (snd <| Util.freevars_typ cres.result_typ)
              then raise (Error(Tc.Errors.expected_pure_expression c2, range_of_exp e2 (Env.get_range env)))
              else (Some <| Env.Binding_var(x, targ), cres), c2, Trivial
         | Some f -> 
              (None, Util.subst_comp_typ [Inr(x, e2)] cres), total_c2, f in
    let res = Tc.Util.bind env c1 (None, Tc.Util.bind env c2 x_cres) in
    let res = Tc.Util.strengthen_precondition env res f in
    comp_check_expected_typ env (Exp_app(e1, e2, imp)) cres 
       
  | Exp_tapp(e1, t1) -> 
    let env1, _ = Env.clear_expected_typ env in 
    let e1, c1 = tc_exp ({env1 with Env.instantiate_targs=false}) e1 in 
    let t1, k1, f = tc_typ env1 t1 in 
    begin match Tc.Util.destruct_poly_typ env1 c1.result_typ e1 t1 with
      | {t=Typ_univ(a, k, tres)}, e1' ->
          let f = Tc.Rel.keq env1 (Some t1) k k1 in 
          let tres = Util.subst_comp_typ [Inl(a, t1)] tres in
          let cres = Tc.Util.bind env c1 (None, tres) in
          comp_check_expected_typ env (Exp_tapp(e1, t1)) cres 
      | _ -> failwith "impossible"
    end
    
  | Exp_match(e1, eqns) -> 
    let env1, topt = Env.clear_expected_typ env in 
    let env1 = instantiate_both env1 in
    let e1, c1 = tc_exp env1 e1 in
    let env_branches = match topt with
      | Some _ -> env 
      | None -> Env.set_expected_typ env (Tc.Util.new_tvar env Kind_type) in
    let guard_x = Util.new_bvd (Some <| range_of_exp e1 (Env.get_range env)) in
    let t_eqns = eqns |> List.map (tc_eqn guard_x c1.result_typ env_branches) in
    let c_branches = List.fold_right (fun (_, c) caccum -> Tc.Util.bind_ite env c.result_typ c caccum) 
                        t_eqns 
                        (Tc.Util.lift_pure env (if !Options.pretype then Util.ftv Const.true_lid else Util.ftv Const.false_lid)) in
    let cres = Tc.Util.bind env c1 (Some <| Env.Binding_var(guard_x, c1.result_typ), c_branches) in
    Exp_match(e1, List.map fst t_eqns), cres

  | Exp_ascribed(e1, t1) -> 
    let t1, f = tc_typ_check env t1 Kind_type in 
    let e1, c = tc_exp (Env.set_expected_typ env t1) e1 in
    comp_check_expected_typ env (Exp_ascribed(e1, t1)) (Tc.Util.strengthen_precondition env c f)
  
  | Exp_let((false, [(x, t, e1)]), e2) -> 
    let env = instantiate_both env in
    let t = Tc.Util.extract_lb_annotation env t e1 in
    let t, f = tc_typ_check env t Kind_type in
    let env1, topt = Env.clear_expected_typ env in 
    let env1 = Tc.Env.set_expected_typ env1 t in
    let e1, c1 = tc_exp env1 e1 in 
    let c1 = Tc.Util.strengthen_precondition env c1 f in
    let e1, c1 = if Util.is_total_comp c1
                 then Tc.Util.generalize env1 e1 c1 
                 else e1, c1 in 
    let b = binding_of_lb x c1.result_typ in
    let e2, c2 = tc_exp (Env.push_local_binding env b) e1 in
    let cres = Tc.Util.bind env c1 (Some b, c2) in
    let e = Exp_let((false, [(x, c1.result_typ, e1)]), e2) in
    begin match topt, x with 
      | None, Inl bvd -> 
         if Util.for_some (fun y -> bvd_eq y.v bvd) (snd <| Util.freevars_typ cres.result_typ)
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
      let t = Tc.Util.extract_lb_annotation env t e in 
      let t = tc_typ_check_trivial env0 t Kind_type in
      let env = Env.push_local_binding env (binding_of_lb x t) in
      (x, t, e)::xts, env) ([], env0)  in 
    let lbs = lbs |> List.map (fun (x, t, e) -> 
      let env' = Env.set_expected_typ env' t in
      let e, c = no_guard env <| tc_total_exp env' e in 
      (x, c, e)) in  
    let lbs, bindings, env = lbs |> List.fold_left (fun (lbs, bindings, env) (x, t, e) -> 
      let e, c = Tc.Util.generalize env' e (Util.total_comp t (Env.get_range env)) in
      let b = binding_of_lb x c.result_typ in
      let env = Env.push_local_binding env b in
      (x, c.result_typ, e)::lbs, b::bindings, env) ([], [], env) in
    let e1, cres = tc_exp env e1 in 
    let cres = Tc.Util.close_comp_typ env bindings cres in
    let e = Exp_let((true, lbs), e1) in
    begin match topt with 
      | Some _ -> e, cres
      | None -> 
         let _, fxvs = Util.freevars_typ cres.result_typ in 
         match fxvs |> List.tryFind (fun y -> lbs |> Util.for_some (function
          | (Inr _, _, _) -> false
          | (Inl x, _, _) -> bvd_eq x y.v)) with
            | None -> e, cres
            | Some y -> raise (Error(Tc.Errors.inferred_type_causes_variable_to_escape cres.result_typ y.v, rng env))
    end

  | Exp_primop(op, es) -> 
    let env = instantiate_both env in
    let op_t = Tc.Env.lookup_operator env op in
    let x = Util.new_bvd (Some op.idRange) in
    let env' = Tc.Env.push_local_binding env (Env.Binding_var(x, op_t)) in
    let app = Util.mk_curried_app (Util.bvd_to_exp x op_t) (List.map (fun e -> Inr(e, false)) es) in
    let app, c = tc_exp env' app in
    let _, tes = Util.uncurry_app app in
    let es = tes |> List.map (function 
      | Inl _ -> failwith "Impossible"
      | Inr (e, _) -> e) in 
    Exp_primop(op, es), c

and tc_eqn (guard_x:bvvdef) pat_t env (pat, when_clause, branch) : (pat * option<exp> * exp) * comp_typ =
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
        else Env.Binding_var(x, Tc.Util.new_tvar env Kind_type) :: bindings , [Inr x]
      | Pat_tvar a -> 
        if binding_exists bindings (Inl a) 
        then raise (Error(Tc.Errors.nonlinear_pattern_variable a, Util.range_of_bvd a))
        else Env.Binding_typ(a, Tc.Util.new_kvar env)::bindings, [Inl a]
      | Pat_cons(l, pats) -> 
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
    let env = {(Tc.Env.set_expected_typ pat_env pat_t) with Env.is_pattern=true} in
    //Printf.printf "Checking patterns ... expecting type %s\n" (Print.typ_to_string pat_t);
    bindings, pat_env, List.map (fun e -> fst <| (no_guard env <| tc_total_exp env e)) exps in

  let bindings, pat_env, disj_exps = tc_pat pat_t env pat in 
  let when_clause = match when_clause with 
    | None -> None
    | Some e -> Some (fst <| (no_guard env <| tc_total_exp (Env.set_expected_typ pat_env Tc.Util.t_bool) e)) in
  let branch, c = tc_exp pat_env branch in
  let guard_exp = Util.bvd_to_exp guard_x pat_t in
  let c = 
    let eqs : formula = List.fold_left (fun disj e -> Util.mk_disj disj (Util.mk_eq guard_exp e)) 
                    (Util.mk_eq guard_exp (List.hd disj_exps))
                    (List.tl disj_exps) in
    let guard = match when_clause with
      | None -> eqs
      | Some g -> Util.mk_conj eqs (Util.mk_eq g Const.exp_true_bool) in
    Tc.Util.close_comp_typ env bindings <| Tc.Util.weaken_precondition env c (Guard guard) in
  (pat, when_clause, branch), c 

and tc_kind_trivial env k : knd = 
  match tc_kind env k with 
    | k, Trivial -> k
    | _ -> raise (Error(Tc.Errors.kind_has_a_non_trivial_precondition k, Env.get_range env));

and tc_typ_trivial env t : typ * knd = 
  let t, k, g = tc_typ env t in
  match g with 
    | Trivial -> t, k
    | _ -> raise (Error(Tc.Errors.type_has_a_non_trivial_precondition t, range_of_typ t (Env.get_range env)))

and tc_typ_check_trivial env t k = 
  let t, f = tc_typ_check env t k in
  match f with 
    | Trivial -> t
    | _ -> raise (Error(Tc.Errors.type_has_a_non_trivial_precondition t, range_of_typ t (Env.get_range env)))

and tc_total_exp env e : exp * typ * guard = 
  let e, c = tc_exp env e in
  match Tc.Rel.sub_comp_typ env c (Util.total_comp c.result_typ (Env.get_range env)) with 
    | Some g -> e, c.result_typ, g
    | _ -> raise (Error(Tc.Errors.expected_pure_expression c, Tc.Env.get_range env))


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

let kt k1 k2 = Kind_tcon(None, k1, k2, false)
let kd t k = Kind_dcon(None, t, k, false)
let a_kwp_a m s = match s with 
  | Kind_tcon(Some a, Kind_type, Kind_tcon(None, kwp, Kind_tcon(None, kwlp, Kind_effect, false), false), false) -> a, kwp
  | _ -> raise (Error(Tc.Errors.unexpected_signature_for_monad m s, range_of_lid m))

let rec tc_monad_decl env m =  
  let mk = tc_kind_trivial env m.signature in 
  let a, kwp_a = a_kwp_a m.mname mk in 
  let a_typ = Util.bvd_to_typ a Kind_type in
  let b = Util.new_bvd (Some <| range_of_lid m.mname) in 
  let b_typ = Util.bvd_to_typ b Kind_type in
  let kwp_b = Util.subst_kind [Inl(a, b_typ)] kwp_a in
  let kwlp_a = kwp_a in
  let kwlp_b = kwp_b in
  let ret = 
    let expected_k = Kind_tcon(Some a, Kind_type, kd a_typ kwp_a, false) in
    tc_typ_check_trivial env m.ret expected_k in
  let bind_wp, bind_wlp =
    let expected_k = Kind_tcon(Some a, Kind_type, Kind_tcon(Some b, Kind_type, kt kwp_a (kt kwlp_a (kt (kd a_typ kwp_b) (kt (kd a_typ kwlp_b) kwp_b))), false), false) in
    tc_typ_check_trivial env m.bind_wp expected_k, tc_typ_check_trivial env m.bind_wlp expected_k in
  let ite_wp =
    let expected_k = Kind_tcon(Some a, Kind_type, kt Kind_type (kt kwp_a (kt kwlp_a (kt kwp_a (kt kwlp_a kwp_a)))), false) in
    tc_typ_check_trivial env m.ite_wp expected_k in
  let ite_wlp =
    let expected_k = Kind_tcon(Some a, Kind_type, kt Kind_type (kt kwlp_a (kt kwlp_a kwlp_a)), false) in
    tc_typ_check_trivial env m.ite_wlp expected_k in
  let imp_wp = 
    let expected_k = Kind_tcon(Some a, Kind_type, kt kwp_a (kt kwp_a Kind_type), false) in
    tc_typ_check_trivial env m.imp_wp expected_k in
  let close_wp = 
    let b = Util.new_bvd None in
    let expected_k = 
      Kind_tcon(Some a, Kind_type, 
        Kind_tcon(Some b, Kind_type, 
          Kind_tcon(None, Kind_dcon(None, Util.bvd_to_typ b Kind_type, kwp_a, false), 
                          kwp_a, false), false), false) in
    tc_typ_check_trivial env m.close_wp expected_k in
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
    imp_wp=imp_wp;
    close_wp=close_wp} in 
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
        let kwp_a_tgt = Util.subst_kind [Inl(b, Util.bvd_to_typ a Kind_type)] kwp_b_tgt in
        let expected_k = Kind_tcon(Some a, Kind_type, kt kwp_a_src kwp_a_tgt, false) in
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
        | Kind_uvar _ -> Rel.trivial <| Tc.Rel.keq env None k Kind_type
        | _ -> () in 
      let env = Tc.Env.push_sigelt env se in
      se, env
  
    | Sig_typ_abbrev(lid, tps, k, t, tags, r) -> 
      let env = Tc.Env.set_range env r in
      let tps, env = tc_tparams env tps in
      let t, k1 = tc_typ_trivial env t in 
      let k2 = tc_kind_trivial env k in 
      Rel.trivial <| Rel.keq env (Some t) k1 k2;
      let se = Sig_typ_abbrev(lid, tps, k1, t, tags, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
  
    | Sig_datacon(lid, t, tname, r) -> 
      let env = Tc.Env.set_range env r in
      let t = tc_typ_check_trivial env t Kind_type in 
      let args, result_t = Util.collect_formals t in
      let constructed_t, _ = Util.flatten_typ_apps result_t in (* TODO: check that the tps in tname are the same as here *)
      let _ = match destruct constructed_t tname with 
        | Some _ -> ()
        | _ -> raise (Error (Tc.Errors.constructor_builds_the_wrong_type (Util.fvar lid (range_of_lid lid)) constructed_t (Util.ftv tname), range_of_lid lid)) in
      let se = Sig_datacon(lid, t, tname, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
  
    | Sig_val_decl(lid, t, tag, ltag, r) -> 
      let env = Tc.Env.set_range env r in
      let t = tc_typ_check_trivial env t Kind_type in 
      let se = Sig_val_decl(lid, t, tag, ltag, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
  
    | Sig_assume(lid, phi, qual, tag, r) ->
      let env = Tc.Env.set_range env r in
      let phi = tc_typ_check_trivial env phi Kind_type in 
      let se = Sig_assume(lid, phi, qual, tag, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
  
    | Sig_logic_function(lid, t, tags, r) -> 
      let env = Tc.Env.set_range env r in
      let t = tc_typ_check_trivial env t Kind_type in 
      let se = Sig_logic_function(lid, t, tags, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
  
    | Sig_let(lbs, r) -> 
      let env = Tc.Env.set_range env r in
      let lbs' = snd lbs |> List.fold_left (fun lbs lb -> 
        let lb = match lb with 
          | (Inl _, _, _) -> failwith "impossible"
          | (Inr l, t, e) -> 
            match Tc.Env.try_lookup_val_decl env l with 
              | None -> 
                let t = Tc.Util.extract_lb_annotation env t e in
                (Inr l, t, e)
              | Some t' -> match t.t with 
                  | Typ_unknown -> 
                   // Util.print_string (Util.format2 "Looked up val %s got type %s\n" l.str (Print.typ_to_string t'));
                    (Inr l, t', e)
                  | _ -> raise (Error (Tc.Errors.inline_type_annotation_and_val_decl l, range_of_lid l)) in
        lb::lbs) [] in
      let lbs' = List.rev lbs' in
      let e = Exp_let((fst lbs, lbs'), Exp_constant(Syntax.Const_unit)) in
      let se = match tc_exp env e with 
        | Exp_let(lbs, _), c -> (* TODO: Call the solver here! *) 
          Sig_let(lbs, r)
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
           let k = match k with 
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
          let tt = Util.close_with_lam tps (withkind kun <| Typ_ascribed(t, k)) in
          let tt, _ = tc_typ_trivial env1 tt in
          let tps, t = 
            let rec aux tps t =
            let t = compress_typ t in 
             match tps, t.t with 
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
      let env = Tc.Env.push_sigelt env (Sig_bundle(tycons@abbrevs@rest, r)) in 
      se, env

and tc_decls (env:Tc.Env.env) ses = 
  let ses, env = List.fold_left (fun (ses, (env:Tc.Env.env)) se ->
//  if (env.curmodule.str <> "Prims")
//  //then Util.print_string (Util.format1 "Checking sigelt\t%s\n" (Util.lids_of_sigelt se |> List.map (fun l -> l.str) |> String.concat(", ")))
//  then Util.print_string (Util.format1 "Checking sigelt\t%s\n" (Print.sigelt_to_string se))
//  else ();
  let se, env = tc_decl env se in 
//  if (env.curmodule.str <> "Prims")
//  then Util.print_string (Util.format1 "Checked sigelt\n\t%s\n" (Print.sigelt_to_string_short se))// (Print.sigelt_to_string se))
//  else ();
  se::ses, env) ([], env) ses in
  List.rev ses, env 

let tc_modul env modul = 
  let env = Tc.Env.set_current_module env modul.name in 
  let ses, env = tc_decls env modul.declarations in 
  let modul = {name=modul.name; declarations=ses; exports=[]} in (* TODO: handle exports *) 
  let env = Tc.Env.finish_module env modul in
  modul, env

let check_modules mods = 
   let fmods, _ = mods |> List.fold_left (fun (mods, env) m -> 
    let m, env = tc_modul env m in 
    (m::mods, env)) ([], Tc.Env.initial_env Const.prims_lid) in
   List.rev fmods
 
