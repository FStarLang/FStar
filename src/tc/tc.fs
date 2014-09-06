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
let no_inst env = {env with Env.instantiate_targs=false; Env.instantiate_vargs=false}

let norm_t env t = Tc.Normalize.norm_typ [Normalize.Beta; Normalize.SNComp] env t
let norm_k env k = Tc.Normalize.norm_kind [Normalize.Beta; Normalize.SNComp] env k
let norm_c env c = Tc.Normalize.norm_comp [Normalize.Beta; Normalize.SNComp] env c
let fxv_check env kt fvs =
    let rec aux norm kt = 
        if Util.set_is_empty fvs then ()
        else let fvs' = match kt with 
                | Inl k -> Util.freevars_kind (if norm then norm_k env k else k)
                | Inr t -> Util.freevars_typ (if norm then norm_t env t else t) in
                let a = Util.set_intersect fvs fvs'.fxvs in 
                if Util.set_is_empty a then ()
                else if not norm 
                then aux true kt
                else let escaping = Util.set_elements a |> List.map (fun x -> Print.strBvd x.v) |> String.concat ", " in
                    raise (Error(Util.format1 "Variables %s escape because of impure applications; add explicit let-bindings" escaping, 
                                    Env.get_range env)) in
    aux false kt
        
let maybe_push_binding env b =
  if is_null_binder b then env
  else match fst b with 
      | Inl a -> 
        let b = Tc.Env.Binding_typ(a.v, a.sort) in
        Env.push_local_binding env b
      | Inr x -> 
        let b = Tc.Env.Binding_var(x.v, x.sort) in
        Env.push_local_binding env b

let maybe_make_subst = function 
  | Inl(Some a, t) -> [Inl(a,t)]
  | Inr(Some x, e) -> [Inr(x,e)]
  | _ -> []

let maybe_alpha_subst s b1 b2 = 
    if is_null_binder b1 then s 
    else match fst b1, fst b2 with 
        | Inl a, Inl b -> if Util.bvar_eq a b then s else extend_subst (Inl(a.v, btvar_to_typ b)) s
        | Inr x, Inr y -> if Util.bvar_eq x y then s else extend_subst (Inr(x.v, bvar_to_exp y)) s
        | _ -> failwith "impossible"

let maybe_extend_subst s b v =  
    if is_null_binder b then s 
    else match fst b, v with
          | Inl a, Inl t -> extend_subst (Inl(a.v,t)) s
          | Inr x, Inr e -> extend_subst (Inr(x.v,e)) s
          | _ -> failwith "Impossible"

let value_check_expected_typ env e tc : exp * comp =
  let c = match tc with 
    | Inl t -> (match t.n with 
                  | Typ_fun _ -> mk_Total t
                  | _ -> Tc.Util.return_value env t e)
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
   | Some t ->
     Tc.Util.weaken_result_typ env e c t

let check_expected_effect env (copt:option<comp>) (e, c) : exp * comp * guard = 
  match copt with 
    | None -> e, c, Trivial
    | Some c' -> //expected effects should already be normalized
       let c = norm_c env c in
       Tc.Util.check_comp env e c c' 
    
let no_guard env (te, kt, f) = match f with
  | Trivial -> te, kt
  | NonTrivial f -> raise (Error(Tc.Errors.unexpected_non_trivial_precondition_on_term f, Env.get_range env)) 

let binding_of_lb x t = match x with 
  | Inl bvd -> Env.Binding_var(bvd, t)
  | Inr lid -> Env.Binding_lid(lid, t)

let print_expected_ty env = match Env.expected_typ env with 
    | None -> printfn "Expected type is None"
    | Some t -> printfn "Expected type is %s" (Print.typ_to_string t)
    
let rec tc_kind env k : knd * guard = 
  let k = Util.compress_kind k in 
  let w f = f k.pos in
  match k.n with
  | Kind_lam _ 
  | Kind_delayed _ -> failwith "impossible"

  | Kind_type
  | Kind_effect -> k, Trivial
  | Kind_uvar (u, args) -> 
    if debug env then printfn "(%s) - Checking kind %s" (Range.string_of_range k.pos) (Print.kind_to_string k);
    let env, _ = Tc.Env.clear_expected_typ env in
    let args, g = tc_args env args in
    w <| mk_Kind_uvar(u, args), g 

  | Kind_abbrev(kabr, k) -> 
    let k, f = tc_kind env k in 
    let args, g = tc_args env <| snd kabr in
    let kabr = (fst kabr, args) in
    let kk = w <| mk_Kind_abbrev(kabr, k) in 
    kk, Tc.Rel.conj_guard f g

  | Kind_arrow(bs, k) -> 
    let bs, env, g = tc_binders env bs in
    let k, f = tc_kind env k in
    let f = Tc.Util.close_guard bs f in
    w <| mk_Kind_arrow(bs, k), Rel.conj_guard g f

  | Kind_unknown -> 
    Tc.Util.new_kvar env, Trivial

and tc_vbinder env x = 
    let t, g = tc_typ_check env x.sort ktype in
    let x = {x with sort=t} in
    let env' = maybe_push_binding env (v_binder x) in
    x, env', g 

and tc_binders env bs = 
  let bs, env, g = bs |> List.fold_left (fun (bs, env, g) (b, imp) -> match b with 
    | Inl a -> 
      let k, g' = tc_kind env a.sort in
      let b = Inl ({a with sort=k}), imp in
      let env' = maybe_push_binding env b in
      b::bs, env', Tc.Rel.conj_guard g g'

    | Inr x ->
      let x, env, g' = tc_vbinder env x in
      (Inr x, imp)::bs, env, Tc.Rel.conj_guard g g') ([], env, Trivial) in
 List.rev bs, env, g

and tc_args env args : args * guard = 
   List.fold_right (fun (arg, imp) (args, g) -> match arg with 
    | Inl t -> 
        let t, _, g' = tc_typ env t in 
        (Inl t, imp)::args, Tc.Rel.conj_guard g g'
    | Inr e -> 
        let e, _, g' = tc_total_exp env e in
        (Inr e, imp)::args, Tc.Rel.conj_guard g g') args ([], Trivial)

   
and tc_comp env c = 
  let c = Normalize.comp_comp env c in
  match c.n with 
    | Flex(u, t) -> 
      let t, g = tc_typ_check env t ktype in
      let u, g' = tc_typ_check env u (mk_Kind_arrow([null_t_binder ktype], keffect) t.pos) in
      mk_Flex(u, t), Tc.Rel.conj_guard g g'

    | Total t -> 
      let t, g = tc_typ_check env t ktype in
      mk_Total t, g

    | Comp c -> 
      let kc =  Tc.Env.lookup_typ_lid env c.effect_name in
      let head = Util.ftv c.effect_name kc in
      let tc = mk_Typ_app(head, (targ c.result_typ)::c.effect_args) kun c.result_typ.pos in
      let tc, f = tc_typ_check env tc keffect in 
      let _, args = Util.head_and_args tc in
      let res, args = match args with 
        | (Inl res, _)::args -> res, args
        | _ -> failwith "Impossible" in
      mk_Comp ({c with 
          result_typ=res;
          effect_args=args}), f

    | Rigid _
    | Flex _ -> failwith "Impossible"
  
and tc_typ env (t:typ) : typ * knd * guard = 
  let env = Tc.Env.set_range env t.pos in
  let w k = syn t.pos k in
  let t = Util.compress_typ t in
  let top = t in
  match t.n with 
  | Typ_btvar a -> 
    let k = Env.lookup_btvar env a in
    let a = {a with sort=k} in
    w k <| mk_Typ_btvar a, k, Trivial

  | Typ_const i when (lid_equals i.v Const.allTyp_lid || lid_equals i.v Const.exTyp_lid) -> 
    (* Special treatment for ForallTyp and ExistsTyp, giving them polymorphic kinds *)
    let k = Tc.Util.new_kvar env in
    let qk = Util.allT_k k in
    {t with tk=qk}, qk, Trivial 
    
  | Typ_const i -> 
    let k = Env.lookup_typ_lid env i.v in 
    {t with tk=k}, k, Trivial
     
  | Typ_fun(bs, cod) -> 
    let bs, env, g = tc_binders env bs in 
    let cod, f = tc_comp env cod in
    w ktype <| mk_Typ_fun(bs, cod), ktype, Rel.conj_guard g (Tc.Util.close_guard bs f)

  | Typ_lam(bs, t) -> 
    let bs, env, g = tc_binders env bs in
    let t, k, f = tc_typ env t in
    let k = mk_Kind_arrow(bs, k) top.pos in
    w k <| mk_Typ_lam(bs, t), k, Rel.conj_guard g <| Tc.Util.close_guard bs f
 
  | Typ_refine(x, phi) -> 
    let x, env, f1 = tc_vbinder env x in 
    let phi, f2 = tc_typ_check env phi ktype in
    w ktype <| mk_Typ_refine(x, phi), ktype, Rel.conj_guard f1 (Tc.Util.close_guard [v_binder x] f2)

  | Typ_app(head, args) -> 
    let head, k1, f1 = tc_typ env head in 
    let args, f2 = tc_args env args in
    if debug env then printfn "(%s) Destructing arrow kind: %s\n" (Range.string_of_range top.pos) (Print.kind_to_string k1);
    let imps, formals, kres = Tc.Util.destruct_arrow_kind env head k1 args in
    let rec check_args subst g formals args = match formals, args with 
      | [], [] -> g, Util.subst_kind subst kres
      | formal::formals, actual::actuals -> 
        begin match formal, actual with 
            | (Inl a, _), (Inl t, _) -> 
              let env = Env.set_range env t.pos in 
              let g' = Tc.Rel.subkind env t.tk (Util.subst_kind subst a.sort) in
              let subst = maybe_extend_subst subst formal (Inl t) in
              check_args subst (Rel.conj_guard g g') formals actuals

            | (Inr x, _), (Inr v, _) -> 
              let env = Env.set_range env t.pos in 
              let tx = Util.subst_typ subst x.sort in
              if debug env then printfn "(%s) Checking arg %s:%s against type %s" (Range.string_of_range v.pos) (Print.exp_to_string v) (Print.typ_to_string v.tk) (Print.typ_to_string tx); 
              let _, g' = Tc.Util.check_and_ascribe env v v.tk tx in
              let subst = maybe_extend_subst subst formal (Inr v) in
              check_args subst (Rel.conj_guard g g') formals actuals

            | (Inl _, _), (Inr v, _) ->
              raise (Error("Expected a type; got an expression", v.pos))
            
            | (Inr _, _), (Inl t, _) ->
              raise (Error("Expected an expression; got a type", t.pos)) 
        end 

      | _, [] -> g, Util.subst_kind subst (mk_Kind_arrow(formals, kres) kres.pos) //partial app

      | [], _ -> raise (Error("Too many arguments to type", top.pos)) in
    let g, k = check_args [] (Rel.conj_guard f1 f2) formals args in
    let t = mk_Typ_app(head, imps@args) k top.pos in
    t, k, g
  
  | Typ_ascribed(t1, k1) -> 
    let k1, f1 = tc_kind env k1 in 
    let t1, f2 = tc_typ_check env t1 k1 in
    w k1 <| mk_Typ_ascribed'(t1, k1), k1, Rel.conj_guard f1 f2

  | Typ_uvar(u, k1) -> 
    let s = compress_typ t in 
    (match s.n with 
        | Typ_uvar _ -> 
          let k1, g = tc_kind env k1 in
          w k1 <| mk_Typ_uvar'(u, k1), k1, g
        | _ -> tc_typ env s)
        
  | Typ_meta (Meta_named(t, l)) -> 
    let t, k, f = tc_typ env t in 
    mk_Typ_meta(Meta_named(t, l)), k, f

  | Typ_meta (Meta_pattern(qbody, pats)) -> 
    let quant, f = tc_typ_check env qbody ktype in 
    let pats, g = tc_args env pats in
    mk_Typ_meta(Meta_pattern(quant, pats)), quant.tk, Rel.conj_guard f g
 
  | Typ_unknown -> 
    let vars = Env.binders env in
    let k, _ = Rel.new_kvar top.pos vars in
    let t, _ = Rel.new_tvar top.pos vars k in
    t, k, Trivial

  | _ -> failwith (Util.format1 "Unexpected type : %s\n" (Print.typ_to_string t)) 

and tc_typ_check env t (k:knd) : typ * guard = 
  let t, k', f = tc_typ env t in
  let env = Env.set_range env t.pos in
  let f' = Rel.subkind env k' k in
  t, Rel.conj_guard f f'       

and tc_value env e : exp * comp = 
  let env = Env.set_range env e.pos in
  let top = e in
  match e.n with
  | Exp_uvar(_, t1) -> 
    value_check_expected_typ env e (Inl t1)
  
  | Exp_bvar x -> 
    let t = Env.lookup_bvar env x in
    let e = mk_Exp_bvar({x with sort=t}) t e.pos in
    let e, t = Tc.Util.maybe_instantiate env e t in
    value_check_expected_typ env e (Inr (mk_Total t))

  | Exp_fvar(v, dc) -> 
    let t = Env.lookup_lid env v.v in
    let e, t = Tc.Util.maybe_instantiate env e t in 
    //printfn "Instantiated type of %s to %s\n" (Print.exp_to_string e) (Print.typ_to_string t);
    if dc && not(Env.is_datacon env v.v)
    then raise (Error(Util.format1 "Expected a data constructor; got %s" v.v.str, Tc.Env.get_range env))
    else value_check_expected_typ env e (Inr (mk_Total t))

  | Exp_constant c -> 
    let t = Tc.Util.typing_const env c in
    value_check_expected_typ env ({e with tk=t}) (Inl t)

  | Exp_abs(bs, body) ->  (* This is the dual of the treatment of application ... see the Exp_app case below. *)
    let fail t =  raise (Error(Tc.Errors.expected_a_term_of_type_t_got_a_function t top, top.pos)) in
    let rec expected_function_typ t0 = match t0 with 
        | None -> (* no expected type; just build a function type from the binders in the term *)
            let bs, envbody, g = tc_binders env bs in
            let res_t = Rel.new_tvar body.pos (Env.binders env) ktype |> fst in
            let c = Rel.new_cvar body.pos (Env.binders envbody) res_t |> fst in
            let envbody = Env.set_expected_typ envbody res_t in
            mk_Typ_fun(bs,c) ktype top.pos, bs, c, envbody, g

        | Some t -> 
           let t = compress_typ t in
           let rec as_function_typ norm t =
               match t.n with 
                | Typ_uvar _
                | Typ_app({n=Typ_uvar _}, _) -> (* expected a uvar; build a function type from the term and unify with it *)
                  let tfun, bs, c, envbody, g = expected_function_typ None in 
                  trivial <| Rel.teq env t tfun;
                  t, bs, c, envbody, g

                | Typ_fun(bs', c) -> (* the main interesting bit here is that the expected type may have additional type binders *)
                  
                  let rec tc_binders (out, env, g, subst) bs_annot bs = match bs_annot, bs with
                    | [], [] -> List.rev out, env, g, Util.subst_comp subst c 
                    
                    | hdannot::tl_annot,  hd::tl -> 
                      begin match hdannot, hd with 
                            | (Inl _, _), (Inr _, _) -> (* expected type includes a type-binder; add a type abstraction to the term *)
                              let env = maybe_push_binding env hdannot in
                              tc_binders (hdannot::out, env, g, subst) tl_annot tl 
                              
                            | (Inl a, _), (Inl b, imp) -> 
                              let k, g1 = tc_kind env b.sort in
                              let g2 = Rel.keq env None (Util.subst_kind subst a.sort) k in
                              let g = Rel.conj_guard g (Rel.conj_guard g1 g2) in
                              let b = Inl ({b with sort=k}), imp in
                              let env = maybe_push_binding env b in
                              let subst = maybe_alpha_subst subst hdannot b in 
                              tc_binders (b::out, env, g, subst) tl_annot tl 

                            | (Inr x, _), (Inr y, imp) -> 
                              let t, _, g1 = tc_typ env y.sort in
                              let g2 = Rel.teq env (Util.subst_typ subst x.sort) t in
                              let g = Rel.conj_guard g (Rel.conj_guard g1 g2) in
                              let b = Inr ({y with sort=t}), imp in
                              let env = maybe_push_binding env b in
                              let subst = maybe_alpha_subst subst hdannot b in 
                              tc_binders (b::out, env, g, subst) tl_annot tl 

                            | _ -> fail t
                      end
                    
                    | _ -> raise (Error(Tc.Errors.expected_a_term_of_type_t_got_a_function t top, top.pos)) in

                 let bs, envbody, g, c = tc_binders ([], env, Trivial, []) bs' bs in
                 let envbody = Tc.Env.set_expected_typ envbody (Util.comp_result c) in
                 t, bs, c, envbody, g

                | _ -> (* expected type is not a function; try normalizing it before giving up *)
                  if not norm
                  then as_function_typ true (Normalize.normalize env t) 
                  else fail t in
           as_function_typ false t in

    let tfun, bs, c, envbody, g = expected_function_typ (Tc.Env.expected_typ env) in
    let body, cbody = tc_exp envbody body in 
    let body, _, guard = check_expected_effect envbody (Some c) (body, cbody) in
    Tc.Util.discharge_guard envbody (Rel.conj_guard g guard);
    syn e.pos tfun <| mk_Exp_abs(bs, body), mk_Total tfun

  | _ -> 
    failwith (Util.format1 "Unexpected value: %s" (Print.exp_to_string e))

and tc_exp env e : exp * comp = 
  let env = if e.pos=dummyRange then env else Env.set_range env e.pos in
  let w c = syn e.pos (Util.comp_result c) in
  let top = e in
  match e.n with
  | Exp_meta(Meta_uvar_e_app _) -> failwith "Impossible"

  | Exp_delayed _ -> tc_exp env (compress_exp e)

  | Exp_uvar _ 
  | Exp_bvar _  
  | Exp_fvar _ 
  | Exp_constant _  
  | Exp_abs _  -> tc_value env e 

  | Exp_ascribed(e1, t1) -> 
    let t1, f = tc_typ_check env t1 ktype in 
    let e1, c = tc_exp (Env.set_expected_typ env t1) e1 in
    comp_check_expected_typ env (w c <| mk_Exp_ascribed'(e1, t1)) (Tc.Util.strengthen_precondition env c f)

//  | Exp_meta(Meta_uvar_e_app(e, (u,t))) -> 
//    let e, c = tc_exp env e in 
//    mk_Exp_meta(Meta_uvar_e_app(e, (u,t))), c
    

  | Exp_meta(Meta_desugared(e, Data_app)) -> 
    (* These are (potentially) values, but constructor types 
       already have an (Tot) effect annotation on their co-domain. 
       So, we can treat them as normal applications. Except ...  *)
//    let env = instantiate_both env in
    let d, args = Util.head_and_args_e e in (* if there are no user-provided type applications, try to infer them as below ... *)
    begin match args with 
        | (Inl _, _)::_ -> (* user provided typ argument *)
            let e, c = tc_exp env e in 
            mk_Exp_meta(Meta_desugared(e, Data_app)), c

        | _ -> 
        let env1, topt = Env.clear_expected_typ env in 
        let t = Env.expected_typ env in 
    
        (* The main subtlety with bidirectional typing is here:
            Consider typing (e1, e2) as (x:t * t')
            It is desugared to (MkTuple2 '_u1 '_u2 e1 e2), and we have to compute the instantiations for '_u1 and '_u2.
            The idea is to push the result type (Tuple2 t (\x:t. t')) down to the constructor MkTuple2
            and then instantiating MkTuple2's arguments using the expected type.
            That's what the Meta_datainst(d, topt) does ... below. 
            Once we compute good instantiations for '_u1 and '_u2, the rest follows as usual. *)
        let d = mk_Exp_meta(Meta_datainst(d, topt)) in
        let e = match args with 
            | [] -> d 
            | _ -> mk_Exp_app(d, args) tun top.pos in
        let e, c = tc_exp env1 e in
        let e = match e.n with  //reassociate inferred targs
            | Exp_app({n=Exp_app(hd, targs)}, args) -> mk_Exp_app(hd, targs@args) e.tk e.pos 
            | _ -> e in
        comp_check_expected_typ env (mk_Exp_meta(Meta_desugared(e, Data_app))) c
    end

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
    
    (* For compatibility with ML: dtuples without a type annotation default to their non-dependent versions *)
    let maybe_default_dtuple_type env tres topt  = 
      let tconstr, args = Util.head_and_args tres in
      if Util.is_dtuple_constructor tconstr 
      then let tup = Tc.Util.mk_basic_dtuple_type env (List.length args) in
            let _ = match topt with 
                    | None -> ()
                    | Some t -> Tc.Rel.trivial_subtype env None t tup in
            Tc.Rel.trivial_subtype env None tres tup in
     
    let dc, c_dc = tc_value (instantiate_both env) dc in 
    let t_dc = Util.comp_result c_dc in
    let tres = match Util.function_formals t_dc with 
        | Some (_, c) -> Util.comp_result c
        | _ -> t_dc in
    begin match topt with 
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
              Tc.Rel.trivial_subtype env None tres t_expected
    end;
    dc, c_dc (* NB: Removed the Meta_datainst tag on the way up---no other part of the compiler sees Meta_datainst *)

  | Exp_app(f, args) ->
    let env0 = env in
    let env = Tc.Env.clear_expected_typ env |> fst |> instantiate_both in 
    if debug env then printfn "(%s) Checking app %s" (Range.string_of_range top.pos) (Print.exp_to_string top);
    let f, cf = tc_exp (no_inst env) f in
    let tf = Util.comp_result cf in
    if debug env then printfn "(%s) Type of head is %s" (Range.string_of_range f.pos) (Print.typ_to_string tf);
    let argpos = function 
        | Inl t, _ -> t.pos
        | Inr e, _ -> e.pos in
    let rec check_function_app norm tf = match tf.n with 
        | Typ_uvar _
        | Typ_app({n=Typ_uvar _}, _) ->
          let rec tc_args env args : (args * list<comp>) = match args with
                | [] -> ([], [])
                | (Inl t, _)::_ -> 
                  raise (Error("Explicit type applications on a term with unknown type; add an annotation?", t.pos))
                | (Inr e, imp)::tl -> 
                  let e, c = tc_exp env e in 
                  let args, comps = tc_args env tl in 
                  (Inr e, imp)::args, c::comps in
          (* Infer: t1 -> ... -> tn -> ML ('u 'a1 ... 'am), 
                    where ti are the result types of each arg
                    and  'ai are the free type variables in the environment *)
          let args, comps = tc_args env args in 
          let bs = null_binders_of_args args in
          let ai = Env.binders env |> List.filter (function Inl _, _ -> true | _ -> false) in
          let cres = Util.ml_comp (Rel.new_tvar f.pos ai ktype |> fst) top.pos in
          trivial <| Rel.teq env tf (mk_Typ_fun(bs, cres) ktype tf.pos);
          let comp = List.fold_right (fun c out -> Tc.Util.bind env c (None, out)) (cf::comps) cres in
          mk_Exp_app(f, args) (Util.comp_result comp) top.pos, comp

        | Typ_fun(bs, c) -> 
          let vars = Tc.Env.binders env in
          let rec tc_args (subst, outargs, comps, g, fvs) bs args = match bs, args with 
            | (Inl a, _)::rest, (Inr e, _)::_ -> (* instantiate a type argument *) 
              let k = Util.subst_kind subst a.sort in
              fxv_check env (Inl k) fvs;
              let targ = fst <| Tc.Rel.new_tvar e.pos vars k in
              if debug env then printfn "Instantiating %s to %s" (Print.strBvd a.v) (Print.typ_to_string targ);
              let subst = extend_subst (Inl(a.v, targ)) subst in
              tc_args (subst, (Inl targ,true)::outargs, comps, g, fvs) rest args

            | (Inr x, true)::rest, (_, false)::_ -> (* instantiate an implicit value arg *)
              let t = Util.subst_typ subst x.sort in
              fxv_check env (Inr t) fvs;
              let varg = (fst <| Tc.Rel.new_evar (argpos <| List.hd args) vars t) in
              let subst = extend_subst (Inr(x.v, varg)) subst in
              tc_args (subst, (Inr varg, true)::outargs, comps, g, fvs) rest args

            | (Inl a, _)::rest, (Inl t, _)::rest' -> (* a concrete type argument *)
              let k = Util.subst_kind subst a.sort in 
              fxv_check env (Inl k) fvs;
              let t, g' = tc_typ_check env t k in
              let subst = maybe_extend_subst subst (List.hd bs) (Inl t) in
              tc_args (subst, (targ t)::outargs, comps, Rel.conj_guard g g', fvs) rest rest'

            | (Inr x, _)::rest, (Inr e, _)::rest' -> (* a concrete exp argument *)
              let targ = Util.subst_typ subst x.sort in
              fxv_check env (Inr targ) fvs;
              let env = Tc.Env.set_expected_typ env targ in
              if debug env then printfn "Checking arg (%s) %s at type %s" (Print.tag_of_exp e) (Print.exp_to_string e) (Print.typ_to_string targ);
              let e, c = tc_exp env e in 
              if Util.is_total_comp c 
              then let subst = maybe_extend_subst subst (List.hd bs) (Inr e) in
                   tc_args (subst, (varg e)::outargs, comps, g, fvs) rest rest'
              else if Tc.Util.is_pure env c 
              then let g' = Util.must <| Tc.Rel.sub_comp env c (mk_Total (Util.comp_result c)) in
                   let subst = maybe_extend_subst subst (List.hd bs) (Inr e) in
                   tc_args (subst, (varg e)::outargs, comps, Rel.conj_guard g g', fvs) rest rest'
              else if is_null_binder (List.hd bs)
              then tc_args (subst, (varg e)::outargs, (None, c)::comps, g, fvs) rest rest'
              else tc_args (subst, (varg e)::outargs, (Some <| Env.Binding_var(x.v, x.sort), c)::comps, g, Util.set_add x fvs) rest rest'

            | _, [] -> (* full or partial application *) 
              let cres = match bs with 
                | [] -> Util.subst_comp subst c (* full app *)
                | _ -> mk_Total  (Util.subst_typ subst <| mk_Typ_fun(bs, c) ktype top.pos) (* partial app *) in
              let comp = List.fold_left (fun out c -> fst c, Tc.Util.bind env (snd c) out) (None, cres) comps in
              let comp = Tc.Util.bind env cf comp in
              let comp = Tc.Util.strengthen_precondition env comp g in
              mk_Exp_app(f, List.rev outargs) (Util.comp_result comp) top.pos, comp
               
            | (Inr _, _)::_, (Inl _, _)::_ ->
              raise (Error(Util.format1 "Unexpected type argument (%s)" (Print.exp_to_string top), argpos (List.hd args)))

            | [], arg::_ -> (* too many args ... maybe c returns a function? *) 
              raise (Error(Util.format1 "Too many arguments to function of type %s" (Print.typ_to_string tf), argpos arg)) in
         
          tc_args ([], [], [], Trivial, no_fvs.fxvs) bs args
                  
        | _ -> 
            if not norm
            then check_function_app true (Normalize.normalize env tf)
            else raise (Error(Tc.Errors.expected_function_typ tf, f.pos)) in

    let e, c = check_function_app false tf in
    let c = if !Options.verify && (Util.is_primop f || Util.is_total_comp c)
            then Tc.Util.maybe_assume_result_eq_pure_term env e c 
            else c in
    if debug env then printfn "(%s) About to check %s against expected typ %s" (Range.string_of_range e.pos) (Print.typ_to_string (Util.comp_result (Tc.Normalize.normalize_comp env0 c))) (Env.expected_typ env0 |> (fun x -> match x with None -> "None" | Some t-> Print.typ_to_string t));
    comp_check_expected_typ env0 e c 
          
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
    let t, f = tc_typ_check env t ktype in
    let t = norm_t env t in
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
      let e, t = Tc.Util.extract_lb_annotation true env t e in //NS: pull inline annotation to force the ML monad here; remove once we have better termination checks
      let t = tc_typ_check_trivial env0 t ktype |> norm_t env in
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
    let disc = mk_Exp_app(Util.fvar disc (range_of_lid f.v), [varg <| guard_exp]) tun guard_exp.pos in
    let e, _, _ = tc_total_exp (Env.set_expected_typ guard_env Tc.Util.t_bool) disc in
    Util.mk_eq e Const.exp_true_bool in
  let gg =
    let discs = disj_exps |> List.collect (fun e -> 
      let e = compress_exp e in 
      match e.n with 
      | Exp_uvar _
      | Exp_app({n=Exp_uvar _}, _) 
      | Exp_bvar _ -> [Util.ftv Const.true_lid ktype]
      | Exp_constant _ -> [Util.mk_eq guard_exp e]
      | Exp_fvar(f, _) 
      | Exp_app({n=Exp_fvar(f, _)}, _) ->  [discriminate f]
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
  else let c = norm_c env c in 
       match Tc.Rel.sub_comp env c (Util.total_comp (Util.comp_result c) (Env.get_range env)) with 
        | Some g -> e, Util.comp_result c, g
        | _ -> raise (Error(Tc.Errors.expected_pure_expression e c, e.pos))


(*****************Type-checking the signature of a module*****************************)

let tc_tparams env tps : (list<tparam> * Env.env) = 
	let tps', env = List.fold_left (fun (tps, env) tp -> match tp with 
	  | Tparam_typ(a, k) -> 
				let k = tc_kind_trivial env k |> norm_k env in 
				let env = Tc.Env.push_local_binding env (Env.Binding_typ(a, k)) in
				Tparam_typ(a,k)::tps, env
	  | Tparam_term(x, t) -> 
				let t, _ = tc_typ_trivial env t in
                let t = norm_t env t in 
				let env = Tc.Env.push_local_binding env (Env.Binding_var(x, t)) in
				Tparam_term(x, t)::tps, env) ([], env) tps in
		List.rev tps', env 
//
//let kt k1 k2 = mk_Kind_tcon(None, k1, k2, false) k2.pos
//let kd t k = mk_Kind_dcon(None, t, k, false) k.pos
let a_kwp_a m s = match s.n with 
  | Kind_arrow([Inl a, _;
                Inl wp, _;
                Inl _, _], _) -> a, wp.sort
  | _ -> raise (Error(Tc.Errors.unexpected_signature_for_monad m s, range_of_lid m))

let rec tc_monad_decl env m =  
  let mk = tc_kind_trivial env m.signature in 
  let a, kwp_a = a_kwp_a m.mname mk in 
  let a_typ = Util.btvar_to_typ a in
  let b = Util.gen_bvar_p (range_of_lid m.mname) ktype in
  let b_typ = Util.btvar_to_typ b in
  let kwp_b = Util.subst_kind [Inl(a.v, b_typ)] kwp_a in
  let kwlp_a = kwp_a in
  let kwlp_b = kwp_b in
  let a_kwp_b = mk_Kind_arrow([null_v_binder a_typ], kwp_b) a_typ.pos in
  let a_kwlp_b = a_kwp_b in
  let w k = k (range_of_lid m.mname) in
  let ret = 
    let expected_k = w <| mk_Kind_arrow([t_binder a; null_v_binder a_typ], kwp_a) in
    tc_typ_check_trivial env m.ret expected_k |> norm_t env in
  let bind_wp =
    let expected_k = w <| mk_Kind_arrow([t_binder a; t_binder b; 
                                         null_t_binder kwp_a; null_t_binder kwlp_a;
                                         null_t_binder a_kwp_b; null_t_binder a_kwlp_b], 
                                         kwp_b) in
    tc_typ_check_trivial env m.bind_wp expected_k |> norm_t env  in
  let bind_wlp = 
   let expected_k = w <| mk_Kind_arrow([t_binder a; t_binder b;
                                        null_t_binder kwlp_a;
                                        null_t_binder a_kwlp_b],
                                        kwlp_b) in
   tc_typ_check_trivial env m.bind_wlp expected_k |> norm_t env in
  let ite_wp =
    let expected_k = w <| mk_Kind_arrow([t_binder a;
                                         null_t_binder kwlp_a;
                                         null_t_binder kwp_a],
                                         kwp_a) in
    tc_typ_check_trivial env m.ite_wp expected_k |> norm_t env in
  let ite_wlp =
    let expected_k = w <| mk_Kind_arrow([t_binder a;
                                         null_t_binder kwlp_a],
                                         kwlp_a) in
    tc_typ_check_trivial env m.ite_wlp expected_k |> norm_t env in
  let wp_binop = 
    let expected_k = w <| mk_Kind_arrow([t_binder a; 
                                         null_t_binder kwp_a;
                                         null_t_binder (Const.kbin ktype ktype ktype);
                                         null_t_binder kwp_a], 
                                         kwp_a) in
    tc_typ_check_trivial env m.wp_binop expected_k |> norm_t env in
  let wp_as_type = 
    let expected_k = w <| mk_Kind_arrow([t_binder a;
                                         null_t_binder kwp_a],
                                        ktype) in
//    let expected_k = w <| mk_Kind_tcon(Some a, ktype, kt kwp_a ktype, false) in
    tc_typ_check_trivial env m.wp_as_type expected_k |> norm_t env in
  let close_wp = 
    let expected_k = w <| mk_Kind_arrow([t_binder b; t_binder a; 
                                         null_t_binder a_kwp_b],
                                        kwp_b) in
    tc_typ_check_trivial env m.close_wp expected_k |> norm_t env in
  let close_wp_t = 
    let expected_k = w <| mk_Kind_arrow([t_binder a;
                                         null_t_binder (w <| mk_Kind_arrow([null_t_binder ktype], kwp_a))],
                                        kwp_a)  in
    tc_typ_check_trivial env m.close_wp_t expected_k |> norm_t env in
  let assert_p, assume_p = 
    let expected_k =   w <| mk_Kind_arrow([t_binder a; 
                                           null_t_binder ktype; 
                                           null_t_binder kwp_a], kwp_a) in
    tc_typ_check_trivial env m.assert_p expected_k |> norm_t env, tc_typ_check_trivial env m.assume_p expected_k |> norm_t env in
  let null_wp = 
      let expected_k = w <| mk_Kind_arrow([t_binder a], kwp_a) in
      tc_typ_check_trivial env m.null_wp expected_k |> norm_t env in
  let trivial =
      let expected_k = w <| mk_Kind_arrow([t_binder a; null_t_binder kwp_a], ktype) in
      tc_typ_check_trivial env m.trivial expected_k |> norm_t env in
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
        let kwp_a_tgt = Util.subst_kind' [Inl(b.v, Util.btvar_to_typ a)] kwp_b_tgt in
        let expected_k = r |> mk_Kind_arrow([t_binder a; null_t_binder kwp_a_src], kwp_a_tgt) in
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
      let k = match k.n with 
        | Kind_unknown -> ktype
        | _ -> tc_kind_trivial env k in
      if debug env then Util.fprint2 "Checked %s at kind %s\n" (Print.sli lid) (Print.kind_to_string (Util.close_kind tps k));
      let k = norm_k env k in 
      let se = Sig_tycon(lid, tps, k, _mutuals, _data, tags, r) in
      let _ = match compress_kind k with
        | {n=Kind_uvar _} -> Rel.trivial <| Tc.Rel.keq env None k ktype
        | _ -> () in 
      let env = Tc.Env.push_sigelt env se in
      se, env
  
    | Sig_typ_abbrev(lid, tps, k, t, tags, r) -> 
      let env = Tc.Env.set_range env r in
      let tps, env' = tc_tparams env tps in
      let t, k1 = tc_typ_trivial env' t |> (fun (t, k) -> norm_t env' t, norm_k env' k) in 
      let k2 = match k.n with 
        | Kind_unknown -> k1 
        | _ -> let k2 = tc_kind_trivial env' k |> norm_k env in 
               Rel.trivial <| Rel.keq env' (Some t) k1 k2; k1 in
      let se = Sig_typ_abbrev(lid, tps, k2, t, tags, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
  
    | Sig_datacon(lid, t, tname, quals, r) -> 
      let env = Tc.Env.set_range env r in
      let t = tc_typ_check_trivial env t ktype |> norm_t env in 
      let formals, result_t = match Util.function_formals t with 
        | Some (formals, cod) -> formals, Util.comp_result cod
        | _ -> [], t in
      (* TODO: check that the tps in tname are the same as here *)
      let _ = match destruct result_t tname with 
        | Some _ -> ()
        | _ -> printfn "type is %s" (Print.typ_to_string t);
               raise (Error (Tc.Errors.constructor_builds_the_wrong_type (Util.fvar lid (range_of_lid lid)) result_t (Util.ftv tname kun), range_of_lid lid)) in
      let t = Tc.Util.refine_data_type env lid formals result_t in
      let se = Sig_datacon(lid, t, tname, quals, r) in 
      let env = Tc.Env.push_sigelt env se in 
      if log env then Util.print_string <| Util.format2 "data %s : %s\n" lid.str (Print.typ_to_string t);
      se, env
  
    | Sig_val_decl(lid, t, quals, r) -> 
      let env = Tc.Env.set_range env r in
      let t = tc_typ_check_trivial env t ktype |> norm_t env in 
      Tc.Util.check_uvars r t;
      let se = Sig_val_decl(lid, t, quals, r) in 
      let env = Tc.Env.push_sigelt env se in 
      if log env then Util.print_string <| Util.format2 "val %s : %s\n" lid.str (Print.typ_to_string t);
      se, env
  
    | Sig_assume(lid, phi, quals, r) ->
      let env = Tc.Env.set_range env r in
      let phi = tc_typ_check_trivial env phi ktype |> norm_t env in 
      Tc.Util.check_uvars r phi;
      let se = Sig_assume(lid, phi, quals, r) in 
      let env = Tc.Env.push_sigelt env se in 
      se, env
   
    | Sig_let(lbs, r) -> 
      //let is_rec = fst lbs in
      let env = Tc.Env.set_range env r in
      let lbs' = snd lbs |> List.fold_left (fun lbs lb -> 
        let lb = match lb with 
          | (Inl _, _, _) -> failwith "impossible"
          | (Inr l, t, e) -> 
            let (lb, t, e) = match Tc.Env.try_lookup_val_decl env l with 
              | None -> lb //                let t = Tc.Util.extract_lb_annotation is_rec env t e in
                           //                (Inr l, t, e) //<--NS: Used to pull out inline annots ... not sure it helps
              | Some t' -> match t.n with 
                  | Typ_unknown -> (Inr l, t', e)
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
          let tps, t = match tt.n with 
            | Typ_lam(bs, t) -> Util.tps_of_binders bs, t
            | _ -> failwith "Impossible" in
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
 
