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
module FStar.TypeChecker.Tc

open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util

let log env = !Options.log_types && not(lid_equals Const.prims_lid (Env.current_module env))
let rng env = Env.get_range env
let instantiate_both env = {env with Env.instantiate_imp=true}
let no_inst env = {env with Env.instantiate_imp=false}
let mk_lex_list vs =
    List.fold_right (fun v tl ->
        let r = if tl.pos = Range.dummyRange then v.pos else Range.union_ranges v.pos tl.pos in
        mk_Tm_app lex_pair [(Recheck.check v, Some Implicit); arg v; arg tl] (Some lex_t.n) r) 
    vs lex_top
let is_eq = function
    | Some Equality -> true
    | _ -> false
let steps env =
    if Options.should_verify env.curmodule.str then
    [N.Beta; N.SNComp]
    else [N.Beta]
let whnf   env t = N.normalize [N.WHNF; N.DeltaHard; N.Beta] env t
let norm   env t = N.normalize (steps env) env t
let norm_c env c = N.normalize_comp (steps env) env c
let fxv_check head env kt fvs =
    let rec aux try_norm t =
        if Util.set_is_empty fvs then ()
        else let fvs' = Free.names (if try_norm then norm env t else t) in
             let a = Util.set_intersect fvs fvs' in
             if Util.set_is_empty a then ()
             else if not try_norm
             then aux true t
             else let fail () =
                    let escaping = Util.set_elements a |> List.map Print.bv_to_string  |> String.concat ", " in
                    let msg = if Util.set_count a > 1
                              then Util.format2 "Bound variables '{%s}' in the type of '%s' escape because of impure applications; add explicit let-bindings" 
                                    escaping (N.term_to_string env head)
                              else Util.format2 "Bound variable '%s' in the type of '%s' escapes because of impure applications; add explicit let-bindings" 
                                    escaping (N.term_to_string env head) in
                    raise (Error(msg, Env.get_range env)) in
                  let s = TcUtil.new_uvar env (Recheck.check t) in
                  begin match Rel.try_teq env t s with
                    | Some g -> Rel.try_discharge_guard env g
                    | _ -> fail ()
                  end in 
    aux false kt

let maybe_push_binding env b =
  if is_null_binder b then env
  else let b = Env.Binding_var(fst b, ([], (fst b).sort)) in
       Env.push_local_binding env b
       
let maybe_make_subst = function
  | Inr(Some x, e) -> [NT(x,e)]
  | _ -> []

let maybe_extend_subst s b v : subst =
    if is_null_binder b then s
    else NT(fst b, v)::s

let set_lcomp_result lc t =
    {lc with res_typ=t; comp=fun () -> Util.set_result_typ (lc.comp()) t}

let value_check_expected_typ env e tlc guard : term * lcomp * Rel.guard_t =
  let lc = match tlc with
    | Inl t -> TcUtil.lcomp_of_comp (if not (Util.is_pure_or_ghost_function t)
                                      then mk_Total t
                                      else TcUtil.return_value env t e)
    | Inr lc -> lc in
  let t = lc.res_typ in
  let e, lc, g = match Env.expected_typ env with
   | None -> e, lc, guard
   | Some t' ->
     if debug env Options.High
     then Util.fprint2 "Computed return type %s; expected type %s\n" (Print.term_to_string t) (Print.term_to_string t');
     let e, g = TcUtil.check_and_ascribe env e t t' in
     let g = Rel.conj_guard g guard in
     let lc, g = TcUtil.strengthen_precondition (Some <| Errors.subtyping_failed env t t') env e lc g in
     e, set_lcomp_result lc t', g in
  if debug env Options.Low
  then Util.fprint1 "Return comp type is %s\n" (Print.lcomp_to_string lc);
  e, lc, g

let comp_check_expected_typ env e lc : term * lcomp * Rel.guard_t =
  match Env.expected_typ env with
   | None -> e, lc, Rel.trivial_guard
   | Some t -> TcUtil.weaken_result_typ env e lc t

let check_expected_effect env (copt:option<comp>) (e, c) : term * comp * Rel.guard_t =
  let expected_c_opt = match copt with
    | Some _ -> copt
    | None ->
        let c1 = N.weak_norm_comp env c in
        let md = Env.get_effect_decl env c1.effect_name in
        match Env.default_effect env md.mname with
            | None -> None
            | Some l ->
                let flags =
                    if lid_equals l Const.effect_Tot_lid then [TOTAL]
                    else if lid_equals l Const.effect_ML_lid then [MLEFFECT]
                    else [] in
                let def = mk_Comp ({effect_name=l;
                                    result_typ=c1.result_typ;
                                    effect_args=[];
                                    flags=flags})  in
                Some def in

  match expected_c_opt with
    | None -> e, norm_c env c, Rel.trivial_guard
    | Some expected_c -> //expected effects should already be normalized
       if debug env Options.Low then Util.fprint3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                                  (Range.string_of_range e.pos) (Print.comp_to_string c) (Print.comp_to_string expected_c);
       let c = norm_c env c in
       let expected_c' = TcUtil.refresh_comp_label env true (TcUtil.lcomp_of_comp <| expected_c) in
       let e, _, g = TcUtil.check_comp env e c <| expected_c'.comp() in
       if debug env Options.Low then Util.fprint2 "(%s) DONE check_expected_effect; guard is: %s\n" (Range.string_of_range e.pos) (Rel.guard_to_string env g);
       e, expected_c, g

let no_logical_guard env (te, kt, f) =
  match Rel.guard_form f with
    | Rel.Trivial -> te, kt, f
    | Rel.NonTrivial f -> raise (Error(Errors.unexpected_non_trivial_precondition_on_term env f, Env.get_range env))

let binding_of_lb x t = match x with
  | Inl bvd -> Env.Binding_var(bvd, t)
  | Inr lid -> Env.Binding_lid(lid, t)

let print_expected_ty env = match Env.expected_typ env with
    | None -> Util.print_string "Expected type is None"
    | Some t -> Util.fprint1 "Expected type is %s" (Print.term_to_string t)

let with_implicits imps (e, l, g) = e, l, {g with implicits=imps@g.implicits}
let add_implicit u g = {g with implicits=u::g.implicits}

(************************************************************************************************************)
(* check the patterns in an SMT lemma to make sure all bound vars are mentiond *)
(************************************************************************************************************)
let check_smt_pat env t bs c = 
    if Util.is_smt_lemma t //check patterns cover the bound vars
    then match c.n with
        | Comp ({effect_args=[(pre, _); (post, _); (pats, _)]}) ->
            let rec extract_pats pats = match (SS.compress pats).n with 
                | Tm_app({n=Tm_fvar (cons, _)}, [_; (hd, _); (tl, _)]) when lid_equals cons.v Const.cons_lid -> 
                    let head, args = Util.head_and_args hd in
                    let pat = match args with 
                        | [_; arg]
                        | [arg] -> [arg]
                        | _ -> [] in
                    pat@extract_pats tl 
                | _ -> [] in
            let pats = extract_pats (N.normalize [N.Beta] env pats) in
            let fvs = List.fold_left (fun out (a, _) -> Util.set_union out (Free.names a)) (S.new_bv_set()) pats in
            begin match bs |> Util.find_opt (fun (b, _) -> not(Util.set_mem b fvs)) with
                    | None -> ()
                    | Some (x,_) -> Errors.warn t.pos (Util.format1 "Pattern misses at least one bound variables: %s" (Print.bv_to_string x))
            end
        | _ -> failwith "Impossible"
    
(************************************************************************************************************)
(* Building the environment for the body of a let rec;                                                      *)
(* guards the recursively bound names with a termination check                                              *)
(************************************************************************************************************)
let guard_letrecs env actuals expected_c : list<(lbname*typ)> = 
    match env.letrecs with
    | [] -> []
    | letrecs ->
      let r = Env.get_range env in
      let env = {env with letrecs=[]} in
      let precedes = S.fvar (Some S.Data_ctor) Const.precedes_lid (Env.get_range env) in

      let decreases_clause bs c = 
          //exclude types and function-typed arguments from the decreases clause
          let filter_types_and_functions (bs:binders)  =
            bs |> List.collect (fun (b, _) -> 
                    let t = whnf env (Util.unrefine b.sort) in 
                    match t.n with 
                        | Tm_type _ 
                        | Tm_arrow _ -> []
                        | _ -> [S.bv_to_name b]) in
          let as_lex_list dec =
                let head, _ = Util.head_and_args dec in
                match head.n with (* The decreases clause is always an expression of type lex_t; promote if it isn't *)
                    | Tm_fvar (fv, _) when lid_equals fv.v Const.lexcons_lid -> dec
                    | _ -> mk_lex_list [dec] in
          let ct = Util.comp_to_comp_typ c in
          match ct.flags |> List.tryFind (function DECREASES _ -> true | _ -> false) with
                | Some (DECREASES dec) -> as_lex_list dec
                | _ ->
                    let xs = bs |> filter_types_and_functions in
                    match xs with
                        | [x] -> x //NS: why no promotion here?
                        | _ -> mk_lex_list xs in

        let previous_dec = decreases_clause actuals expected_c in
        let guard_one_letrec (l, t) = 
            match (SS.compress t).n with
                | Tm_arrow(formals, c) ->
                  let formals, c = SS.open_comp formals c in
                  let dec = decreases_clause formals c in
                  let precedes = mk_Tm_app precedes [arg dec; arg previous_dec] None r in
                  let bs, (last, imp) = Util.prefix formals in
                  let last = {last with sort=Util.refine last precedes} in
                  let refined_formals = bs@[(last,imp)] in
                  let t' = Util.arrow refined_formals c in
                  if debug env Options.Low
                  then Util.fprint3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                        (Print.lbname_to_string l) (Print.term_to_string t) (Print.term_to_string t');
                  l,t'
                  
                | _ -> failwith "Impossible: Annotated type of 'let rec' is not an arrow" in

        letrecs |> List.map guard_one_letrec 

(************************************************************************************************************)
(* Main type-checker begins here                                                                            *)
(************************************************************************************************************)
let rec tc_term env (e:term) : term                  (* type-checked and elaborated version of e            *)
                             * lcomp                 (* computation type where the WPs are lazily evaluated *)
                             * Rel.guard_t =         (* well-formedness condition                           *)
  let env = if e.pos=Range.dummyRange then env else Env.set_range env e.pos in
  if debug env Options.Low then Util.fprint2 "%s (%s)\n" (Range.string_of_range <| Env.get_range env) (Print.tag_of_term e);
  let top = e in
  match e.n with
  | Tm_delayed _ -> tc_term env (SS.compress e)

  | Tm_uvar _
  | Tm_bvar _
  | Tm_name _
  | Tm_fvar _
  | Tm_constant _
  | Tm_abs _
  | Tm_arrow _
  | Tm_refine _
  | Tm_type _  -> tc_value env e

  | Tm_unknown -> //only occurs where type annotations are missing in source programs
    let t, u = TcUtil.type_u () in
    let e = TcUtil.new_uvar env t in
    let c = Util.gtotal_comp t |> Util.lcomp_of_comp in
    e, c, Rel.trivial_guard

  | Tm_meta(e, Meta_pattern pats) -> 
    let t, u = TcUtil.type_u () in
    let e, c, g = tc_check_tot_or_gtot_term env e t in
    let pats, g' = tc_pats env pats in
    let g' = {g' with guard_f=Trivial} in //The pattern may have some VCs associated with it, but these are irrelevant.
    mk (Tm_meta(e, Meta_pattern pats)) (Some t.n) top.pos, 
    c,
    Rel.conj_guard g g' //but don't drop g' altogether, since it also contains unification constraints

  | Tm_meta(e, Meta_desugared Sequence) -> 
    begin match (SS.compress e).n with
        | Tm_let((_,[{lbname=x; lbdef=e1}]), e2) -> //NS: Why not handle this specially in the deugaring phase, adding a unit annotation on x?
          let e1, c1, g1 = tc_term (Env.set_expected_typ env Recheck.t_unit) e1 in
          let e2, c2, g2 = tc_term env e2 in
          let c = TcUtil.bind env (Some e1) c1 (None, c2) in
          let e = mk (Tm_let((false, [mk_lb (x, [], c1.eff_name, Recheck.t_unit, e1)]), e2)) (Some c.res_typ.n) e.pos in
          let e = mk (Tm_meta(e, Meta_desugared Sequence)) (Some c.res_typ.n) top.pos in
          e, c, Rel.conj_guard g1 g2
        | _ ->
          let e, c, g = tc_term env e in
          let e = mk (Tm_meta(e, Meta_desugared Sequence)) (Some c.res_typ.n) top.pos in
          e, c, g
    end

  | Tm_meta(e, m) -> 
    let e, c, g = tc_term env e in
    let e = mk (Tm_meta(e, m)) (Some c.res_typ.n) top.pos in
    e, c, g

  | Tm_ascribed (e, t, _) -> 
    let k, u = TcUtil.type_u () in
    let t, _, f = tc_check_tot_or_gtot_term env t k in
    let e, c, g = tc_term (Env.set_expected_typ env t) e in
    let c, f = TcUtil.strengthen_precondition (Some (fun () -> Errors.ill_kinded_type)) (Env.set_range env t.pos) e c f in
    let e, c, f2 = comp_check_expected_typ env (mk (Tm_ascribed(e, t, Some c.eff_name)) (Some t.n) top.pos) c in
    e, c, Rel.conj_guard f (Rel.conj_guard g f2)

  | Tm_app(head, args) -> 
    let env0 = env in
    let env = Env.clear_expected_typ env |> fst |> instantiate_both in
    if debug env Options.High then Util.fprint2 "(%s) Checking app %s\n" (Range.string_of_range top.pos) (Print.term_to_string top);
    //Don't instantiate head; instantiations will be computed below, accounting for implicits/explicits
    let head, chead, g_head = tc_term (no_inst env) head in 
    let e, c, g = if TcUtil.short_circuit_head head 
                  then check_short_circuit_args env head chead g_head args
                  else check_application_args env head chead g_head args in 
    if Env.debug env <| Options.Other "Implicits"
    then Util.fprint1 "Introduced %s implicits in application\n" (string_of_int <| List.length g.implicits);
    let c = if Options.should_verify env.curmodule.str
            && not (Util.is_lcomp_partial_return c)
            && Util.is_pure_or_ghost_lcomp c //ADD_EQ_REFINEMENT for pure applications
            then TcUtil.maybe_assume_result_eq_pure_term env e c
            else c in
    if debug env Options.Extreme
    then Util.fprint3 "(%s) About to check %s against expected typ %s\n" (Range.string_of_range e.pos)
            (Print.term_to_string c.res_typ)
            (Env.expected_typ env0 |> (fun x -> match x with None -> "None" | Some t -> Print.term_to_string t));
    let e, c, g' = comp_check_expected_typ env0 e c in
    e, c, Rel.conj_guard g g'
    
  | Tm_match(e1, eqns) ->
    let env1, topt = Env.clear_expected_typ env in
    let env1 = instantiate_both env1 in
    let e1, c1, g1 = tc_term env1 e1 in
    let env_branches, res_t = match topt with
      | Some t -> env, t
      | None ->
        let k, _ = TcUtil.type_u() in
        let res_t = TcUtil.new_uvar env k in
        Env.set_expected_typ env res_t, res_t in
 
    let guard_x = S.new_bv (Some e1.pos) c1.res_typ in
    let t_eqns = eqns |> List.map (tc_eqn guard_x env_branches) in
    let c_branches, g_branches =
      let cases, g = List.fold_right (fun (_, f, c, g) (caccum, gaccum) ->
        (f, c)::caccum, Rel.conj_guard g gaccum) t_eqns ([], Rel.trivial_guard) in
      TcUtil.bind_cases env res_t cases, g in (* bind_cases adds an exhaustiveness check *)
   
    if debug env Options.Extreme
    then Util.fprint4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n"
                      (Range.string_of_range top.pos) (Print.lcomp_to_string c1) (Print.lcomp_to_string c_branches) (Rel.guard_to_string env g_branches);
   
    let cres = TcUtil.bind env (Some e1) c1 (Some <| Env.Binding_var(guard_x, ([],c1.res_typ)), c_branches) in
    let e = mk (Tm_match(e1, List.map (fun (f, _, _, _) -> f) t_eqns)) (Some cres.res_typ.n) top.pos in
    let e = mk (Tm_ascribed(e, cres.res_typ, Some cres.eff_name)) None e.pos in  //important to ascribe, for recomputing types
    e, cres, Rel.conj_guard g1 g_branches

(************************************************************************************************************)
(* Type-checking values:                                                                                    *)
(*   Values have no special status, except that we structure the code to promote a value type t to a Tot t  *)
(************************************************************************************************************)
and tc_value env (e:term) : term 
                          * lcomp 
                          * Rel.guard_t =
  //As a general naming convention, we use e for the term being analyzed and its subterms as e1, e2, etc.
  //We use t and its variants for the type of the term being analyzed 
  let env = Env.set_range env e.pos in
  let top = SS.compress e in
  match top.n with
  | Tm_uvar(_, t1) -> //the type of a uvar is given directly with it; we do not recheck the type
    value_check_expected_typ env e (Inl t1) Rel.trivial_guard

  | Tm_bvar x ->
    failwith "Impossible: Violation of locally nameless convention"

  | Tm_name x ->
    let t = Env.lookup_bv env x in //should instantiate universe variables, if any
    let e = S.bv_to_name ({x with sort=t}) in 
    let e, t, implicits = TcUtil.maybe_instantiate env e t in
    let tc = if Options.should_verify env.curmodule.str then Inl t else Inr (TcUtil.lcomp_of_comp <| mk_Total t) in
    with_implicits implicits <| value_check_expected_typ env e tc Rel.trivial_guard

  | Tm_fvar (v, dc) ->
    let t = Env.lookup_lid env v.v in
    let e = mk (Tm_fvar({v with sort=t}, dc)) (Some t.n) e.pos in
    let e, t, implicits = TcUtil.maybe_instantiate env e t in
    //printfn "Instantiated type of %s to %s\n" (Print.term_to_string e) (Print.term_to_string t);
    let tc = if Options.should_verify env.curmodule.str then Inl t else Inr (TcUtil.lcomp_of_comp <| mk_Total t) in
    let is_data_ctor = function
        | Some Data_ctor
        | Some (Record_ctor _) -> true
        | _ -> false in
    if is_data_ctor dc && not(Env.is_datacon env v.v)
    then raise (Error(Util.format1 "Expected a data constructor; got %s" v.v.str, Env.get_range env))
    else with_implicits implicits <| value_check_expected_typ env e tc Rel.trivial_guard

  | Tm_constant c ->
    let t = Recheck.check e in //Recheck can always check constants
    let e = mk (Tm_constant c) (Some t.n) e.pos in
    value_check_expected_typ env e (Inl t) Rel.trivial_guard

  | Tm_arrow(bs, c) -> 
    let bs, c = SS.open_comp bs c in 
    let env0 = env in
    let bs, env, g, us = tc_binders env bs in
    let c, uc, f = tc_comp env c in
    let e = {Util.arrow bs c with pos=top.pos} in
    check_smt_pat env e bs c;
    let u = List.fold_left (fun out u -> S.U_max(out, u)) uc us in
    let t = mk (Tm_type u) None top.pos in
    let g = Rel.conj_guard g (Rel.close_guard bs f) in
    value_check_expected_typ env0 e (Inl t) g

  | Tm_type u -> 
    let u = tc_universe env u in 
    let t = mk (Tm_type(S.U_succ u)) None top.pos in
    let e = mk (Tm_type u) (Some t.n) top.pos in
    value_check_expected_typ env e (Inl t) Rel.trivial_guard

  | Tm_refine(x, phi) ->
    let x, phi = SS.open_term [S.mk_binder x] phi in
    let env0 = env in
    let x, env, f1, u = tc_binder env (List.hd x) in
    if debug env Options.High 
    then Util.fprint3 "(%s) Checking refinement formula %s; env expects type %s\n"  
        (Range.string_of_range top.pos) (Print.term_to_string phi) 
        (match Env.expected_typ env with None -> "None" | Some t -> Print.term_to_string t);
    let t_phi, _ = TcUtil.type_u () in
    let phi, _, f2 = tc_check_tot_or_gtot_term env phi t_phi in
    let e = {Util.refine (fst x) phi with pos=top.pos} in
    let t = mk (Tm_type u) None top.pos in
    let g = Rel.conj_guard f1 (Rel.close_guard [x] f2) in
    value_check_expected_typ env0 e (Inl t) g

  | Tm_abs(bs, body) ->  
    let bs, body = SS.open_term bs body in
    tc_abs env top bs body

  | Tm_let((false, [{lbname=x; lbunivs=univ_vars; lbtyp=t; lbdef=e1}]), e2) ->
    let push_univ_vars env univ_vars : Env.env = failwith "NYI" in
    let open_univ_vars univ_vars t   : univ_vars * term = failwith "NYI" in

    let env = instantiate_both env in
    let env0 = env in
    let topt = Env.expected_typ env in
    let top_level = match x with Inr _ -> true | _ -> false in
    let env1, _ = Env.clear_expected_typ env in
    let f, univ_vars, env1 = match t.n with
        | Tm_unknown ->
          if univ_vars <> [] then failwith "Impossible: non-empty universe variables but the type is unknown";
          Rel.trivial_guard, [], env1

        | _ ->
            let univ_vars, t = open_univ_vars univ_vars t in
            let env1 = push_univ_vars env1 univ_vars in
            if top_level && not (env.generalize)
            then Rel.trivial_guard, univ_vars, Env.set_expected_typ env1 t //t has already been kind-checked
            else let k, _ = TcUtil.type_u () in
                 let t, _, f = tc_check_tot_or_gtot_term env1 t k in
                 if debug env Options.Medium then Util.fprint2 "(%s) Checked type annotation %s\n" (Range.string_of_range top.pos) (Print.term_to_string t);
                 let t = norm env1 t in
                 f, univ_vars, Env.set_expected_typ env1 t in

    let e1, c1, g1 = tc_term ({env1 with top_level=top_level}) e1 in
    let c1, guard_f = TcUtil.strengthen_precondition (Some (fun () -> Errors.ill_kinded_type)) (Env.set_range env t.pos) e1 c1 f in
    begin match x with
        | Inr _ -> (* top-level let, always ends with e2=():unit *)
          let e2, c1 =
            if Options.should_verify env.curmodule.str
            then let ok, c1 = TcUtil.check_top_level env (Rel.conj_guard g1 guard_f) c1 in
                 if ok
                 then e2, c1
                 else (if !Options.warn_top_level_effects
                       then Errors.warn (Env.get_range env) Errors.top_level_effect;
                       mk (Tm_meta(e2, Meta_desugared Masked_effect)) None e2.pos, c1)
            else (TcUtil.discharge_guard env (Rel.conj_guard g1 guard_f);  //still need to solve remaining unification/subtyping constraints
                  e2, c1.comp()) in
          let _, e1, c1 = if env.generalize
                          then List.hd <| TcUtil.generalize false env1 [x, e1, c1] (* only generalize top-level lets, when there is no val decl *)
                          else x, e1, c1 in
          let cres = TcUtil.lcomp_of_comp <| Util.ml_comp Recheck.t_unit top.pos in
          let cres = if Util.is_total_comp c1
                     then cres
                     else TcUtil.bind env None (TcUtil.lcomp_of_comp c1) (None, cres) in
          e2.tk := Some (Recheck.t_unit.n);
          w cres <| mk_Exp_let((false, [mk_lb (x, Util.comp_effect_name c1, Util.comp_result c1, e1)]), e2), cres, Rel.trivial_guard

        | Inl bvd ->  (* don't generalize inner lets *)
            let b = binding_of_lb x c1.res_typ in
            let e2, c2, g2 = tc_exp (Env.push_local_binding env b) e2 in
            let cres = TcUtil.bind env (Some e1) c1 (Some b, c2) in
            let e = w cres <| mk_Exp_let((false, [mk_lb (x, c1.eff_name, c1.res_typ, e1)]), e2) in
            let g2 = Rel.close_guard [v_binder (Util.bvd_to_bvar_s bvd c1.res_typ)] <|
                (Rel.imp_guard (Rel.guard_of_guard_formula (Rel.NonTrivial <| Util.mk_eq c1.res_typ c1.res_typ (Util.bvd_to_exp bvd c1.res_typ) e1)) g2) in
            let guard = Rel.conj_guard guard_f (Rel.conj_guard g1 g2) in
            match topt with
              | None -> (* no expected type; check that x doesn't escape it's scope *)
                 let tres = cres.res_typ in
                 let fvs = Util.freevars_typ tres in
                 if Util.set_mem (bvd_to_bvar_s bvd t) fvs.fxvs
                 then let t = TcUtil.new_tvar env0 ktype in
                      Tc.Rel.try_discharge_guard env <| Tc.Rel.teq env tres t;
                      e, cres, guard
                 else e, cres, guard
              | _ -> e, cres, guard
     end

  | _ ->
    failwith (Util.format1 "Unexpected value: %s" (Print.term_to_string top))

(************************************************************************************************************)
(* Type-checking computation types                                                                          *)
(************************************************************************************************************)
and tc_comp env c : comp                                      (* checked version of c                       *)
                  * universe                                  (* universe of c.result_typ                   *)
                  * Rel.guard_t =                             (* logical guard for the well-formedness of c *)
  match c.n with
    | Total t ->
      let k, u = TcUtil.type_u () in
      let t, _, g = tc_check_tot_or_gtot_term env t k in
      mk_Total t, u, g

    | Comp c ->
      let kc =  Env.lookup_effect_lid env c.effect_name in
      let head = S.fvar None c.effect_name (range_of_lid c.effect_name) in
      let tc = mk_Tm_app head ((arg c.result_typ)::c.effect_args) None c.result_typ.pos in
      let tc, _, f = tc_check_tot_or_gtot_term env tc S.teff in
      let _, args = Util.head_and_args tc in
      let res, args = List.hd args, List.tl args in
      let flags, guards = c.flags |> List.map (function
        | DECREASES e ->
            let env, _ = Env.clear_expected_typ env in
            let e, _, g = tc_tot_or_gtot_term env e in
            DECREASES e, g
        | f -> f, Rel.trivial_guard) |> List.unzip in
      let u = match Recheck.check (fst res) with  //TODO: UGLY!
        | {n=Tm_type u} -> u
        | _ -> failwith "Impossible" in
      mk_Comp ({c with
          result_typ=fst res;
          effect_args=args}), 
      u,
      List.fold_left Rel.conj_guard f guards

and tc_universe env u = 
   failwith "NYI"

(* Several complex cases from the main type-checker are factored in to separate functions below *)

(*******************************************************************************************************************)
(* Type-checking abstractions, aka lambdas                                                                         *)
(*    top = fun bs -> body, although bs and body must already be opened                                            *)
(*******************************************************************************************************************)
and tc_abs env (top:term) (bs:binders) (body:term) : term * lcomp * Rel.guard_t =
    let fail :string -> typ -> 'a = fun msg t -> raise (Error(Errors.expected_a_term_of_type_t_got_a_function env msg t top, top.pos)) in
    
    (***************************************************************************************************************)
    (* check_binders checks that the binders bs of top                                                             *)
    (*               are compatible with the binders of the function typ expected by the context                   *)
    (*               If there are more bs than bs_expected, we only check a prefix and the suffix is returned Inl  *)
    (*               If there are more bs_expected than bs, the suffix of bs_expected is returned Inr              *)
    (***************************************************************************************************************)
    let check_binders env bs bs_expected  : Env.env                           (* env extended with a prefix of bs  *)
                                            * binders                         (* a type-checked prefix of bs       *)
                                            * option<either<binders,binders>> (* suffix of either bs or bs_expected*)
                                            * Rel.guard_t                     (* accumulated logical guard         *)
                                            * subst =                         (* alpha conv. of bs_expected to bs  *)
        let rec aux (env, out, g, subst) (bs:binders) (bs_expected:binders) = match bs, bs_expected with 
            | [], [] -> env, List.rev out, None, g, subst

            | (hd, imp)::bs, (hd_expected, imp')::bs_expected -> 
               if imp<>imp' then raise (Error(Util.format1 "Inconsistent implicit argument annotation on argument %s" (Print.bv_to_string hd), 
                                              S.range_of_bv hd));
               let expected_t = SS.subst subst hd_expected.sort in
               let t, g = match (Util.unmeta hd.sort).n with
                    | Tm_unknown -> expected_t, g
                    | _ ->
                      if Env.debug env Options.High then Util.fprint1 "Checking binder %s\n" (Print.bv_to_string hd);
                      let t, _, g1 = tc_tot_or_gtot_term env hd.sort in
                      let g2 = Rel.teq env t expected_t in
                      let g = Rel.conj_guard g (Rel.conj_guard g1 g2) in
                      t, g in
                let hd = {hd with sort=t} in 
                let b = hd, imp in
                let b_expected = (hd_expected, imp') in
                let env = maybe_push_binding env b in
                let subst = maybe_extend_subst subst b_expected  (S.bv_to_name hd) in
                aux (env, b::out, g, subst) bs bs_expected 

          | rest, [] -> env, List.rev out, Some (Inl rest), g, subst

          | [], rest -> env, List.rev out, Some (Inr rest), g, subst in

        aux (env, [], Rel.trivial_guard, []) bs bs_expected in


    let rec expected_function_typ env t0 : (option<(typ*bool)> (* any remaining expected type to check against; bool signals to check using teq *)
                                            * binders          (* binders from the abstraction checked against the binders in the corresponding Typ_fun, if any *)
                                            * binders          (* let rec binders, suitably guarded with termination check, if any *)
                                            * option<comp>     (* the expected comp type for the body *)
                                            * Env.env          (* environment for the body *)
                                            * guard_t) =       (* accumulated guard from checking the binders *)
       match t0 with
        | None -> (* no expected type; just build a function type from the binders in the term *)
            let _ = match env.letrecs with [] -> () | _ -> failwith "Impossible: Can't have a let rec annotation but no expected type" in
            let bs, envbody, g, _ = tc_binders env bs in
            None, bs, [], None, envbody, g

        | Some t ->
           let t = SS.compress t in
           let rec as_function_typ norm t =
               match (SS.compress t).n with
                | Tm_uvar _
                | Tm_app({n=Tm_uvar _}, _) -> (* expected a uvar; build a function type from the term and unify with it *)
                  let _ = match env.letrecs with [] -> () | _ -> failwith "Impossible" in
                  let bs, envbody, g, _ = tc_binders env bs in
                  let envbody, _ = Env.clear_expected_typ envbody in
                  Some (t, true), bs, [], None, envbody, g

                (* CK: add this case since the type may be f:(a -> M b wp){φ}, in which case I drop the refinement *)
                (* NS: 07/21 dropping the refinement is not sound; we need to check that f validates phi. See Bug #284 *)
                | Tm_refine (b, _) ->
                  let _, bs, bs', copt, env, g = as_function_typ norm b.sort in
                  Some (t, false), bs, bs', copt, env, g

                | Tm_arrow(bs_expected, c_expected) ->
                  let bs_expected, c_expected = SS.open_comp bs_expected c_expected in
                    (* Two main interesting bits here;
                        1. The expected type may have
                             a. more immediate binders, whereas the function may itself return a function
                             b. fewer immediate binders, meaning that the function type is explicitly curried
                        2. If the function is a let-rec, and the expected type is pure, then we need to add termination checks.
                    *)
                  let check_actuals_against_formals env bs bs_expected = 
                      let rec handle_more (env, bs, more, guard, subst) c_expected = match more with 
                        | None -> //number of binders match up
                          env, bs, guard, SS.subst_comp subst c_expected

                        | Some (Inr more_bs_expected) -> //more formal parameters; expect the body to return a total function 
                          let c = S.mk_Total (Util.arrow more_bs_expected c_expected) in
                          env, bs, guard, SS.subst_comp subst c 

                        | Some (Inl more_bs) ->  //more actual args
                          let c = SS.subst_comp subst c_expected in
                          (* the expected type is explicitly curried *)
                          if Util.is_total_comp c
                          then let t = whnf env (Util.comp_result c) in
                               match t.n with 
                                | Tm_arrow(bs_expected, c_expected) ->  
                                  let (env, bs', more, guard', subst) = check_binders env more_bs bs_expected in
                                  handle_more (env, bs@bs', more, Rel.conj_guard guard guard', subst) c_expected 
                                | _ -> fail (Util.format1 "More arguments than annotated type (%s)" (Print.term_to_string t)) t
                          else fail "Function definition takes more arguments than expected from its annotated type" t in
                  
                       handle_more (check_binders env bs bs_expected) c_expected in

                 let mk_letrec_env envbody bs c = 
                     let letrecs = guard_letrecs envbody bs c in
                     letrecs |> List.fold_left (fun (env, letrec_binders) (l,t) -> 
                        let t, _, _ = tc_term (Env.clear_expected_typ env |> fst) t in
                        let env = Env.push_local_binding env (binding_of_lb l ([],t)) in
                        let lb = match l with 
                            | Inl x -> S.mk_binder ({x with sort=t})::letrec_binders
                            | _ -> letrec_binders in
                        env, lb)
                      (envbody, []) in

                 let envbody, bs, g, c = check_actuals_against_formals env bs bs_expected in
                 let envbody, letrecs = if Options.should_verify env.curmodule.str then mk_letrec_env envbody bs c else envbody, [] in
                 let envbody = Env.set_expected_typ envbody (Util.comp_result c) in
                 Some (t, false), bs, letrecs, Some c, envbody, g

                | _ -> (* expected type is not a function;
                          try normalizing it first;
                          otherwise synthesize a type and check it against the given type *)
                  if not norm
                  then as_function_typ true (whnf env t)
                  else let _, bs, _, c_opt, envbody, g = expected_function_typ env None in
                       Some (t, false), bs, [], c_opt, envbody, g in
           as_function_typ false t in

    let use_eq = env.use_eq in
    let env, topt = Env.clear_expected_typ env in
    let tfun_opt, bs, letrec_binders, c_opt, envbody, g = expected_function_typ env topt in
    let body, cbody, guard_body = tc_term ({envbody with top_level=false; use_eq=use_eq}) body in
    if Env.debug env Options.Medium
    then Util.fprint3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" 
          (Print.term_to_string body) (Print.lcomp_to_string cbody) (Rel.guard_to_string env guard_body);
    let guard_body = Rel.solve_deferred_constraints envbody guard_body in
    if Env.debug env <| Options.Other "Implicits"
    then Util.fprint1 "Introduced %s implicits in body of abstraction\n" (string_of_int <| List.length guard_body.implicits);
    let body, cbody, guard = check_expected_effect ({envbody with use_eq=use_eq}) c_opt (body, cbody.comp()) in
    let guard = Rel.conj_guard guard_body guard in
    let guard = if env.top_level || not(Options.should_verify env.curmodule.str)
                then (TcUtil.discharge_guard envbody (Rel.conj_guard g guard); {Rel.trivial_guard with implicits=guard.implicits})
                else let guard = Rel.close_guard (bs@letrec_binders) guard in Rel.conj_guard g guard in

    let tfun_computed = Util.arrow bs cbody in 
    let e = Util.abs bs body in
    //Important to ascribe, since the SMT encoding requires the type of every abstraction
    let ascribe e t = mk (Tm_ascribed (e, t, Some Const.effect_Tot_lid)) None top.pos  in

    let e, tfun, guard = match tfun_opt with
        | Some (t, use_teq) ->
           let t = SS.compress t in
           (match t.n with
                | Tm_arrow _ ->
                    //we already checked the body to have the expected type; so, no need to check again
                    //just repackage the expression with this type; t is guaranteed to be alpha equivalent to tfun_computed
                    ascribe e t,
                    t,
                    guard
                | _ ->
                    let e = ascribe e tfun_computed in
                    let e, guard' =
                        if use_teq
                        then e, Rel.teq env t tfun_computed
                        else TcUtil.check_and_ascribe env e tfun_computed t in
                    ascribe e t, 
                    t,  
                    Rel.conj_guard guard guard')

        | None -> ascribe e tfun_computed, tfun_computed, guard in

    if Env.debug env Options.Low
    then Util.fprint3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" 
            (Print.term_to_string tfun) (Print.term_to_string tfun) (Rel.guard_to_string env guard);

    let c = if env.top_level then mk_Total tfun else TcUtil.return_value env tfun e in
    let c, g = TcUtil.strengthen_precondition None env e (TcUtil.lcomp_of_comp c) guard in
    e, c, g

(******************************************************************************)
(* Type-checking applications: Tm_app head args                               *)
(*      head is already type-checked has comp type chead, with guard ghead    *)
(******************************************************************************)
and check_application_args env head chead ghead args : term * lcomp * Rel.guard_t= 
    let n_args = List.length args in
    let r = Env.get_range env in
    let thead = chead.res_typ in
    if debug env Options.High then Util.fprint2 "(%s) Type of head is %s\n" (Range.string_of_range head.pos) (Print.term_to_string thead);
    let rec check_function_app norm tf = 
       match (Util.unrefine tf).n with
        | Tm_uvar _
        | Tm_app({n=Tm_uvar _}, _) ->
            let rec tc_args env args : (Syntax.args * list<lcomp> * guard_t) = match args with
                | [] -> ([], [], Rel.trivial_guard)
                | (e, imp)::tl ->
                    let e, c, g_e = tc_term env e in
                    let args, comps, g_rest = tc_args env tl in
                    (e, imp)::args, c::comps, Rel.conj_guard g_e g_rest in
            (* Infer: t1 -> ... -> tn -> ML ('u x1...xm),
                    where ti are the result types of each arg
                    and   xi are the free type/term variables in the environment *)
            let args, comps, g_args = tc_args env args in
            let bs = null_binders_of_tks (comps |> List.map (fun c -> c.res_typ, None)) in
            let cres = Util.ml_comp (TcUtil.new_uvar env (TcUtil.type_u () |> fst)) r in
            TcUtil.discharge_guard env <| Rel.teq env tf (Util.arrow bs cres);
            let comp = List.fold_right (fun c out -> TcUtil.bind env None c (None, out)) (chead::comps) (TcUtil.lcomp_of_comp <| cres) in
            mk_Tm_app head args (Some comp.res_typ.n) r, comp, Rel.conj_guard ghead g_args

        | Tm_arrow(bs, c) ->
            let bs, c = SS.open_comp bs c in

            let rec tc_args (subst,  (* substituting actuals for formals seen so far, when actual is pure *)
                            outargs, (* type-checked actuals *)
                            arg_rets,(* The results of each argument at the logic level *)
                            comps,   (* computation types for each actual *)
                            g,       (* conjoined guard formula for all the actuals *)
                            fvs)     (* unsubstituted formals, to check that they do not occur free elsewhere in the type of f *)
                            bs       (* formal parameters *)
                            cres     (* function result comp *)
                            args     (* actual arguments  *) : (term * lcomp * guard_t) =
            match bs, args with
            | (x, Some Implicit)::rest, (_, None)::_ -> (* instantiate an implicit value arg *)
                let t = SS.subst subst x.sort in
                fxv_check head env t fvs;
                let varg, u = TcUtil.new_implicit_var env t in //new_uvar env t in
                let subst = NT(x, varg)::subst in
                let arg = varg, as_implicit true in
                tc_args (subst, arg::outargs, arg::arg_rets, comps, add_implicit u g, fvs) rest cres args

            | (x, aqual)::rest, (e, aq)::rest' -> (* a concrete argument *)
                let _ = match aqual, aq with 
                | Some Implicit, Some Implicit 
                | None, None 
                | Some Equality, None -> ()
                | _ -> raise (Error("Inconsistent implicit qualifier", e.pos)) in
                let targ = SS.subst subst x.sort in
                if debug env Options.Extreme then  Util.fprint1 "\tType of arg (after subst) = %s\n" (Print.term_to_string targ);
                fxv_check head env targ fvs;
                let env = Env.set_expected_typ env targ in
                let env = {env with use_eq=is_eq aqual} in
                if debug env Options.High then  Util.fprint3 "Checking arg (%s) %s at type %s\n" (Print.tag_of_term e) (Print.term_to_string e) (Print.term_to_string targ);
                let e, c, g_e = tc_term env e in
                let g = Rel.conj_guard g g_e in
                if debug env Options.High then Util.fprint2 "Guard on this arg is %s;\naccumulated guard is %s\n" (Rel.guard_to_string env g_e) (Rel.guard_to_string env g);
                let arg = e, aq in
                if Util.is_tot_or_gtot_lcomp c //e is Tot or GTot; we can just substitute it
                then let subst = maybe_extend_subst subst (List.hd bs) e in
                    tc_args (subst, arg::outargs, arg::arg_rets, comps, g, fvs) rest cres rest'
                else if TcUtil.is_pure_or_ghost_effect env c.eff_name //its conditionally pure; can substitute, but must check its WP
                then let subst = maybe_extend_subst subst (List.hd bs) e in
                    let comps, guard =
                        (Some (Env.Binding_var(x, ([],targ))), c)::comps, g in
                    tc_args (subst, arg::outargs, arg::arg_rets, comps, guard, fvs) rest cres rest'
                else if is_null_binder (List.hd bs) //it's not pure, but the function isn't dependent; just check its WP
                then let newx = S.new_bv (Some e.pos) c.res_typ in 
                    let arg' = S.arg <| S.bv_to_name newx in
                    let binding = Env.Binding_var(newx, ([],newx.sort)) in
                    tc_args (subst, arg::outargs, arg'::arg_rets, (Some binding, c)::comps, g, fvs) rest cres rest'
                else //e is impure and the function may be dependent... 
                    //need to check that the variable does not occur free in the rest of the function type
                    //by adding x to fvs
                    tc_args (subst, arg::outargs, S.arg (S.bv_to_name x)::arg_rets, 
                            (Some <| Env.Binding_var(x, ([],targ)), c)::comps, g, Util.set_add x fvs) rest cres rest'

            | _, [] -> (* no more args; full or partial application *)
                fxv_check head env cres.res_typ fvs;
                let cres, g = match bs with
                | [] -> (* full app *)
                    let cres = TcUtil.subst_lcomp subst cres in
                    (* If we have f e1 e2
                        where e1 or e2 is impure but f is a pure function,
                        then refine the result to be equal to f x1 x2,
                        where xi is the result of ei. (See the last two tests in examples/unit-tests/unit1.fst)
                    *)
                    let g = Rel.conj_guard ghead g in

                    let refine_with_equality =
                        //if the function is pure, but its arguments are not, then add an equality refinement here
                        //OW, for pure applications we always add an equality at the end; see ADD_EQ_REFINEMENT below
                        Util.is_pure_or_ghost_lcomp cres
                        && comps |> Util.for_some (fun (_, c) -> not (Util.is_pure_or_ghost_lcomp c)) in 
                        (* if the guard is trivial, then strengthen_precondition below will not add an equality; so add it here *)

                    let cres = //NS: Choosing when to add an equality refinement is VERY important for performance. 
                                //Adding it unconditionally impacts run time by >5x
                        if refine_with_equality
                        then Util.maybe_assume_result_eq_pure_term env 
                                (mk_Tm_app head (List.rev arg_rets) (Some cres.res_typ.n) r) 
                                cres
                        else (if Env.debug env Options.Low
                                then Util.fprint3 "Not refining result: f=%s; cres=%s; guard=%s\n" 
                                    (Print.term_to_string head) (Print.lcomp_to_string cres) (Rel.guard_to_string env g);
                                cres) in

                    (* relabeling the labeled sub-terms in cres to report failing pre-conditions at this call-site *)
                    TcUtil.refresh_comp_label env false cres, g

                | _ ->  (* partial app *)
                    let g = Rel.conj_guard ghead g |> Rel.solve_deferred_constraints env in
                    TcUtil.lcomp_of_comp <| mk_Total  (SS.subst subst <| Util.arrow bs (cres.comp())), g in

                if debug env Options.Low then Util.fprint1 "\t Type of result cres is %s\n" (Print.lcomp_to_string cres);
                let comp = List.fold_left (fun out c -> TcUtil.bind env None (snd c) (fst c, out)) cres comps in
                let comp = TcUtil.bind env None chead (None, comp) in
                let app =  mk_Tm_app head (List.rev outargs) (Some comp.res_typ.n) r in
                let comp, g = TcUtil.strengthen_precondition None env app comp g in //Each conjunct in g is already labeled
                if debug env Options.Low 
                then Util.fprint2 "\t Type of app term %s is %s\n" (N.term_to_string env app) (Print.comp_to_string (comp.comp()));
                app, comp, g


            | [], arg::_ -> (* too many args, except maybe c returns a function *)
                let rec aux norm tres =
                let tres = SS.compress tres |> Util.unrefine in
                match tres.n with
                    | Tm_arrow(bs, cres') ->
                        if debug env Options.Low 
                        then Util.fprint1 "%s: Warning: Potentially redundant explicit currying of a function type \n" 
                            (Range.string_of_range tres.pos);
                        tc_args (subst, outargs, arg_rets, (None, cres)::comps, g, fvs) bs (TcUtil.lcomp_of_comp cres') args
                    | _ when (not norm) ->
                        aux true (whnf env tres)
                    | _ -> raise (Error(Util.format2 "Too many arguments to function of type %s; got %d arguments" 
                                            (N.term_to_string env tf) (Util.string_of_int n_args), argpos arg)) in
                aux false cres.res_typ in

            tc_args ([], [], [], [], Rel.trivial_guard, S.new_bv_set()) bs (TcUtil.lcomp_of_comp c) args

        | _ ->
            if not norm
            then check_function_app true (whnf env tf)
            else raise (Error(Errors.expected_function_typ env tf, head.pos)) in

    check_function_app false (Util.unrefine thead) 

(******************************************************************************)
(* SPECIAL CASE OF CHECKING APPLICATIONS:                                     *)
(*        head symbol is one of &&, ||, /\, \/, ==>                           *)
(*   ALL OF THEM HAVE A LOGICAL SPEC THAT IS BIASED L-to-R,                   *)
(*  aka they are short-circuiting                                             *) 
(******************************************************************************)
and check_short_circuit_args env head chead g_head args : term * lcomp * Rel.guard_t = 
    let r = Env.get_range env in
    let tf = SS.compress chead.res_typ in
    match tf.n with 
        | Tm_arrow(bs, c) when Util.is_total_comp c && List.length bs=List.length args -> 
          let res_t = Util.comp_result c in
          let args, guard, ghost = List.fold_left2 (fun (seen, guard, ghost) (e, aq) (b, aq') ->
                if aq<>aq' then raise (Error("Inconsistent implicit qualifiers", e.pos)); 
                let e, c, g = tc_check_tot_or_gtot_term env e b.sort in //NS: this forbids stuff like !x && y, maybe that's ok
                let short = TcUtil.short_circuit head seen in 
                let g = Rel.imp_guard (Rel.guard_of_guard_formula short) g in
                let ghost = ghost || not (TcUtil.is_pure_effect env c.eff_name) in
                seen@[arg e], Rel.conj_guard guard g, ghost) ([], g_head, false) args bs in
          let e = mk_Tm_app head args (Some res_t.n) r  in
          let c = if ghost then Util.gtotal_comp res_t |> Util.lcomp_of_comp else Util.lcomp_of_comp c in
          e, c, guard
        
        | _ -> //fallback
          check_application_args env head chead g_head args


(********************************************************************************************************************)
(* Type-checking a pattern-matching branch                                                                          *)
(* the pattern, when_clause and branch are closed                                                                   *)
(* scrutinee is the logical name of the expression being matched; it is not in scope in the branch                  *)
(*           but it is in scope for the VC of the branch                                                            *)
(* env does not contain scrutinee, or any of the pattern-bound variables                                            *)
(* the returned terms are well-formed in an environment extended with the scrutinee only                            *)
(********************************************************************************************************************)
and tc_eqn scrutinee env branch 
        : (pat * option<term> * term)                                                             (* checked branch *)
        * term       (* the guard condition for taking this branch, used by the caller for the exhaustiveness check *) 
        * lcomp                                                                   (* computation type of the branch *) 
        * guard_t =                                                                    (* well-formedness condition *)
  let pattern, when_clause, branch_exp = SS.open_branch branch in
  
  (*<tc_pat>*)
  let tc_pat (allow_implicits:bool) (pat_t:typ) p0 : 
        pat                                (* the type-checked, fully decorated pattern                             *)
      * list<Env.binding>                  (* all its bound variables, used for closing the type of the branch term *)
      * Env.env                            (* the environment exteneded with all the binders                        *)
      * list<term>                         (* terms corresponding to each clause in the disjunctive pat             *)
      * list<term>                         (* the same terms in normal form                                         *)
      =
    let bindings, exps, p = TcUtil.pat_as_exps allow_implicits env p0 in //an expression for each clause in a disjunctive pattern
    let pat_env = List.fold_left Env.push_local_binding env bindings in
    let env1, _ = Env.clear_expected_typ pat_env in
    let env1 = {env1 with Env.is_pattern=true} in  //just a flag for a better error message
    let expected_pat_t = Rel.unrefine env pat_t in
    let exps, norm_exps = exps |> List.map (fun e ->
        if Env.debug env Options.High
        then Util.fprint2 "Checking pattern expression %s against expected type %s\n" (Print.term_to_string e) (Print.term_to_string pat_t);

        let e, lc, g =  tc_term env1 e in //only keep the unification/subtyping constraints; discard the logical guard for patterns

        if Env.debug env Options.High
        then Util.fprint2 "Pre-checked pattern expression %s at type %s\n" (N.term_to_string env e) (N.term_to_string env lc.res_typ);

        let g' = Rel.teq env lc.res_typ expected_pat_t in
        let g = Rel.conj_guard g g' in
        ignore <| Rel.solve_deferred_constraints env g;
        let e' = N.normalize [N.Beta] env e in
        if not <| Util.set_is_subset_of (Free.uvars e') (Free.uvars expected_pat_t)
        then raise (Error(Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" 
                                    (Print.term_to_string e') (Print.term_to_string expected_pat_t), p.p));

        if Env.debug env Options.High
        then Util.fprint1 "Done checking pattern expression %s\n" (N.term_to_string env e);

        //explicitly return e here, not its normal form, since pattern decoration relies on it
        e,e') |> List.unzip in
    let p = TcUtil.decorate_pattern env p exps in
    p, bindings, pat_env, exps, norm_exps in
  (*</tc_pat>*)

  let pat_t = scrutinee.sort in
  let scrutinee_tm = S.bv_to_name scrutinee in 
  let scrutinee_env, _ = Env.push_local_binding env (Env.Binding_var(scrutinee, ([],pat_t))) |> Env.clear_expected_typ in
 
  (* 1. Check the pattern *)
  let pattern, bindings, pat_env, disj_exps, norm_disj_exps = tc_pat true pat_t pattern in //disj_exps, an exp for each arm of a disjunctive pattern
 
  (* 2. Check the when clause *)
  let when_clause, g_when = match when_clause with
    | None -> None, Rel.trivial_guard
    | Some e ->
        if Options.should_verify (env.curmodule.str)
        then raise (Error("When clauses are not yet supported in --verify mode; they will be some day", e.pos))
        //             let e, c, g = no_logical_guard pat_env <| tc_total_exp (Env.set_expected_typ pat_env TcUtil.t_bool) e in
        //             Some e, g
        else let e, c, g = tc_term (Env.set_expected_typ pat_env Recheck.t_bool) e in
             Some e, g in

  (* 3. Check the branch *)
  let branch_exp, c, g_branch = tc_term pat_env branch_exp in
 
  (* 4. Lift the when clause to a logical condition. *)
  (*    It is used in step 5 (a) below, and in step 6 (d) to build the branch guard *)
  let when_condition = match when_clause with
        | None -> None
        | Some w -> Some <| Util.mk_eq Util.t_bool Util.t_bool w Const.exp_true_bool in

  (* 5 (a). Build equality conditions between the pattern and the scrutinee                                   *)
  (*   (b). Weaken the VCs of the branch and when clause with the equalities from 5(a) and the when condition *)
  (*   (c). Close the VCs so that they no longer have the pattern-bound variables occurring free in them      *)
  let c, g_when, g_branch =

    (* (a) eqs are equalities between the scrutinee and the pattern *)
    let eqs = disj_exps |> List.fold_left (fun fopt e ->
        let e = SS.compress e in
        match e.n with
            | Tm_uvar _
            | Tm_constant _
            | Tm_fvar _ -> fopt (* Equation for non-binding forms are handled with the discriminators below *)
            | _ ->
              let clause = Util.mk_eq pat_t pat_t scrutinee_tm e in
              match fopt with
                | None -> Some clause
                | Some f -> Some <| Util.mk_disj clause f) None in
    (* (b) *)
    let c_weak, g_when_weak, g_branch_weak = 
     match eqs, when_condition with
      | None, None -> 
        c, g_when, g_branch
      
      | Some f, None -> 
        let gf = Rel.NonTrivial f in
        let g = Rel.guard_of_guard_formula gf in
        TcUtil.weaken_precondition env c gf,
        Rel.imp_guard g g_when, 
        Rel.imp_guard g g_branch 

      | Some f, Some w ->
        let g_f = Rel.NonTrivial f in
        let g_fw = Rel.NonTrivial (Util.mk_conj f w) in
        TcUtil.weaken_precondition env c g_fw, 
        Rel.imp_guard (Rel.guard_of_guard_formula g_f) g_when,
        Rel.imp_guard (Rel.guard_of_guard_formula g_fw) g_branch

      | None, Some w -> 
        let g_w = Rel.NonTrivial w in
        let g = Rel.guard_of_guard_formula g_w in
        TcUtil.weaken_precondition env c g_w, 
        g_when, 
        Rel.imp_guard g g_branch in
    
    (* (c) *)
    let binders = Env.binders_of_bindings bindings in
    TcUtil.close_comp env bindings c_weak, 
    Rel.close_guard binders g_when_weak, 
    Rel.close_guard binders g_branch_weak in

  (* 6. Building the guard for this branch;                                                             *)
  (*        the caller assembles the guards for each branch into an exhaustiveness check.               *)
  (*                                                                                                    *)
  (* (a) Compute the branch guard for each arm of a disjunctive pattern.                                *)
  (*      logically the same as step 5(a),                                                              *)
  (*      but expressed in terms for discriminators and projectors on sub-terms of scrutinee            *)
  (*      for the benefit of the caller, who works in an environment without the pattern-bound vars     *)
  (*                                                                                                    *)
  (* (b) Type-check the condition computed in 6 (a)                                                     *)
  (*                                                                                                    *)
  (* (c) Make a disjunctive formula out of 6(b) for each arm of the pattern                             *)
  (*                                                                                                    *)
  (* (d) Strengthen 6 (c) with the when condition, if there is one                                      *)
  let branch_guard = 
      (* 6 (a) *)
      let rec build_branch_guard scrutinee_tm pat_exp : typ =
        let discriminate scrutinee_tm f =
            let disc = S.fvar None (Util.mk_discriminator f.v) (range_of_lid f.v) in
            let disc = mk_Tm_app disc [arg scrutinee_tm] None scrutinee_tm.pos in
            Util.mk_eq Util.t_bool Util.t_bool disc Const.exp_true_bool in

        let pat_exp = SS.compress pat_exp in
        match pat_exp.n with
            | Tm_uvar _
            | Tm_app({n=Tm_uvar _}, _)
            | Tm_name _
            | Tm_constant Const_unit -> S.fvar None Const.true_lid scrutinee_tm.pos
            | Tm_constant _ -> mk_Tm_app Util.teq [arg scrutinee_tm; arg pat_exp] None scrutinee_tm.pos
            | Tm_fvar(f, _) -> discriminate scrutinee_tm f
            | Tm_app({n=Tm_fvar(f, _)}, args) ->
                let head = discriminate scrutinee_tm f in
                let sub_term_guards = args |> List.mapi (fun i (ei, _) -> 
                    let projector = Env.lookup_projector env f.v i in //NS: TODO ... should this be a marked as a record projector? But it doesn't matter for extraction
                    let sub_term = mk_Tm_app (S.fvar None projector f.p) [arg scrutinee_tm] None f.p in
                    [build_branch_guard sub_term ei]) |> List.flatten in
                Util.mk_conj_l (head::sub_term_guards)
            | _ -> failwith (Util.format2 "tc_eqn: Impossible (%s) %s" (Range.string_of_range pat_exp.pos) (Print.term_to_string pat_exp)) in

      (* 6 (b) *)
      let build_and_check_branch_guard scrutinee_tm pat =
         if not (Options.should_verify env.curmodule.str)
         then S.fvar None Const.true_lid scrutinee_tm.pos //if we're not verifying, then don't even bother building it
         else let t = build_branch_guard scrutinee_tm pat in
              let k, _ = TcUtil.type_u() in
              let t, _, _ = tc_check_tot_or_gtot_term scrutinee_env t k in
              t in

      (* 6 (c) *)
     let branch_guard = norm_disj_exps |> List.map (build_and_check_branch_guard scrutinee_tm) |> Util.mk_disj_l  in

      (* 6 (d) *)
      let branch_guard = match when_condition with
        | None -> branch_guard
        | Some w -> Util.mk_conj branch_guard w in

      branch_guard in
  
  let guard = Rel.conj_guard g_when g_branch in
 
  if Env.debug env Options.High
  then Util.fprint1 "Carrying guard from match: %s\n" <| Rel.guard_to_string env guard;

  SS.close_branch (pattern, when_clause, branch_exp), 
  branch_guard, //expressed in terms of discriminators and projectors on scrutinee---does not contain the pattern-bound variables
  c, //closed already---does not contain free pattern-bound variables
  guard

(******************************************************************************)
(* Several utility functions follow                                           *)
(******************************************************************************)
and tc_binder env (x:bv, imp) =
    let tu, u = TcUtil.type_u () in
    let t, _, g = tc_check_tot_or_gtot_term env x.sort tu in //ghost effect ok in the types of binders
    let x = {x with sort=t} in
    let env' = maybe_push_binding env (x, imp) in
    (x,imp), env', g, u

and tc_binders env bs =
    let rec aux env bs = match bs with
        | [] -> [], env, Rel.trivial_guard, []
        | b::bs ->
          let b, env', g, u = tc_binder env b in
          let bs, env', g', us = aux env' bs in
          b::bs, env', Rel.conj_guard g (Rel.close_guard [b] g'), u::us in
    aux env bs

and tc_args env args : Syntax.args * guard_t =
   //an optimization for checking arguments in cases where we know that their types match the types of the corresponding formal parameters
   //notably, this is used when checking the application  (?u x1 ... xn).
   List.fold_right (fun (t, imp) (args, g) -> 
                         let t, _, g' = tc_term env t in
                         (t, imp)::args, Rel.conj_guard g g') 
      args ([], Rel.trivial_guard)

and tc_pats env pats = 
    List.fold_right (fun p (pats, g) -> let args, g' = tc_args env p in (args::pats, Rel.conj_guard g g')) pats ([], Rel.trivial_guard) 

and tc_tot_or_gtot_term env e : term           
                                * lcomp 
                                * guard_t =
  let e, c, g = tc_term env e in
  if Util.is_tot_or_gtot_lcomp c
  then e, c, g
  else let g = Rel.solve_deferred_constraints env g in
       let c = c.comp() |> norm_c env in
       let target_comp, allow_ghost = 
            if TcUtil.is_pure_effect env (Util.comp_effect_name c)
            then S.mk_Total (Util.comp_result c), false
            else Util.gtotal_comp (Util.comp_result c), true in
       match Rel.sub_comp env c target_comp with
        | Some g' -> e, Util.lcomp_of_comp target_comp, Rel.conj_guard g g'
        | _ -> 
            if allow_ghost
            then raise (Error(Errors.expected_ghost_expression e c, e.pos))
            else raise (Error(Errors.expected_pure_expression e c, e.pos))

and tc_check_tot_or_gtot_term env e t : term
                                      * lcomp 
                                      * guard_t = 
    let e, c, g = tc_tot_or_gtot_term env e in
    let g' = Rel.subtype env c.res_typ t in
    let c = if Util.is_total_lcomp c 
            then S.mk_Total t 
            else Util.gtotal_comp t in
    e, Util.lcomp_of_comp c, Rel.conj_guard g g'

and tc_ghost_term env (e:term) (bs:binders) (body:term) : term * lcomp * Rel.guard_t =
    //use of the ghost effect is allowed in e, since it is syntactically deemed to be computationally irrelevant
   failwith "NYI"

and check_args env args bs = failwith ""


let rec tc_exp env e : exp * lcomp * guard_t =
  let env = if e.pos=dummyRange then env else Env.set_range env e.pos in
  if debug env Options.Low then Util.fprint2 "%s (%s)\n" (Range.string_of_range <| Env.get_range env) (Print.tag_of_exp e);
  let w lc = syn e.pos <| Some lc.res_typ in
  let top = e in
  match e.n with

  | Exp_let((false, [{lbname=x; lbtyp=t; lbdef=e1}]), e2) ->
    let env = instantiate_both env in
    let env0 = env in
    let topt = Env.expected_typ env in
    let top_level = match x with Inr _ -> true | _ -> false in
    let env1, _ = Env.clear_expected_typ env in
    let f, env1 = match t.n with
        | Typ_unknown ->
            Rel.trivial_guard, env1
        | _ ->
            if top_level && not (env.generalize)
            then Rel.trivial_guard, Env.set_expected_typ env1 t //t has already been kind-checked
            else let t, f = tc_typ_check env1 t ktype in
                 if debug env Options.Medium then Util.fprint2 "(%s) Checked type annotation %s\n" (Range.string_of_range top.pos) (Print.term_to_string t);
                 let t = norm_t env1 t in
                 let env1 = Env.set_expected_typ env1 t in
                 f, env1 in

    let e1, c1, g1 = tc_exp ({env1 with top_level=top_level}) e1 in
    let c1, guard_f = TcUtil.strengthen_precondition (Some (fun () -> Errors.ill_kinded_type)) (Env.set_range env t.pos) e1 c1 f in
    begin match x with
        | Inr _ -> (* top-level let, always ends with e2=():unit *)
          let e2, c1 =
            if Options.should_verify env.curmodule.str
            then let ok, c1 = TcUtil.check_top_level env (Rel.conj_guard g1 guard_f) c1 in
                 if ok
                 then e2, c1
                 else (if !Options.warn_top_level_effects
                       then Tc.Errors.warn (Env.get_range env) Tc.Errors.top_level_effect;
                       mk_Exp_meta(Meta_desugared(e2, Masked_effect)), c1)
            else (TcUtil.discharge_guard env (Rel.conj_guard g1 guard_f);  //still need to solve remaining unification/subtyping constraints
                  e2, c1.comp()) in
          let _, e1, c1 = if env.generalize
                          then List.hd <| TcUtil.generalize false env1 [x, e1, c1] (* only generalize top-level lets, when there is no val decl *)
                          else x, e1, c1 in
          let cres = TcUtil.lcomp_of_comp <| Util.ml_comp Recheck.t_unit top.pos in
          let cres = if Util.is_total_comp c1
                     then cres
                     else TcUtil.bind env None (TcUtil.lcomp_of_comp c1) (None, cres) in
          e2.tk := Some (Recheck.t_unit);
          w cres <| mk_Exp_let((false, [mk_lb (x, Util.comp_effect_name c1, Util.comp_result c1, e1)]), e2), cres, Rel.trivial_guard

        | Inl bvd ->  (* don't generalize inner lets *)
            let b = binding_of_lb x c1.res_typ in
            let e2, c2, g2 = tc_exp (Env.push_local_binding env b) e2 in
            let cres = TcUtil.bind env (Some e1) c1 (Some b, c2) in
            let e = w cres <| mk_Exp_let((false, [mk_lb (x, c1.eff_name, c1.res_typ, e1)]), e2) in
            let g2 = Rel.close_guard [v_binder (Util.bvd_to_bvar_s bvd c1.res_typ)] <|
                (Rel.imp_guard (Rel.guard_of_guard_formula (Rel.NonTrivial <| Util.mk_eq c1.res_typ c1.res_typ (Util.bvd_to_exp bvd c1.res_typ) e1)) g2) in
            let guard = Rel.conj_guard guard_f (Rel.conj_guard g1 g2) in
            match topt with
              | None -> (* no expected type; check that x doesn't escape it's scope *)
                 let tres = cres.res_typ in
                 let fvs = Util.freevars_typ tres in
                 if Util.set_mem (bvd_to_bvar_s bvd t) fvs.fxvs
                 then let t = TcUtil.new_tvar env0 ktype in
                      Tc.Rel.try_discharge_guard env <| Tc.Rel.teq env tres t;
                      e, cres, guard
                 else e, cres, guard
              | _ -> e, cres, guard
     end

  | Exp_let((false, _), _) ->
    failwith "impossible"

  | Exp_let((true, lbs), e1) ->
    let env = instantiate_both env in
    let env0, topt = Env.clear_expected_typ env in
    let is_inner_let = lbs |> Util.for_some (function {lbname=Inl _} -> true (* inner let *) | _ -> false) in
    (* build an environment with recursively bound names. refining the types of those names with decreases clauses is done in Exp_abs *)
    let lbs, env' = lbs |> List.fold_left (fun (xts, env) ({lbname=x; lbtyp=t; lbdef=e}) ->
      let _, t, check_t = TcUtil.extract_lb_annotation env t e in
      let e = Util.unascribe e in
      let t =
        if not check_t
        then t
        else if not (is_inner_let) && not(env.generalize)
        then (if Env.debug env <| Options.High then Util.fprint1 "Type %s is marked as no-generalize\n" (Print.term_to_string t);
              t) (* t is already checked *)
        else tc_typ_check_trivial ({env0 with check_uvars=true}) t ktype |> norm_t env in
      let env = if Util.is_pure_or_ghost_function t
                && Options.should_verify env.curmodule.str (* store the let rec names separately for termination checks *)
                then (//printfn "Extending let recs with %s : %s\n" (Print.lbname_to_string x) (Print.term_to_string t);
                      {env with letrecs=(x,t)::env.letrecs})
                else Env.push_local_binding env (binding_of_lb x t) in
      (x, t, e)::xts, env) ([],env)  in

    let lbs, gs = (lbs |> List.rev) |> List.map (fun (x, t, e) ->
        let t =  Tc.Normalize.norm_typ [Normalize.Beta] env t in
        if Env.debug env Options.High then Util.fprint3 "Checking %s = %s against type %s\n" (Print.lbname_to_string x) (Print.term_to_string e) (Print.term_to_string t);
//        printfn "IN environment: %s : %s\n" (Print.lbname_to_string x) (Print.term_to_string <| Env.lookup_lid env' (right x));
        let env' = Env.set_expected_typ env' t in
        let e, t, g = tc_total_exp env' e in
        (x, t, e), g) |> List.unzip in

    let g_lbs = List.fold_right Rel.conj_guard gs Rel.trivial_guard in

    let lbs, g_lbs =
        if not env.generalize || is_inner_let
        then List.map (fun (x, t, e) -> mk_lb (x, Const.effect_Tot_lid, t, e)) lbs, g_lbs
        else begin
             TcUtil.discharge_guard env g_lbs;
             let ecs = TcUtil.generalize true env (lbs |> List.map (fun (x, t, e) -> (x, e, Util.total_comp t <| range_of_lb (x,t,e)))) in
             List.map (fun (x, e, c) -> mk_lb (x, Const.effect_Tot_lid, Util.comp_result c, e)) ecs, Rel.trivial_guard
        end in

    if not is_inner_let (* the body is just unit *)
    then let cres = TcUtil.lcomp_of_comp <| Util.total_comp Recheck.t_unit top.pos in
         let _ = TcUtil.discharge_guard env g_lbs in //may need to solve all carried unification constraints, in case not generalized
         let _ = e1.tk := Some Recheck.t_unit in
         w cres <| mk_Exp_let((true, lbs), e1), cres, Rel.trivial_guard
    else let bindings, env = lbs |> List.fold_left (fun (bindings, env) ({lbname=x; lbtyp=t}) ->
             let b = binding_of_lb x t in
             let env = Env.push_local_binding env b in
             b::bindings, env) ([], env) in
         let e1, cres, g1 = tc_exp env e1 in
         let guard = Rel.conj_guard g_lbs g1 in
         let cres = TcUtil.close_comp env bindings cres in
         let tres = norm_t env cres.res_typ in
         let cres = {cres with res_typ=tres} in
         //let cres = Normalize.norm_comp [Normalize.Beta] env cres in
         let e = w cres <| mk_Exp_let((true, lbs), e1) in
         begin match topt with
          | Some _ -> e, cres, guard
          | None ->
             let fvs = Util.freevars_typ <| tres in
             match lbs |> List.tryFind (function
                    | ({lbname=Inr _}) -> false
                    | ({lbname=Inl x}) -> Util.set_mem (bvd_to_bvar_s x tun) fvs.fxvs) with
                | Some ({lbname=Inl y}) ->
                  let t' = TcUtil.new_tvar env0 ktype in
                  Tc.Rel.try_discharge_guard env <| Tc.Rel.teq env tres t';
                  e, cres, guard
                  //else raise (Error(Tc.Errors.inferred_type_causes_variable_to_escape env tres y, rng env))
                | _ -> e, cres, guard
         end


and tc_kind_trivial env k : knd =
  let k, g = tc_kind env k in
  TcUtil.discharge_guard env g;
  k

and tc_typ_trivial env t : typ * knd =
  let t, k, g = tc_typ env t in
  TcUtil.discharge_guard env g;
  t, k

and tc_typ_check_trivial env t (k:knd) =
  let t, f = tc_typ_check env t k in
  TcUtil.discharge_guard env f;
  t

and tc_total_exp env e : exp * typ * guard_t =
  let e, c, g = tc_exp env e in
  if is_total_lcomp c
  then e, c.res_typ, g
  else let g = Rel.solve_deferred_constraints env g in
       let c = c.comp() |> norm_c env in
       match Tc.Rel.sub_comp env c (Util.total_comp (Util.comp_result c) (Env.get_range env)) with
        | Some g' -> e, Util.comp_result c, Rel.conj_guard g g'
        | _ -> raise (Error(Tc.Errors.expected_pure_expression e c, e.pos))

and tc_ghost_exp env e : exp * typ * guard_t =
  let e, c, g = tc_exp env e in
  if is_total_lcomp c
  then e, c.res_typ, g
  else let c = c.comp() |> norm_c env in
       let expected_c = Util.gtotal_comp (Util.comp_result c) in
       let g = Rel.solve_deferred_constraints env g in
       match Tc.Rel.sub_comp ({env with use_eq=false}) c expected_c with
        | Some g' -> e, Util.comp_result c, Rel.conj_guard g g'
        | _ -> raise (Error(Tc.Errors.expected_ghost_expression e c, e.pos))

(*****************Type-checking the signature of a module*****************************)

let tc_tparams env (tps:binders) : (binders * Env.env) =
    let tps, env, g = tc_binders env tps in
    TcUtil.force_trivial env g;
    tps, env

let a_kwp_a env m s = match s.n with
  | Kind_arrow([(Inl a, _);
                (Inl wp, _);
                (Inl _, _)], _) -> a, wp.sort
  | _ -> raise (Error(Tc.Errors.unexpected_signature_for_monad env m s, range_of_lid m))

let rec tc_eff_decl env (m:Syntax.eff_decl)  =
  let binders, env, g = tc_binders env m.binders in
  TcUtil.discharge_guard env g;
  let mk = tc_kind_trivial env m.signature in
  let a, kwp_a = a_kwp_a env m.mname mk in
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
  let if_then_else =
    let expected_k = w <| mk_Kind_arrow([t_binder a;
                                         t_binder b;
                                         null_t_binder kwp_a;
                                         null_t_binder kwp_a], kwp_a) in
    tc_typ_check_trivial env m.if_then_else expected_k |> norm_t env in
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
  let trivial_wp =
      let expected_k = w <| mk_Kind_arrow([t_binder a; null_t_binder kwp_a], ktype) in
      tc_typ_check_trivial env m.trivial expected_k |> norm_t env in
    {
        mname=m.mname;
        qualifiers=m.qualifiers;
        binders=binders;
        signature=mk;
        ret=ret;
        bind_wp=bind_wp;
        bind_wlp=bind_wlp;
        if_then_else=if_then_else;
        ite_wp=ite_wp;
        ite_wlp=ite_wlp;
        wp_binop=wp_binop;
        wp_as_type=wp_as_type;
        close_wp=close_wp;
        close_wp_t=close_wp_t;
        assert_p=assert_p;
        assume_p=assume_p;
        null_wp=null_wp;
        trivial=trivial_wp
    }

and tc_decl env se deserialized = match se with
    | Sig_pragma(p, r) ->
        begin match p with
            | SetOptions o ->
                begin match Options.set_options o with
                    | Getopt.GoOn -> se, env
                    | Getopt.Help  -> raise (Error ("Failed to process pragma: use 'fstar --help' to see which options are available", r))
                    | Getopt.Die s -> raise (Error ("Failed to process pragma: " ^s, r))
                end
            | ResetOptions ->
                env.solver.refresh();
                Options.reset_options() |> ignore;
                se, env
        end

    | Sig_new_effect(ne, r) ->
      let ne = tc_eff_decl env ne in
      let se = Sig_new_effect(ne, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_sub_effect(sub, r) ->
      let a, kwp_a_src = a_kwp_a env sub.source (Env.lookup_effect_lid env sub.source) in
      let b, kwp_b_tgt = a_kwp_a env sub.target (Env.lookup_effect_lid env sub.target) in
      let kwp_a_tgt = Util.subst_kind [Inl(b.v, Util.btvar_to_typ a)] kwp_b_tgt in
      let expected_k = r |> mk_Kind_arrow([t_binder a; null_t_binder kwp_a_src], kwp_a_tgt) in
      let lift = tc_typ_check_trivial env sub.lift expected_k in
      let sub = {sub with lift=lift} in
      let se = Sig_sub_effect(sub, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) ->
      let env = Env.set_range env r in
      let tps, env = tc_tparams env tps in
      let k = match k.n with
        | Kind_unknown -> ktype
        | _ -> tc_kind_trivial env k in
      if debug env Options.Extreme then Util.fprint2 "Checked %s at kind %s\n" (Print.sli lid) (Print.kind_to_string (Util.close_kind tps k));
      let k = norm_k env k in
      let se = Sig_tycon(lid, tps, k, _mutuals, _data, tags, r) in
      let _ = match compress_kind k with
        | {n=Kind_uvar _} -> TcUtil.force_trivial env <| Tc.Rel.keq env None k ktype
        | _ -> () in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_kind_abbrev(lid, tps, k, r) ->
      let env0 = env in
      let env = Env.set_range env r in
      let tps, env = tc_tparams env tps in
      let k = tc_kind_trivial env k in
      let se = Sig_kind_abbrev(lid, tps, k, r) in
      let env = Env.push_sigelt env0 se in
      se, env

    | Sig_effect_abbrev(lid, tps, c, tags, r) ->
      let env0 = env in
      let env = Env.set_range env r in
      let tps, env = tc_tparams env tps in
      let c, g = tc_comp env c in
      let tags = tags |> List.map (function
        | DefaultEffect None ->
          let c' = Tc.Normalize.weak_norm_comp env c in
          DefaultEffect (c'.effect_name |> Some)
        | t -> t) in
      let se = Sig_effect_abbrev(lid, tps, c, tags, r) in
      let env = Env.push_sigelt env0 se in
      se, env

    | Sig_typ_abbrev(lid, tps, k, t, tags, r) ->
      let env = Env.set_range env r in
      let tps, env' = tc_tparams env tps in
      let t, k1 = tc_typ_trivial env' t |> (fun (t, k) -> norm_t env' t, norm_k env' k) in
      let k2 = match k.n with
        | Kind_unknown -> k1
        | _ -> let k2 = tc_kind_trivial env' k |> norm_k env in
               TcUtil.force_trivial env' <| Rel.keq env' (Some t) k1 k2; k2 in
      let se = Sig_typ_abbrev(lid, tps, k2, t, tags, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_datacon(lid, t, (tname, tps, k), quals, mutuals, r) ->
      let env = Env.set_range env r in
      let tps, env, g = tc_binders env tps in
      let tycon = tname, tps, k in
      TcUtil.discharge_guard env g;
      let t = tc_typ_check_trivial env t ktype in
      let t = norm_t env t in

      let formals, result_t = match Util.function_formals t with
        | Some (formals, cod) -> formals, Util.comp_result cod
        | _ -> [], t in

      let cardinality_and_positivity_check (formal:binder) = 
        let check_positivity formals = 
            formals |> List.iter (fun (a, _) -> match a with
                | Inl _ -> ()
                | Inr y ->
                    let t = y.sort in
                    Visit.collect_from_typ (fun b t ->
                    match (Util.compress_typ t).n with
                    | Typ_const f ->
                        begin match List.tryFind (lid_equals f.v) mutuals with
                        | None -> ()
                        | Some tname ->
                            raise (Error (Tc.Errors.constructor_fails_the_positivity_check env (Util.fvar (Some Data_ctor) lid (range_of_lid lid)) tname, range_of_lid lid))
                        end
                    | _ -> ()) () t) in
        match fst formal with
        | Inl a -> 
          begin 
              if Options.warn_cardinality()
              then Tc.Errors.warn r (Tc.Errors.cardinality_constraint_violated lid a)
              else if Options.check_cardinality()
              then raise (Error(Tc.Errors.cardinality_constraint_violated lid a, r))
          end;
          let k = Normalize.norm_kind [Normalize.Beta; Normalize.DeltaHard] env a.sort in
          begin match k.n with 
            | Kind_arrow _ -> 
              let formals, _ = Util.kind_formals k in
              check_positivity formals
            | _ -> ()
          end

        | Inr x ->
          let t = Normalize.norm_typ [Normalize.Beta; Normalize.DeltaHard] env x.sort in
          if Util.is_function_typ t && Util.is_pure_or_ghost_function t
          then let formals, _ = Util.function_formals t |> Util.must in
               check_positivity formals in

      formals |> List.iter cardinality_and_positivity_check;

      let _ = match destruct result_t tname with
        | Some args ->
          if not (List.length args >= List.length tps
               && List.forall2 (fun (a, _) (b, _) -> match a, b with 
                             | Inl ({n=Typ_btvar aa}), Inl bb -> Util.bvar_eq aa bb
                             | Inr ({n=Exp_bvar xx}), Inr yy -> Util.bvar_eq xx yy
                             | _ -> false) (Util.first_N (List.length tps) args |> fst) tps)
          then let expected_t = match tps with 
                | [] -> Util.ftv tname kun
                | _ -> 
                  let _, expected_args = Util.args_of_binders tps in
                  Util.mk_typ_app (Util.ftv tname kun) expected_args in 
               raise (Error (Tc.Errors.constructor_builds_the_wrong_type env (Util.fvar (Some Data_ctor) lid (range_of_lid lid)) result_t expected_t, range_of_lid lid))
        | _ -> raise (Error (Tc.Errors.constructor_builds_the_wrong_type env (Util.fvar (Some Data_ctor) lid (range_of_lid lid)) result_t (Util.ftv tname kun), range_of_lid lid)) in
      let se = Sig_datacon(lid, t, tycon, quals, mutuals, r) in
      let env = Env.push_sigelt env se in
      if log env then Util.print_string <| Util.format2 "data %s : %s\n" lid.str (Tc.Normalize.typ_norm_to_string env t);
      se, env

    | Sig_val_decl(lid, t, quals, r) ->
      let env = Env.set_range env r in
      let t = tc_typ_check_trivial env t ktype |> Tc.Normalize.norm_typ [Normalize.Beta; Normalize.SNComp] env in
      TcUtil.check_uvars r t;
      let se = Sig_val_decl(lid, t, quals, r) in
      let env = Env.push_sigelt env se in
      if log env then Util.print_string <| Util.format2 "val %s : %s\n" lid.str (Tc.Normalize.typ_norm_to_string env t);
      se, env

    | Sig_assume(lid, phi, quals, r) ->
      let env = Env.set_range env r in
      let phi = tc_typ_check_trivial env phi ktype |> norm_t env in
      TcUtil.check_uvars r phi;
      let se = Sig_assume(lid, phi, quals, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_let(lbs, r, lids, quals) ->
      //let is_rec = fst lbs in
      let env = Env.set_range env r in
      let generalize, lbs' = snd lbs |> List.fold_left (fun (gen, lbs) lb ->
        let gen, lb = match lb with
          | {lbname=Inl _} -> failwith "impossible"
          | {lbname=Inr l; lbtyp=t; lbdef=e} ->
            let gen, lb = match Env.try_lookup_val_decl env l with
              | None -> gen, lb
              | Some (t', _) ->
                if debug env Options.Medium
                then Util.fprint2 "Using annotation %s for let binding %s\n" (Print.term_to_string t') l.str;
                match t.n with
                  | Typ_unknown ->
                    false, mk_lb (Inr l, Const.effect_ALL_lid, t', e) //explicit annotation provided; do not generalize
                  | _ ->
                   if not(deserialized)
                   then Util.print_string <| Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" (Range.string_of_range r);
                   false, mk_lb (Inr l, Const.effect_ALL_lid, t', e) in
             gen, lb in
        gen, lb::lbs) (true, []) in
      let lbs' = List.rev lbs' in
      let e = mk_Exp_let((fst lbs, lbs'), syn' env Recheck.t_unit <| mk_Exp_constant(Const_unit)) None r in
      let se, lbs = match tc_exp ({env with generalize=generalize}) e with
        | {n=Exp_let(lbs, e)}, _, g when Rel.is_trivial g ->
            let quals = match e.n with
                | Exp_meta(Meta_desugared(_, Masked_effect)) -> HasMaskedEffect::quals
                | _ -> quals in
            Sig_let(lbs, r, lids, quals), lbs
        | _ -> failwith "impossible" in
      if log env
      then Util.fprint1 "%s\n" (snd lbs |> List.map (fun lb ->
            let should_log = match Env.try_lookup_val_decl env (right lb.lbname) with
                | None -> true
                | _ -> false in
            if should_log
            then Util.format2 "let %s : %s" (Print.lbname_to_string lb.lbname) (Tc.Normalize.typ_norm_to_string env lb.lbtyp)
            else "") |> String.concat "\n");
      let env = Env.push_sigelt env se in
      se, env

    | Sig_main(e, r) ->
      let env = Env.set_range env r in
      let env = Env.set_expected_typ env Recheck.t_unit in
      let e, c, g1 = tc_exp env e in
      let g1 = Rel.solve_deferred_constraints env g1 in
      let e, _, g = check_expected_effect env (Some (Util.ml_comp Recheck.t_unit r)) (e, c.comp()) in
      TcUtil.discharge_guard env (Rel.conj_guard g1 g);
      let se = Sig_main(e, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_bundle(ses, quals, lids, r) ->
      let env = Env.set_range env r in
      let tycons, rest = ses |> List.partition (function Sig_tycon _ -> true | _ -> false) in
      let abbrevs, rest = rest |> List.partition (function Sig_typ_abbrev _ -> true | _ -> false) in
      let recs = abbrevs |> List.map (function
        | Sig_typ_abbrev(lid, tps, k, t, [], r) ->
           let k = match k.n with
            | Kind_unknown -> Tc.Rel.new_kvar r tps |> fst
            | _ -> k in
           Sig_tycon(lid, tps, k, [], [], [], r), t
        | _ -> failwith "impossible") in
      let recs, abbrev_defs = List.split recs in
      let msg = if !Options.logQueries
                then Util.format1 "Recursive bindings: %s" (Print.sigelt_to_string_short se)
                else "" in
      env.solver.push msg; //Push a context in the solver to check the recursively bound definitions
      let tycons, _, _ = tc_decls false env tycons deserialized in
      let recs, _, _ = tc_decls false env recs deserialized in
      let env1 = Env.push_sigelt env (Sig_bundle(tycons@recs, quals, lids, r)) in
      let rest, _, _ = tc_decls false env1 rest deserialized in
      let abbrevs = List.map2 (fun se t -> match se with
        | Sig_tycon(lid, tps, k, [], [], [], r) ->
          let tt = Util.close_with_lam tps (mk_Typ_ascribed(t, k) t.pos) in
          let tt, _ = tc_typ_trivial env1 tt in
          let tps, t = match tt.n with
            | Typ_lam(bs, t) -> bs, t
            | _ -> [], tt in
          Sig_typ_abbrev(lid, tps, compress_kind k, t, [], r)
        | _ -> failwith (Util.format1 "(%s) Impossible" (Range.string_of_range r)))
        recs abbrev_defs in
      env.solver.pop msg;
      let se = Sig_bundle(tycons@abbrevs@rest, quals, lids, r) in
      let env = Env.push_sigelt env se in
      se, env

and tc_decls for_export env ses deserialized =
 let ses, all_non_private, env =
  ses |> List.fold_left (fun (ses, all_non_private, (env:Env.env)) se ->
          if debug env Options.Low then Util.print_string (Util.format1 "Checking sigelt\t%s\n" (Print.sigelt_to_string se));

          let se, env = tc_decl env se deserialized in
          env.solver.encode_sig env se;

          let non_private_decls =
            if for_export
            then non_private env se
            else [] in

          se::ses, non_private_decls::all_non_private, env)
  ([], [], env) in
  List.rev ses, List.rev all_non_private |> List.flatten, env

and non_private env se : list<sigelt> =
   let is_private quals = List.contains Private quals in
   match se with
    | Sig_bundle(ses, quals, _, _) ->
//      if is_private quals
//      then let ses = ses |> List.filter (function
//                | Sig_datacon _ -> false
//                | _ -> true) in
//           ses |> List.map (function
//            | Sig_tycon(lid, bs, k, mutuals, datas, quals, r) -> Sig_tycon(lid, bs, k, [], [], Assumption::quals, r)
//            | se -> se)
//      else
      [se]

   | Sig_tycon(_, _, _, _, _, quals, r) ->
     if is_private quals
     then []
     else [se]

   | Sig_typ_abbrev(l, bs, k, t, quals, r) ->
     if is_private quals
     then [Sig_tycon(l, bs, k, [], [], Assumption::quals, r)]
     else [se]

   | Sig_assume(_, _, quals, _) ->
     if is_private quals
     then []
     else [se]

   | Sig_val_decl(_, _, quals, _) ->
     if is_private quals
     then []
     else [se]

   | Sig_main  _ -> []

   | Sig_new_effect     _
   | Sig_sub_effect     _
   | Sig_effect_abbrev  _
   | Sig_pragma         _
   | Sig_kind_abbrev    _ -> [se]

   | Sig_datacon _ -> failwith "Impossible"

   | Sig_let(lbs, r, l, _) ->
     let check_priv lbs =
        let is_priv = function
            | {lbname=Inr l} ->
            begin match Env.try_lookup_val_decl env l with
                    | Some (_, qs) -> List.contains Private qs
                    | _ -> false
            end
            | _ -> false in
        let some_priv = lbs |> Util.for_some is_priv in
        if some_priv
        then if lbs |> Util.for_some (fun x -> is_priv x |> not)
             then raise (Error("Some but not all functions in this mutually recursive nest are marked private", r))
             else true
        else false in


     let pure_funs, rest = snd lbs |> List.partition (fun lb -> Util.is_pure_or_ghost_function lb.lbtyp && not <| Util.is_lemma lb.lbtyp) in
     begin match pure_funs, rest with
        | _::_, _::_ ->
          raise (Error("Pure functions cannot be mutually recursive with impure functions", r))

        | _::_, [] ->
          if check_priv pure_funs
          then []
          else [se]

        | [], _::_ ->
          if check_priv rest
          then []
          else rest |> List.collect (fun lb -> match lb.lbname with
                | Inl _ -> failwith "impossible"
                | Inr l -> [Sig_val_decl(l, lb.lbtyp, [Assumption], range_of_lid l)])


        | [], [] -> failwith "Impossible"
     end

let get_exports env modul non_private_decls =
    let assume_vals decls =
        decls |> List.map (function
            | Sig_val_decl(lid, t, quals, r) -> Sig_val_decl(lid, t, Assumption::quals, r)
            | s -> s) in
    if modul.is_interface
    then non_private_decls
    else let exports = Util.find_map (Env.modules env) (fun m ->
            if (m.is_interface && Syntax.lid_equals modul.name m.name)
            then Some (m.exports |> assume_vals)
            else None) in
         match exports with
            | None -> non_private_decls
            | Some e -> e

let tc_partial_modul env modul =
  let name = Util.format2 "%s %s"  (if modul.is_interface then "interface" else "module") modul.name.str in
  let msg = "Internals for " ^name in
  let env = {env with Env.is_iface=modul.is_interface; admit=not (Options.should_verify modul.name.str)} in
  if not (lid_equals modul.name Const.prims_lid) then env.solver.push msg;
  let env = Env.set_current_module env modul.name in
  let ses, non_private_decls, env = tc_decls true env modul.declarations modul.is_deserialized in
  {modul with declarations=ses}, non_private_decls, env

let tc_more_partial_modul env modul decls =
  let ses, non_private_decls, env = tc_decls true env decls false in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, non_private_decls, env

let finish_partial_modul env modul npds =
  let exports = get_exports env modul npds in
  let modul = {modul with exports=exports; is_interface=modul.is_interface; is_deserialized=modul.is_deserialized} in
  let env = Env.finish_module env modul in
  if not (lid_equals modul.name Const.prims_lid)
  then begin
    env.solver.pop ("Ending modul " ^ modul.name.str);
    if  not modul.is_interface
    ||  List.contains modul.name.str !Options.admit_fsi
    then env.solver.encode_modul env modul;
    env.solver.refresh();
    Options.reset_options() |> ignore
  end;
  modul, env

let tc_modul env modul =
  let modul, non_private_decls, env = tc_partial_modul env modul in
  finish_partial_modul env modul non_private_decls

let add_modul_to_tcenv (en: env) (m: modul) :env =
  let do_sigelt (en: env) (elt: sigelt) :env =
    let env = Env.push_sigelt en elt in
    env.solver.encode_sig env elt;
    env
  in
  let en = Env.set_current_module en m.name in
  Env.finish_module (List.fold_left do_sigelt en m.exports) m

let check_module env m =
    if List.length !Options.debug <> 0
    then Util.fprint2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.sli m.name);

    let m, env =
        if m.is_deserialized then
          let env' = add_modul_to_tcenv env m in
          m, env'
        else begin
           let m, env = tc_modul env m in
           if !Options.serialize_mods
           then begin
                let c_file_name = Options.get_fstar_home () ^ "/" ^ Options.cache_dir ^ "/" ^ (text_of_lid m.name) ^ ".cache" in
                print_string ("Serializing module " ^ (text_of_lid m.name) ^ "\n");
                SSyntax.serialize_modul (get_owriter c_file_name) m
           end;
           m, env
      end
    in
    if Options.should_dump m.name.str then Util.fprint1 "%s\n" (Print.modul_to_string m);
    [m], env

