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
open FStar.TypeChecker.Common
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module U  = FStar.Syntax.Util

// VALS_HACK_HERE

type effect_cost = | ForFree | NotForFree

let log env = !Options.log_types && not(lid_equals Const.prims_lid (Env.current_module env))
let rng env = Env.get_range env
let instantiate_both env = {env with Env.instantiate_imp=true}
let no_inst env = {env with Env.instantiate_imp=false}
let mk_lex_list vs =
    List.fold_right (fun v tl ->
        let r = if tl.pos = Range.dummyRange then v.pos else Range.union_ranges v.pos tl.pos in
        mk_Tm_app lex_pair [as_arg v; as_arg tl] (Some lex_t.n) r)
    vs lex_top
let is_eq = function
    | Some Equality -> true
    | _ -> false
let steps env =
    if Options.should_verify env.curmodule.str
    then [N.Beta; N.Inline; N.SNComp]
    else [N.Beta; N.Inline]
let unfold_whnf env t = N.normalize [N.WHNF; N.UnfoldUntil Delta_constant; N.Beta] env t
let norm   env t = N.normalize (steps env) env t
let norm_c env c = N.normalize_comp (steps env) env c
let check_no_escape head_opt env (fvs:list<bv>) kt =
    let rec aux try_norm t = match fvs with
        | [] -> ()
        | _ ->
          let fvs' = Free.names (if try_norm then norm env t else t) in
          begin match List.tryFind (fun x -> Util.set_mem x fvs') fvs with
            | None -> ()
            | Some x ->
              if not try_norm
              then aux true t
              else let fail () =
                       let msg = match head_opt with
                        | None -> Util.format1 "Bound variables '%s' escapes; add a type annotation" (Print.bv_to_string x)
                        | Some head -> Util.format2 "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                        (Print.bv_to_string x) (N.term_to_string env head) in
                       raise (Error(msg, Env.get_range env)) in
                   let s = TcUtil.new_uvar env (fst <| U.type_u()) in
                   match Rel.try_teq env t s with
                    | Some g -> Rel.force_trivial_guard env g
                    | _ -> fail ()
         end in
    aux false kt

let maybe_push_binding env b =
  if is_null_binder b then env
  else (if Env.debug env Options.High
        then Util.print2 "Pushing binder %s at type %s\n" (Print.bv_to_string (fst b)) (Print.term_to_string (fst b).sort);
        Env.push_bv env (fst b))

let maybe_make_subst = function
  | Inr(Some x, e) -> [NT(x,e)]
  | _ -> []

let maybe_extend_subst s b v : subst_t =
    if is_null_binder b then s
    else NT(fst b, v)::s

let set_lcomp_result lc t =
    {lc with res_typ=t; comp=fun () -> Util.set_result_typ (lc.comp()) t}

let value_check_expected_typ env e tlc guard : term * lcomp * guard_t =
  let lc = match tlc with
    | Inl t -> U.lcomp_of_comp (if not (Util.is_pure_or_ghost_function t)
                                      then mk_Total t
                                      else TcUtil.return_value env t e)
    | Inr lc -> lc in
  let t = lc.res_typ in
  let e, lc, g = match Env.expected_typ env with
   | None -> e, lc, guard
   | Some t' ->
     if debug env Options.High
     then Util.print2 "Computed return type %s; expected type %s\n" (Print.term_to_string t) (Print.term_to_string t');
     let e, lc = Util.maybe_coerce_bool_to_type env e lc t' in //add a b2t coercion is e:bool and t'=Type
     let t = lc.res_typ in
     let e, g = TcUtil.check_and_ascribe env e t t' in
     if debug env Options.High
     then Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" (Print.term_to_string t) (Rel.guard_to_string env g);
     let g = Rel.conj_guard g guard in
     let lc, g = TcUtil.strengthen_precondition (Some <| Errors.subtyping_failed env t t') env e lc g in
     e, set_lcomp_result lc t', g in
  if debug env Options.Low
  then Util.print1 "Return comp type is %s\n" (Print.lcomp_to_string lc);
  e, lc, g

let comp_check_expected_typ env e lc : term * lcomp * guard_t =
  match Env.expected_typ env with
   | None -> e, lc, Rel.trivial_guard
   | Some t ->
     let e, lc = Util.maybe_coerce_bool_to_type env e lc t in //Add a b2t coercion if e:bool and t=Type
     TcUtil.weaken_result_typ env e lc t

let check_expected_effect env (copt:option<comp>) (e, c) : term * comp * guard_t =
  let expected_c_opt = match copt with
    | Some _ -> copt
    | None  ->
        if !Options.ml_ish && Ident.lid_equals Const.effect_ALL_lid (Util.comp_effect_name c)
        then Some (Util.ml_comp (Util.comp_result c) e.pos)
        else if (*	env.top_level  || *)
                Util.is_tot_or_gtot_comp c //these are already the defaults for their particular effects
        then None
        else if Util.is_pure_comp c
             then Some (mk_Total (Util.comp_result c))
             else if Util.is_pure_or_ghost_comp c
             then Some (mk_GTotal (Util.comp_result c))
             else None in
  match expected_c_opt with
    | None -> e, norm_c env c, Rel.trivial_guard
    | Some expected_c -> //expected effects should already be normalized
       if debug env Options.Low
       then Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
               (Print.term_to_string e) (Print.comp_to_string c) (Print.comp_to_string expected_c);
       let c = norm_c env c in
       if debug env Options.Low
       then Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
               (Print.term_to_string e) (Print.comp_to_string c) (Print.comp_to_string expected_c);

       //let expected_c' = TcUtil.refresh_comp_label env true (U.lcomp_of_comp <| expected_c) in
       let e, _, g = TcUtil.check_comp env e c expected_c in
       let g = TcUtil.label_guard (Env.get_range env) "could not prove post-condition" g in
       if debug env Options.Low then Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" (Range.string_of_range e.pos) (guard_to_string env g);
       e, expected_c, g

let no_logical_guard env (te, kt, f) =
  match guard_form f with
    | Trivial -> te, kt, f
    | NonTrivial f -> raise (Error(Errors.unexpected_non_trivial_precondition_on_term env f, Env.get_range env))

let print_expected_ty env = match Env.expected_typ env with
    | None -> Util.print_string "Expected type is None"
    | Some t -> Util.print1 "Expected type is %s" (Print.term_to_string t)

(************************************************************************************************************)
(* check the patterns in an SMT lemma to make sure all bound vars are mentiond *)
(************************************************************************************************************)
let check_smt_pat env t bs c =
    if Util.is_smt_lemma t //check patterns cover the bound vars
    then match c.n with
        | Comp ({effect_args=[_pre; _post; (pats, _)]}) ->
            let pat_vars = Free.names pats in
            begin match bs |> Util.find_opt (fun (b, _) -> not(Util.set_mem b pat_vars)) with
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
      let precedes = TcUtil.fvar_const env Const.precedes_lid in

      let decreases_clause bs c =
          //exclude types and function-typed arguments from the decreases clause
          let filter_types_and_functions (bs:binders)  =
            bs |> List.collect (fun (b, _) ->
                    let t = unfold_whnf env (Util.unrefine b.sort) in
                    match t.n with
                        | Tm_type _
                        | Tm_arrow _ -> []
                        | _ -> [S.bv_to_name b]) in
          let as_lex_list dec =
                let head, _ = Util.head_and_args dec in
                match head.n with (* The decreases clause is always an expression of type lex_t; promote if it isn't *)
                    | Tm_fvar fv when S.fv_eq_lid fv Const.lexcons_lid -> dec
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
                  //make sure they all have non-null names
                  let formals = formals |> List.map (fun (x, imp) -> if S.is_null_bv x then (S.new_bv (Some (S.range_of_bv x)) x.sort, imp) else x,imp) in
        (*open*)  let formals, c = SS.open_comp formals c in
                  let dec = decreases_clause formals c in
                  let precedes = mk_Tm_app precedes [as_arg dec; as_arg previous_dec] None r in
                  let bs, (last, imp) = Util.prefix formals in
                  let last = {last with sort=Util.refine last precedes} in
                  let refined_formals = bs@[(last,imp)] in
        (*close*) let t' = Util.arrow refined_formals c in
                  if debug env Options.Low
                  then Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                        (Print.lbname_to_string l) (Print.term_to_string t) (Print.term_to_string t');
                  l,t'

                | _ -> failwith "Impossible: Annotated type of 'let rec' is not an arrow" in

        letrecs |> List.map guard_one_letrec

(************************************************************************************************************)
(* Main type-checker begins here                                                                            *)
(************************************************************************************************************)
let rec tc_term env e = tc_maybe_toplevel_term ({env with top_level=false}) e

and tc_maybe_toplevel_term env (e:term) : term                  (* type-checked and elaborated version of e            *)
                                        * lcomp                 (* computation type where the WPs are lazily evaluated *)
                                        * guard_t =             (* well-formedness condition                           *)
  let env = if e.pos=Range.dummyRange then env else Env.set_range env e.pos in
  if debug env Options.Low then Util.print2 "%s (%s)\n" (Range.string_of_range <| Env.get_range env) (Print.tag_of_term e);
  let top = e in
  match e.n with
  | Tm_delayed _ -> tc_term env (SS.compress e)

  | Tm_uinst _
  | Tm_uvar _
  | Tm_bvar _
  | Tm_name _
  | Tm_fvar _
  | Tm_constant _
  | Tm_abs _
  | Tm_arrow _
  | Tm_refine _
  | Tm_type _
  | Tm_unknown -> tc_value env e

  | Tm_meta(e, Meta_desugared Meta_smt_pat) ->
    let e, c, g = tc_tot_or_gtot_term env e in
    let g = {g with guard_f=Trivial} in //VC's in SMT patterns are irrelevant
    e, c, g //strip the Meta going up

  | Tm_meta(e, Meta_pattern pats) ->
    let t, u = U.type_u () in
    let e, c, g = tc_check_tot_or_gtot_term env e t in
    let pats, g' =
        let env, _ = Env.clear_expected_typ env in
        tc_pats env pats in
    let g' = {g' with guard_f=Trivial} in //The pattern may have some VCs associated with it, but these are irrelevant.
    mk (Tm_meta(e, Meta_pattern pats)) (Some t.n) top.pos,
    c,
    Rel.conj_guard g g' //but don't drop g' altogether, since it also contains unification constraints

  | Tm_meta(e, Meta_desugared Sequence) ->
    begin match (SS.compress e).n with
        | Tm_let((_,[{lbname=x; lbdef=e1}]), e2) -> //NS: Why not handle this specially in the deugaring phase, adding a unit annotation on x?
          let e1, c1, g1 = tc_term (Env.set_expected_typ env Common.t_unit) e1 in
          let e2, c2, g2 = tc_term env e2 in
          let c = TcUtil.bind env (Some e1) c1 (None, c2) in
          let e = mk (Tm_let((false, [mk_lb (x, [], c1.eff_name, Common.t_unit, e1)]), e2)) (Some c.res_typ.n) e.pos in
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

  | Tm_ascribed (e, Inr expected_c, _) ->
    let expected_c, _, g = tc_comp env expected_c in
    let e, c', g' = tc_term env e in
    let e, expected_c, g'' = check_expected_effect env (Some expected_c) (e, c'.comp()) in
    let t_res = Util.comp_result expected_c in
    mk (Tm_ascribed(e, Inl t_res, Some (Util.comp_effect_name expected_c))) (Some t_res.n) top.pos,
    Util.lcomp_of_comp expected_c,
    Rel.conj_guard g (Rel.conj_guard g' g'')

  | Tm_ascribed (e, Inl t, _) ->
    let k, u = U.type_u () in
    let t, _, f = tc_check_tot_or_gtot_term env t k in
    let e, c, g = tc_term (Env.set_expected_typ env t) e in
    let c, f = TcUtil.strengthen_precondition (Some (fun () -> Errors.ill_kinded_type)) (Env.set_range env t.pos) e c f in
    let e, c, f2 = comp_check_expected_typ env (mk (Tm_ascribed(e, Inl t, Some c.eff_name)) (Some t.n) top.pos) c in
    e, c, Rel.conj_guard f (Rel.conj_guard g f2)

  | Tm_app(head, args) ->
    let env0 = env in
    let env = Env.clear_expected_typ env |> fst |> instantiate_both in
    if debug env Options.High then Util.print2 "(%s) Checking app %s\n" (Range.string_of_range top.pos) (Print.term_to_string top);


    //Don't instantiate head; instantiations will be computed below, accounting for implicits/explicits
    let head, chead, g_head = tc_term (no_inst env) head in
    let e, c, g = if TcUtil.short_circuit_head head
                  then check_short_circuit_args env head chead g_head args (Env.expected_typ env0)
                  else check_application_args env head chead g_head args (Env.expected_typ env0) in
    if Env.debug env Options.Extreme
    then Util.print1 "Introduced {%s} implicits in application\n" (Rel.print_pending_implicits g);
    let c = if Options.should_verify env.curmodule.str
            && not (Util.is_lcomp_partial_return c)
            && Util.is_pure_or_ghost_lcomp c //ADD_EQ_REFINEMENT for pure applications
            then TcUtil.maybe_assume_result_eq_pure_term env e c
            else c in
    let e, c, g' = comp_check_expected_typ env0 e c in
    let gimp =
        match (SS.compress head).n with
            | Tm_uvar(u, _) ->
              let imp = ("head of application is a uvar", env0, u, e, c.res_typ, head.pos) in
              {Rel.trivial_guard with implicits=[imp]}
            | _ -> Rel.trivial_guard in
    let gres = Rel.conj_guard g (Rel.conj_guard g' gimp) in
    if Env.debug env Options.Extreme
    then Util.print1 "Guard from application node is %s\n" (Rel.guard_to_string env gres);
    e, c, gres

  | Tm_match(e1, eqns) ->
    let env1, topt = Env.clear_expected_typ env in
    let env1 = instantiate_both env1 in
    let e1, c1, g1 = tc_term env1 e1 in
    let env_branches, res_t = match topt with
      | Some t -> env, t
      | None ->
        let k, _ = U.type_u() in
        let res_t = TcUtil.new_uvar env k in
        Env.set_expected_typ env res_t, res_t in

    let guard_x = S.gen_bv "scrutinee" (Some e1.pos) c1.res_typ in
    let t_eqns = eqns |> List.map (tc_eqn guard_x env_branches) in
    let c_branches, g_branches =
      let cases, g = List.fold_right (fun (_, f, c, g) (caccum, gaccum) ->
        (f, c)::caccum, Rel.conj_guard g gaccum) t_eqns ([], Rel.trivial_guard) in
      TcUtil.bind_cases env res_t cases, g in (* bind_cases adds an exhaustiveness check *)

    let cres = TcUtil.bind env (Some e1) c1 (Some guard_x, c_branches) in
    let e = mk (Tm_match(e1, List.map (fun (f, _, _, _) -> f) t_eqns)) (Some cres.res_typ.n) top.pos in
    //NS: TODO remove ascription below? used to be important to ascribe, for recomputing types
    let e = mk (Tm_ascribed(e, Inl cres.res_typ, Some cres.eff_name)) None e.pos in
    if debug env Options.Extreme
    then Util.print2 "(%s) comp type = %s\n"
                      (Range.string_of_range top.pos) (Print.comp_to_string <| cres.comp());

    e, cres, Rel.conj_guard g1 g_branches

  | Tm_let ((false, [{lbname=Inr _}]), _) ->
    if Env.debug env Options.Low then Util.print1 "%s\n" (Print.term_to_string top);
    check_top_level_let env top

  | Tm_let ((false, _), _) ->
    check_inner_let env top

  | Tm_let ((true, {lbname=Inr _}::_), _) ->
    if Env.debug env Options.Low then Util.print1 "%s\n" (Print.term_to_string top);
    check_top_level_let_rec env top

  | Tm_let ((true, _), _) ->
    check_inner_let_rec env top

(************************************************************************************************************)
(* Type-checking values:                                                                                    *)
(*   Values have no special status, except that we structure the code to promote a value type t to a Tot t  *)
(************************************************************************************************************)
and tc_value env (e:term) : term
                          * lcomp
                          * guard_t =
  let check_instantiated_fvar env v dc e t =
    let e, t, implicits = TcUtil.maybe_instantiate env e t in
    //printfn "Instantiated type of %s to %s\n" (Print.term_to_string e) (Print.term_to_string t);
    let tc = if Options.should_verify env.curmodule.str then Inl t else Inr (U.lcomp_of_comp <| mk_Total t) in
    let is_data_ctor = function
        | Some Data_ctor
        | Some (Record_ctor _) -> true
        | _ -> false in
    if is_data_ctor dc && not(Env.is_datacon env v.v)
    then raise (Error(Util.format1 "Expected a data constructor; got %s" v.v.str, Env.get_range env))
    else value_check_expected_typ env e tc implicits in

  //As a general naming convention, we use e for the term being analyzed and its subterms as e1, e2, etc.
  //We use t and its variants for the type of the term being analyzed
  let env = Env.set_range env e.pos in
  let top = SS.compress e in
  match top.n with
  | Tm_bvar x ->
    failwith "Impossible: Violation of locally nameless convention"

  | Tm_uvar(u, t1) -> //the type of a uvar is given directly with it; we do not recheck the type
    let g = match (SS.compress t1).n with
        | Tm_arrow _ -> Rel.trivial_guard
        | _ -> let imp = ("uvar in term", env, u, top, t1, top.pos) in
               {Rel.trivial_guard with implicits=[imp]} in
//    let g = Rel.trivial_guard in
    value_check_expected_typ env e (Inl t1) g

  | Tm_unknown -> //only occurs where type annotations are missing in source programs
    let k, u = U.type_u () in
    let t = TcUtil.new_uvar env k in
    let e = TcUtil.new_uvar env t in
    value_check_expected_typ env e (Inl t) Rel.trivial_guard

  | Tm_name x ->
    let t = if env.use_bv_sorts then x.sort else Env.lookup_bv env x in
    let e = S.bv_to_name ({x with sort=t}) in
    let e, t, implicits = TcUtil.maybe_instantiate env e t in
    let tc = if Options.should_verify env.curmodule.str then Inl t else Inr (U.lcomp_of_comp <| mk_Total t) in
    value_check_expected_typ env e tc implicits

  | Tm_uinst({n=Tm_fvar fv}, us) ->
    let us = List.map (tc_universe env) us in
    let us', t = Env.lookup_lid env fv.fv_name.v in
    if List.length us <> List.length us'
    then raise (Error("Unexpected number of universe instantiations", Env.get_range env))
    else List.iter2 (fun u' u -> match u' with
            | U_unif u'' -> Unionfind.change u'' (Some u)
            | _ -> failwith "Impossible") us' us;
    let fv' = {fv with fv_name={fv.fv_name with ty=t}} in
    let e = S.mk_Tm_uinst (mk (Tm_fvar fv') (Some t.n) e.pos) us in
    check_instantiated_fvar env fv'.fv_name fv'.fv_qual e t

  | Tm_fvar fv ->
    let us, t = Env.lookup_lid env fv.fv_name.v in
    let fv' = {fv with fv_name={fv.fv_name with ty=t}} in
    let e = S.mk_Tm_uinst (mk (Tm_fvar fv') (Some t.n) e.pos) us in
    check_instantiated_fvar env fv'.fv_name fv'.fv_qual e t

  | Tm_constant c ->
    let t = tc_constant env top.pos c in
    let e = mk (Tm_constant c) (Some t.n) e.pos in
    value_check_expected_typ env e (Inl t) Rel.trivial_guard

  | Tm_arrow(bs, c) ->
    let bs, c = SS.open_comp bs c in
    let env0 = env in
    let env, _ = Env.clear_expected_typ env in
    let bs, env, g, us = tc_binders env bs in
    let c, uc, f = tc_comp env c in
    let e = {Util.arrow bs c with pos=top.pos} in
    check_smt_pat env e bs c;
    let u = S.U_max (uc::us) in
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
    let env, _ = Env.clear_expected_typ env in
    let x, env, f1, u = tc_binder env (List.hd x) in
    if debug env Options.High
    then Util.print3 "(%s) Checking refinement formula %s; binder is %s\n"
        (Range.string_of_range top.pos) (Print.term_to_string phi) (Print.bv_to_string (fst x));
    let t_phi, _ = U.type_u () in
    let phi, _, f2 = tc_check_tot_or_gtot_term env phi t_phi in
    let e = {Util.refine (fst x) phi with pos=top.pos} in
    let t = mk (Tm_type u) None top.pos in
    let g = Rel.conj_guard f1 (Rel.close_guard [x] f2) in
    value_check_expected_typ env0 e (Inl t) g

  | Tm_abs(bs, body, _) ->
    let bs = Util.maybe_add_implicit_binders env bs in
    if Env.debug env Options.Low
    then Util.print1 "Abstraction is: %s\n" (Print.term_to_string ({top with n=Tm_abs(bs, body, None)}));
    let bs, body = SS.open_term bs body in
    tc_abs env top bs body

  | _ ->
    failwith (Util.format1 "Unexpected value: %s" (Print.term_to_string top))

and tc_constant env r (c:sconst) : typ =
     match c with
      | Const_unit -> t_unit
      | Const_bool _ -> t_bool
      | Const_int (_, None) -> t_int
      | Const_int (_, Some (Unsigned, Int8)) -> t_uint8
      | Const_int (_, Some (Signed, Int8)) -> t_int8
      | Const_int (_, Some (Unsigned, Int16)) -> t_uint16
      | Const_int (_, Some (Signed, Int16)) -> t_int16
      | Const_int (_, Some (Unsigned, Int32)) -> t_uint32
      | Const_int (_, Some (Signed, Int32)) -> t_int32
      | Const_int (_, Some (Unsigned, Int64)) -> t_uint64
      | Const_int (_, Some (Signed, Int64)) -> t_int64
      | Const_string _ -> t_string
      | Const_float _ -> t_float
      | Const_char _ -> t_char
      | Const_effect -> Util.ktype0 //NS: really?
      | Const_range _ ->
        let fail () =
            raise (Error("Range constant cannot be checked in this context; expected an instance of 'range_of'", r)) in
        begin match Env.expected_typ env with
            | None -> fail ()
            | Some t ->
              if Option.isSome (U.destruct t Const.range_of_lid)
              then t
              else fail()
        end

      | _ -> raise (Error("Unsupported constant", r))


(************************************************************************************************************)
(* Type-checking computation types                                                                          *)
(************************************************************************************************************)
and tc_comp env c : comp                                      (* checked version of c                       *)
                  * universe                                  (* universe of c.result_typ                   *)
                  * guard_t =                             (* logical guard for the well-formedness of c *)
  match c.n with
    | Total t ->
      let k, u = U.type_u () in
      let t, _, g = tc_check_tot_or_gtot_term env t k in
      mk_Total t, u, g

    | GTotal t ->
      let k, u = U.type_u () in
      let t, _, g = tc_check_tot_or_gtot_term env t k in
      mk_GTotal t, u, g

    | Comp c ->
      let head = S.fvar c.effect_name Delta_constant None in
      let tc = mk_Tm_app head ((as_arg c.result_typ)::c.effect_args) None c.result_typ.pos in
      let tc, _, f = tc_check_tot_or_gtot_term env tc S.teff in
      let _, args = Util.head_and_args tc in
      let res, args = List.hd args, List.tl args in
      let flags, guards = c.flags |> List.map (function
        | DECREASES e ->
            let env, _ = Env.clear_expected_typ env in
            let e, _, g = tc_tot_or_gtot_term env e in
            DECREASES e, g
        | f -> f, Rel.trivial_guard) |> List.unzip in
      let u = match !(fst res).tk with //TODO:ugly
        | Some (Tm_type u) -> u
        | _ -> failwith "Impossible" in
      mk_Comp ({c with
          result_typ=fst res;
          effect_args=args}),
      u,
      List.fold_left Rel.conj_guard f guards

and tc_universe env u : universe =
   let rec aux u =
       let u = SS.compress_univ u in
       match u with
        | U_bvar _  -> failwith "Impossible: locally nameless"
        | U_unknown -> failwith "Unknown universe"
        | U_unif _
        | U_zero    -> u
        | U_succ u  -> U_succ (aux u)
        | U_max us  -> U_max (List.map aux us)
        | U_name x  -> if env.use_bv_sorts || Env.lookup_univ env x
                       then u
                       else raise (Error (Util.format1 "Universe variable '%s' not found" x.idText, Env.get_range env)) in
    match u with
        | U_unknown -> U.type_u () |> snd
        | _ -> aux u

(* Several complex cases from the main type-checker are factored in to separate functions below *)

(*******************************************************************************************************************)
(* Type-checking abstractions, aka lambdas                                                                         *)
(*    top = fun bs -> body, although bs and body must already be opened                                            *)
(*******************************************************************************************************************)
and tc_abs env (top:term) (bs:binders) (body:term) : term * lcomp * guard_t =
    let fail :string -> typ -> 'a = fun msg t ->
        raise (Error(Errors.expected_a_term_of_type_t_got_a_function env msg t top, top.pos)) in

    (***************************************************************************************************************)
    (* check_binders checks that the binders bs of top                                                             *)
    (*               are compatible with the binders of the function typ expected by the context                   *)
    (*               If there are more bs than bs_expected, we only check a prefix and the suffix is returned Inl  *)
    (*               If there are more bs_expected than bs, the suffix of bs_expected is returned Inr              *)
    (***************************************************************************************************************)
    let check_binders env bs bs_expected  : Env.env                           (* env extended with a prefix of bs  *)
                                            * binders                         (* a type-checked prefix of bs       *)
                                            * option<either<binders,binders>> (* suffix of either bs or bs_expected*)
                                            * guard_t                         (* accumulated logical guard         *)
                                            * subst_t =                         (* alpha conv. of bs_expected to bs  *)
        let rec aux (env, out, g, subst) (bs:binders) (bs_expected:binders) = match bs, bs_expected with
            | [], [] -> env, List.rev out, None, g, subst

            | (hd, imp)::bs, (hd_expected, imp')::bs_expected ->
               begin match imp, imp' with
                    | None, Some (Implicit _)
                    | Some (Implicit _), None ->
                      raise (Error(Util.format1 "Inconsistent implicit argument annotation on argument %s" (Print.bv_to_string hd),
                                                  S.range_of_bv hd))
                    | _ -> ()
               end;
               let expected_t = SS.subst subst hd_expected.sort in
               let t, g = match (Util.unmeta hd.sort).n with
                    | Tm_unknown -> expected_t, g
                    | _ ->
                      if Env.debug env Options.High then Util.print1 "Checking binder %s\n" (Print.bv_to_string hd);
                      let t, _, g1 = tc_tot_or_gtot_term env hd.sort in
                      let g2 =
                          TcUtil.label_guard (Env.get_range env)
                            "Type annotation on parameter incompatible with the expected type"
                            (Rel.teq env t expected_t) in
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


    let rec expected_function_typ env t0 body
        : (option<(typ*bool)> (* any remaining expected type to check against; bool signals to check using teq *)
        * binders             (* binders from the abstraction checked against the binders in the corresponding Typ_fun, if any *)
        * binders             (* let rec binders, suitably guarded with termination check, if any *)
        * option<comp>        (* the expected comp type for the body *)
        * Env.env             (* environment for the body *)
        * term                (* the body itself *)
        * guard_t)            (* accumulated guard from checking the binders *)
        =
       match t0 with
        | None -> (* no expected type; just build a function type from the binders in the term *)
            let _ = match env.letrecs with
                | [] -> ()
                | _ -> failwith "Impossible: Can't have a let rec annotation but no expected type" in
            let bs, envbody, g, _ = tc_binders env bs in
            let copt, body, g = match (SS.compress body).n with
                | Tm_ascribed(e, Inr c, _) ->
                  let c, _, g' = tc_comp envbody c in
                  Some c, body, Rel.conj_guard g g'
                | _ -> None, body, g in
            None, bs, [], copt, envbody, body, g

        | Some t ->
           let t = SS.compress t in
           let rec as_function_typ norm t =
               match (SS.compress t).n with
                | Tm_uvar _
                | Tm_app({n=Tm_uvar _}, _) -> (* expected a uvar; build a function type from the term and unify with it *)
                  let _ = match env.letrecs with | [] -> () | _ -> failwith "Impossible" in
                  let bs, envbody, g, _ = tc_binders env bs in
                  let envbody, _ = Env.clear_expected_typ envbody in
                  Some (t, true), bs, [], None, envbody, body, g

                (* CK: add this case since the type may be f:(a -> M b wp){φ}, in which case I drop the refinement *)
                (* NS: 07/21 dropping the refinement is not sound; we need to check that f validates phi. See Bug #284 *)
                | Tm_refine (b, _) ->
                  let _, bs, bs', copt, env, body, g = as_function_typ norm b.sort in
                  Some (t, false), bs, bs', copt, env, body, g

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
                          then let t = unfold_whnf env (Util.comp_result c) in
                               match t.n with
                                | Tm_arrow(bs_expected, c_expected) ->
                                  let (env, bs', more, guard', subst) = check_binders env more_bs bs_expected in
                                  handle_more (env, bs@bs', more, Rel.conj_guard guard guard', subst) c_expected
                                | _ -> fail (Util.format1 "More arguments than annotated type (%s)" (Print.term_to_string t)) t
                          else fail "Function definition takes more arguments than expected from its annotated type" t in

                       handle_more (check_binders env bs bs_expected) c_expected in

                 let mk_letrec_env envbody bs c =
                     let letrecs = guard_letrecs envbody bs c in
                     let envbody = {envbody with letrecs=[]} in
                     letrecs |> List.fold_left (fun (env, letrec_binders) (l,t) ->
//                        let t = N.normalize [N.EraseUniverses; N.Beta] env t in
//                        printfn "Checking let rec annot: %s\n" (Print.term_to_string t);
                        let t, _, _ = tc_term (Env.clear_expected_typ env |> fst) t in
                        let env = Env.push_let_binding env l ([], t) in
                        let lb = match l with
                            | Inl x -> S.mk_binder ({x with sort=t})::letrec_binders
                            | _ -> letrec_binders in
                        env, lb)
                      (envbody, []) in

                 let envbody, bs, g, c = check_actuals_against_formals env bs bs_expected in
                 let envbody, letrecs = if Options.should_verify env.curmodule.str then mk_letrec_env envbody bs c else envbody, [] in
                 let envbody = Env.set_expected_typ envbody (Util.comp_result c) in
                 Some (t, false), bs, letrecs, Some c, envbody, body, g

                | _ -> (* expected type is not a function;
                          try normalizing it first;
                          otherwise synthesize a type and check it against the given type *)
                  if not norm
                  then as_function_typ true (unfold_whnf env t)
                  else let _, bs, _, c_opt, envbody, body, g = expected_function_typ env None body in
                       Some (t, false), bs, [], c_opt, envbody, body, g in
           as_function_typ false t in

    let use_eq = env.use_eq in
    let env, topt = Env.clear_expected_typ env in

    if Env.debug env Options.High
    then Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
          (match topt with | None -> "None" | Some t -> Print.term_to_string t)
          (if env.top_level then "true" else "false");

    let tfun_opt, bs, letrec_binders, c_opt, envbody, body, g = expected_function_typ env topt body in
    let body, cbody, guard_body = tc_term ({envbody with top_level=false; use_eq=use_eq}) body in

    let guard_body =  //we don't abstract over subtyping constraints; so solve them now
        Rel.solve_deferred_constraints envbody guard_body in

    if Env.debug env <| Options.Other "Implicits"
    then Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
        (string_of_int <| List.length guard_body.implicits)
        (Print.comp_to_string <| cbody.comp());

    let body, cbody, guard = check_expected_effect ({envbody with use_eq=use_eq}) c_opt (body, cbody.comp()) in
    let guard = Rel.conj_guard guard_body guard in
    let guard = if env.top_level || not(Options.should_verify env.curmodule.str)
                then Rel.discharge_guard envbody (Rel.conj_guard g guard)
                else let guard = Rel.close_guard (bs@letrec_binders) guard in
                     Rel.conj_guard g guard in

    let tfun_computed = Util.arrow bs cbody in
    let e = Util.abs bs body (Some (Util.lcomp_of_comp cbody |> Inl)) in
    let e, tfun, guard = match tfun_opt with
        | Some (t, use_teq) ->
           let t = SS.compress t in
           begin match t.n with
                | Tm_arrow _ ->
                    //we already checked the body to have the expected type; so, no need to check again
                    //just repackage the expression with this type; t is guaranteed to be alpha equivalent to tfun_computed
                    e, t, guard
                | _ ->
                    let e, guard' =
                        if use_teq
                        then e, Rel.teq env t tfun_computed
                        else TcUtil.check_and_ascribe env e tfun_computed t in
                    e, t, Rel.conj_guard guard guard'
           end

        | None -> e, tfun_computed, guard in

    let c = if env.top_level then mk_Total tfun else TcUtil.return_value env tfun e in
    let c, g = TcUtil.strengthen_precondition None env e (U.lcomp_of_comp c) guard in
    e, c, g

(******************************************************************************)
(* Type-checking applications: Tm_app head args                               *)
(*      head is already type-checked has comp type chead, with guard ghead    *)
(******************************************************************************)
and check_application_args env head chead ghead args expected_topt : term * lcomp * guard_t=
    let n_args = List.length args in
    let r = Env.get_range env in
    let thead = chead.res_typ in
    if debug env Options.High then Util.print2 "(%s) Type of head is %s\n" (Range.string_of_range head.pos) (Print.term_to_string thead);
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
            (* Infer: t1 -> ... -> tn -> C ('u x1...xm),
                    where ti are the result types of each arg
                    and   xi are the free type/term variables in the environment
               where C = GTot, if the expected result type is Type(u)
                else C = Tot,  if the ML monad is not in scope
                else C = ML,   otherwise *)
            let args, comps, g_args = tc_args env args in
            let bs = null_binders_of_tks (comps |> List.map (fun c -> c.res_typ, None)) in
            let ml_or_tot = match Env.try_lookup_effect_lid env Const.effect_ML_lid with
                | None -> fun t r -> S.mk_Total t
                | _ -> Util.ml_comp in
            let ml_or_tot = match expected_topt with
                | None -> ml_or_tot
                | Some t ->
                  match (SS.compress t).n with
                    | Tm_type _ -> fun t r -> S.mk_GTotal t
                    | _ -> ml_or_tot in

            let cres = ml_or_tot (TcUtil.new_uvar env (U.type_u () |> fst)) r in
            let bs_cres = Util.arrow bs cres in
            if Env.debug env <| Options.Extreme
            then Util.print3 "Forcing the type of %s from %s to %s\n"
                            (Print.term_to_string head)
                            (Print.term_to_string tf)
                            (Print.term_to_string bs_cres);
            Rel.force_trivial_guard env <| Rel.teq env tf bs_cres;
            let comp = List.fold_right (fun c out -> TcUtil.bind env None c (None, out)) (chead::comps) (U.lcomp_of_comp <| cres) in
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
            | (x, Some (Implicit _))::rest, (_, None)::_ -> (* instantiate an implicit arg *)
                let t = SS.subst subst x.sort in
                check_no_escape (Some head) env fvs t;
                let varg, _, implicits = TcUtil.new_implicit_var "Instantiating implicit argument in application" head.pos env t in //new_uvar env t in
                let subst = NT(x, varg)::subst in
                let arg = varg, as_implicit true in
                tc_args (subst, arg::outargs, arg::arg_rets, comps, Rel.conj_guard implicits g, fvs) rest cres args

            | (x, aqual)::rest, (e, aq)::rest' -> (* a concrete argument *)
                let _ = match aqual, aq with
                | Some (Implicit _), Some (Implicit _)
                | None, None
                | Some Equality, None -> ()
                | _ -> raise (Error("Inconsistent implicit qualifier", e.pos)) in
                let targ = SS.subst subst x.sort in
                let x = {x with sort=targ} in
                if debug env Options.Extreme then  Util.print1 "\tType of arg (after subst) = %s\n" (Print.term_to_string targ);
                check_no_escape (Some head) env fvs targ;
                let env = Env.set_expected_typ env targ in
                let env = {env with use_eq=is_eq aqual} in
                if debug env Options.High then  Util.print3 "Checking arg (%s) %s at type %s\n" (Print.tag_of_term e) (Print.term_to_string e) (Print.term_to_string targ);
                let e, c, g_e = tc_term env e in
                let g = Rel.conj_guard g g_e in
//                if debug env Options.High then Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" (guard_to_string env g_e) (guard_to_string env g);
                let arg = e, aq in
                if Util.is_tot_or_gtot_lcomp c //e is Tot or GTot; we can just substitute it
                then let subst = maybe_extend_subst subst (List.hd bs) e in
                    tc_args (subst, arg::outargs, arg::arg_rets, comps, g, fvs) rest cres rest'
                else if TcUtil.is_pure_or_ghost_effect env c.eff_name //its conditionally pure; can substitute, but must check its WP
                then let subst = maybe_extend_subst subst (List.hd bs) e in
                     let comps, guard =
                        (Some x, c)::comps, g in
                     tc_args (subst, arg::outargs, arg::arg_rets, comps, guard, fvs) rest cres rest'
                else if is_null_binder (List.hd bs) //it's not pure, but the function isn't dependent; just check its WP
                then let newx = S.new_bv (Some e.pos) c.res_typ in
                     let arg' = S.as_arg <| S.bv_to_name newx in
                     tc_args (subst, arg::outargs, arg'::arg_rets, (Some newx, c)::comps, g, fvs) rest cres rest'
                else //e is impure and the function may be dependent...
                     //need to check that the variable does not occur free in the rest of the function type
                     //by adding x to fvs
                     tc_args (subst, arg::outargs, S.as_arg (S.bv_to_name x)::arg_rets,
                             (Some x, c)::comps, g, x::fvs) rest cres rest'

            | _, [] -> (* no more args; full or partial application *)
                check_no_escape (Some head) env fvs cres.res_typ;
                let cres, g =
                  match bs with
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
                                    then Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n"
                                        (Print.term_to_string head) (Print.lcomp_to_string cres) (guard_to_string env g);
                                    cres) in

                        (* TODO: relabeling the labeled sub-terms in cres to report failing pre-conditions at this call-site *)
                        cres, g

                    | _ ->  (* partial app *)
                        let g = Rel.conj_guard ghead g |> Rel.solve_deferred_constraints env in
                        U.lcomp_of_comp <| mk_Total  (SS.subst subst <| Util.arrow bs (cres.comp())), g in

                if debug env Options.Low then Util.print1 "\t Type of result cres is %s\n" (Print.lcomp_to_string cres);
                let comp = List.fold_left (fun out c -> TcUtil.bind env None (snd c) (fst c, out)) cres comps in
                let comp = TcUtil.bind env None chead (None, comp) in
                let app =  mk_Tm_app head (List.rev outargs) (Some comp.res_typ.n) r in
                let comp = TcUtil.record_application_site env app comp in
                let comp, g = TcUtil.strengthen_precondition None env app comp g in //Each conjunct in g is already labeled
                app, comp, g


            | [], arg::_ -> (* too many args, except maybe c returns a function *)
                let rec aux norm tres =
                let tres = SS.compress tres |> Util.unrefine in
                match tres.n with
                    | Tm_arrow(bs, cres') ->
                        if debug env Options.Low
                        then Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n"
                            (Range.string_of_range tres.pos);
                        tc_args (subst, outargs, arg_rets, (None, cres)::comps, g, fvs) bs (U.lcomp_of_comp cres') args
                    | _ when (not norm) ->
                        aux true (unfold_whnf env tres)
                    | _ -> raise (Error(Util.format2 "Too many arguments to function of type %s; got %s arguments"
                                            (N.term_to_string env tf) (Util.string_of_int n_args), argpos arg)) in
                aux false cres.res_typ in

            tc_args ([], [], [], [], Rel.trivial_guard, []) bs (U.lcomp_of_comp c) args

        | _ ->
            if not norm
            then check_function_app true (unfold_whnf env tf)
            else raise (Error(Errors.expected_function_typ env tf, head.pos)) in

    check_function_app false (N.normalize [N.Beta;N.WHNF] env (Util.unrefine thead))

(******************************************************************************)
(* SPECIAL CASE OF CHECKING APPLICATIONS:                                     *)
(*        head symbol is one of &&, ||, /\, \/, ==>                           *)
(*   ALL OF THEM HAVE A LOGICAL SPEC THAT IS BIASED L-to-R,                   *)
(*  aka they are short-circuiting                                             *)
(******************************************************************************)
and check_short_circuit_args env head chead g_head args expected_topt : term * lcomp * guard_t =
    let r = Env.get_range env in
    let tf = SS.compress chead.res_typ in
    match tf.n with
        | Tm_arrow(bs, c) when (Util.is_total_comp c && List.length bs=List.length args) ->
          let res_t = Util.comp_result c in
          let args, guard, ghost = List.fold_left2 (fun (seen, guard, ghost) (e, aq) (b, aq') ->
                if aq<>aq' then raise (Error("Inconsistent implicit qualifiers", e.pos));
                let e, c, g = tc_check_tot_or_gtot_term env e b.sort in //NS: this forbids stuff like !x && y, maybe that's ok
                let short = TcUtil.short_circuit head seen in
                let g = Rel.imp_guard (Rel.guard_of_guard_formula short) g in
                let ghost = ghost
                          || (not (Util.is_total_lcomp c)
                              && not (TcUtil.is_pure_effect env c.eff_name)) in
                seen@[as_arg e], Rel.conj_guard guard g, ghost) ([], g_head, false) args bs in
          let e = mk_Tm_app head args (Some res_t.n) r  in
          let c = if ghost then S.mk_GTotal res_t |> Util.lcomp_of_comp else Util.lcomp_of_comp c in
          let c, g = TcUtil.strengthen_precondition None env e c guard in
          e, c, g

        | _ -> //fallback
          check_application_args env head chead g_head args expected_topt


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
  let cpat, _, cbr = branch in

  (*<tc_pat>*)
  let tc_pat (allow_implicits:bool) (pat_t:typ) p0 :
        pat                                (* the type-checked, fully decorated pattern                             *)
      * list<bv>                           (* all its bound variables, used for closing the type of the branch term *)
      * Env.env                            (* the environment extended with all the binders                         *)
      * list<term>                         (* terms corresponding to each clause in the disjunctive pat             *)
      * list<term>                         (* the same terms in normal form                                         *)
      =
    let pat_bvs, exps, p = TcUtil.pat_as_exps allow_implicits env p0 in //an expression for each clause in a disjunctive pattern
    if Env.debug env Options.High
    then Util.print2 "Pattern %s elaborated to %s\n" (Print.pat_to_string p0) (Print.pat_to_string p);
    let pat_env = List.fold_left Env.push_bv env pat_bvs in
    let env1, _ = Env.clear_expected_typ pat_env in
    let env1 = {env1 with Env.is_pattern=true} in  //just a flag for a better error message
    let expected_pat_t = Rel.unrefine env pat_t in
    let exps, norm_exps = exps |> List.map (fun e ->
        if Env.debug env Options.High
        then Util.print2 "Checking pattern expression %s against expected type %s\n" (Print.term_to_string e) (Print.term_to_string pat_t);

        let e, lc, g =  tc_term env1 e in //only keep the unification/subtyping constraints; discard the logical guard for patterns
                                          //Q: where is it being discarded? A: we only use lc.res_typ below, and forget abouts its WP
        if Env.debug env Options.High
        then Util.print2 "Pre-checked pattern expression %s at type %s\n" (N.term_to_string env e) (N.term_to_string env lc.res_typ);

        let g' = Rel.teq env lc.res_typ expected_pat_t in
        let g = Rel.conj_guard g g' in
        let _ = Rel.discharge_guard env ({g with guard_f=Trivial}) |> Rel.resolve_implicits in
        let e' = N.normalize [N.Beta] env e in
        let uvars_to_string uvs = uvs |> Util.set_elements |> List.map (fun (u, _) -> Print.uvar_to_string u) |> String.concat ", " in
        let uvs1 = Free.uvars e' in
        let uvs2 = Free.uvars expected_pat_t in
        if not <| Util.set_is_subset_of uvs1 uvs2
        then (let unresolved = Util.set_difference uvs1 uvs2 |> Util.set_elements in
              raise (Error(Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;\
                                         Variables {%s} were unresolved; please bind them explicitly"
                                    (N.term_to_string env e')
                                    (N.term_to_string env expected_pat_t)
                                    (unresolved |> List.map (fun (u, _) -> Print.uvar_to_string u) |> String.concat ", "), p.p)));

        if Env.debug env Options.High
        then Util.print1 "Done checking pattern expression %s\n" (N.term_to_string env e);

        //explicitly return e here, not its normal form, since pattern decoration relies on it
        e,e') |> List.unzip in
    let p = TcUtil.decorate_pattern env p exps in
    p, pat_bvs, pat_env, exps, norm_exps in
  (*</tc_pat>*)

  let pat_t = scrutinee.sort in
  let scrutinee_tm = S.bv_to_name scrutinee in
  let scrutinee_env, _ = Env.push_bv env scrutinee |> Env.clear_expected_typ in

  (* 1. Check the pattern *)
  let pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps = tc_pat true pat_t pattern in //disj_exps, an exp for each arm of a disjunctive pattern

  (* 2. Check the when clause *)
  let when_clause, g_when = match when_clause with
    | None -> None, Rel.trivial_guard
    | Some e ->
        if Options.should_verify (env.curmodule.str)
        then raise (Error("When clauses are not yet supported in --verify mode; they will be some day", e.pos))
        //             let e, c, g = no_logical_guard pat_env <| tc_total_exp (Env.set_expected_typ pat_env TcUtil.t_bool) e in
        //             Some e, g
        else let e, c, g = tc_term (Env.set_expected_typ pat_env Common.t_bool) e in
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

    let c, g_branch = Util.strengthen_precondition None env branch_exp c g_branch in
    //g_branch is trivial, its logical content is now incorporated within c

    (* (b) *)
    let c_weak, g_when_weak =
     match eqs, when_condition with
      | None, None ->
        c, g_when

      | Some f, None ->
        let gf = NonTrivial f in
        let g = Rel.guard_of_guard_formula gf in
        TcUtil.weaken_precondition env c gf,
        Rel.imp_guard g g_when

      | Some f, Some w ->
        let g_f = NonTrivial f in
        let g_fw = NonTrivial (Util.mk_conj f w) in
        TcUtil.weaken_precondition env c g_fw,
        Rel.imp_guard (Rel.guard_of_guard_formula g_f) g_when

      | None, Some w ->
        let g_w = NonTrivial w in
        let g = Rel.guard_of_guard_formula g_w in
        TcUtil.weaken_precondition env c g_w,
        g_when in

    (* (c) *)
    let binders = List.map S.mk_binder pat_bvs in
    TcUtil.close_comp env pat_bvs c_weak,
    Rel.close_guard binders g_when_weak,
    g_branch in

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
      let rec build_branch_guard scrutinee_tm pat_exp : list<typ> =
        let discriminate scrutinee_tm f =
            if List.length (Env.datacons_of_typ env (Env.typ_of_datacon env f.v)) > 1
            then
                let disc = S.fvar (Util.mk_discriminator f.v) Delta_equational None in
                let disc = mk_Tm_app disc [as_arg scrutinee_tm] None scrutinee_tm.pos in
                [Util.mk_eq Util.t_bool Util.t_bool disc Const.exp_true_bool]
            else [] in

        let fail () =
            failwith (Util.format3 "tc_eqn: Impossible (%s) %s (%s)"
                                        (Range.string_of_range pat_exp.pos)
                                        (Print.term_to_string pat_exp)
                                        (Print.tag_of_term pat_exp))  in

        let rec head_constructor t = match t.n with
            | Tm_fvar fv -> fv.fv_name
            | Tm_uinst(t, _) -> head_constructor t
            | _ -> fail () in

        let pat_exp = SS.compress pat_exp |> Util.unmeta in
        match pat_exp.n with
            | Tm_uvar _
            | Tm_app({n=Tm_uvar _}, _)
            | Tm_name _
            | Tm_constant Const_unit -> []
            | Tm_constant _ -> [mk_Tm_app Util.teq [as_arg scrutinee_tm; as_arg pat_exp] None scrutinee_tm.pos]
            | Tm_uinst _
            | Tm_fvar _ ->
              let f = head_constructor pat_exp in
              if not (Env.is_datacon env f.v)
              then [] //A non-pattern sub-term, typically a type constructor unified via a dot-pattern
              else discriminate scrutinee_tm (head_constructor pat_exp)
            | Tm_app(head, args) ->
                let f = head_constructor head in
                if not (Env.is_datacon env f.v) //A non-pattern sub-term of pat_exp
                then []
                else let sub_term_guards = args |> List.mapi (fun i (ei, _) ->
                        let projector = Env.lookup_projector env f.v i in //NS: TODO ... should this be a marked as a record projector? But it doesn't matter for extraction
                        match Env.try_lookup_lid env projector with
                         | None -> []
                         | _ ->
                            let sub_term = mk_Tm_app (S.fvar (Ident.set_lid_range projector f.p) Delta_equational None) [as_arg scrutinee_tm] None f.p in
                            build_branch_guard sub_term ei) |> List.flatten in
                     discriminate scrutinee_tm f @ sub_term_guards
            | _ -> [] in //a non-pattern sub-term: must be from a dot pattern

      (* 6 (b) *)
      let build_and_check_branch_guard scrutinee_tm pat =
         if not (Options.should_verify env.curmodule.str)
         then TcUtil.fvar_const env Const.true_lid //if we're not verifying, then don't even bother building it
         else let t = Util.mk_conj_l <| build_branch_guard scrutinee_tm pat in
              let k, _ = U.type_u() in
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
  then Util.print1 "Carrying guard from match: %s\n" <| guard_to_string env guard;

  SS.close_branch (pattern, when_clause, branch_exp),
  branch_guard, //expressed in terms of discriminators and projectors on scrutinee---does not contain the pattern-bound variables
  c, //closed already---does not contain free pattern-bound variables
  guard

(******************************************************************************)
(* Checking a top-level, non-recursive let-binding:                           *)
(* top-level let's may be generalized, if they are not annotated              *)
(* the body of a top-level let is always ()---no point in checking it         *)
(******************************************************************************)
and check_top_level_let env e =
   let env = instantiate_both env in
   match e.n with
      | Tm_let((false, [lb]), e2) ->
(*open*) let e1, univ_vars, c1, g1, annotated = check_let_bound_def true env lb in
         (* Maybe generalize its type *)
         let g1, e1, univ_vars, c1 =
            if annotated && not env.generalize
            then g1, e1, univ_vars, c1
            else let g1 = Rel.solve_deferred_constraints env g1 |> Rel.resolve_implicits in
                 let _, univs, e1, c1 = List.hd (TcUtil.generalize env [lb.lbname, e1, c1.comp()]) in
                 g1, e1, univs, Util.lcomp_of_comp c1 in

         (* Check that it doesn't have a top-level effect; warn if it does *)
         let e2, c1 =
            if Options.should_verify env.curmodule.str
            then let ok, c1 = TcUtil.check_top_level env g1 c1 in //check that it has no effect and a trivial pre-condition
                 if ok
                 then e2, c1
                 else (if !Options.warn_top_level_effects //otherwise warn
                       then Errors.warn (Env.get_range env) Errors.top_level_effect;
                       mk (Tm_meta(e2, Meta_desugared Masked_effect)) None e2.pos, c1) //and tag it as masking an effect
            else //even if we're not verifying, still need to solve remaining unification/subtyping constraints
                 (Rel.force_trivial_guard env g1;
                  e2, c1.comp()) in


         (* the result always has type ML unit *)
         let cres = U.lcomp_of_comp <| Util.ml_comp Common.t_unit e.pos in
         e2.tk := Some (Common.t_unit.n);

(*close*)let lb = Util.close_univs_and_mk_letbinding None lb.lbname univ_vars (Util.comp_result c1) (Util.comp_effect_name c1) e1 in
         mk (Tm_let((false, [lb]), e2))
           (Some (Common.t_unit.n))
           e.pos,
         cres,
         Rel.trivial_guard

       | _ -> failwith "Impossible"

(******************************************************************************)
(* Checking an inner non-recursive let-binding:                               *)
(* inner let's are never implicitly generalized                               *)
(* let x = e1 in e2  is logically a bind (lift c1) (\x. lift c2)              *)
(*    except that we also need to strengthen it with well-formedness checks   *)
(*    and a check that x does not escape its scope in the type of c2          *)
(******************************************************************************)
and check_inner_let env e =
   let env = instantiate_both env in
   match e.n with
     | Tm_let((false, [lb]), e2) ->
       let env = {env with top_level=false} in
       let e1, _, c1, g1, annotated = check_let_bound_def false (Env.clear_expected_typ env |> fst) lb in
       let x = {Util.left lb.lbname with sort=c1.res_typ} in
       let lb = Util.mk_letbinding (Inl x) [] c1.res_typ c1.eff_name e1 in
       let xb, e2 = SS.open_term [S.mk_binder x] e2 in
       let xbinder = List.hd xb in
       let x = fst xbinder in
       let e2, c2, g2 = tc_term (Env.push_bv env x) e2 in
       let cres = TcUtil.bind env (Some e1) c1 (Some x, c2) in
       let e = mk (Tm_let((false, [lb]), SS.close xb e2)) (Some cres.res_typ.n) e.pos in
       let x_eq_e1 = NonTrivial <| Util.mk_eq c1.res_typ c1.res_typ (S.bv_to_name x) e1 in
       let g2 = Rel.close_guard xb
                      (Rel.imp_guard (Rel.guard_of_guard_formula x_eq_e1) g2) in
       let guard = Rel.conj_guard g1 g2 in
       if annotated
       then e, cres, guard
       else (* no expected type; check that x doesn't escape it's scope *)
            (check_no_escape None env [x] cres.res_typ;
             e, cres, guard)

    | _ -> failwith "Impossible"

(******************************************************************************)
(* top-level let rec's may be generalized, if they are not annotated          *)
(******************************************************************************)
and check_top_level_let_rec env top =
    let env = instantiate_both env in
    match top.n with
        | Tm_let((true, lbs), e2) ->
(*open*)   let lbs, e2 = SS.open_let_rec lbs e2 in

           let env0, topt = Env.clear_expected_typ env in
           let lbs, rec_env = build_let_rec_env true env0 lbs in
           let lbs, g_lbs = check_let_recs rec_env lbs in
           let g_lbs = Rel.solve_deferred_constraints env g_lbs |> Rel.resolve_implicits in

           let all_lb_names = lbs |> List.map (fun lb -> right lb.lbname) |> Some in

           let lbs =
              if not env.generalize
              then lbs |> List.map (fun lb ->
                    if lb.lbunivs = []
                    then lb
                    else Util.close_univs_and_mk_letbinding all_lb_names lb.lbname lb.lbunivs lb.lbtyp lb.lbeff lb.lbdef)
              else let ecs = TcUtil.generalize env (lbs |> List.map (fun lb ->
                                lb.lbname,
                                lb.lbdef,
                                S.mk_Total lb.lbtyp)) in
                   ecs |> List.map (fun (x, uvs, e, c) ->
                      Util.close_univs_and_mk_letbinding all_lb_names x uvs (Util.comp_result c) (Util.comp_effect_name c) e) in

          let cres = U.lcomp_of_comp <| S.mk_Total Common.t_unit in
          let _ = e2.tk := Some Common.t_unit.n in

(*close*) let lbs, e2 = SS.close_let_rec lbs e2 in
          mk (Tm_let((true, lbs), e2)) (Some Common.t_unit.n) top.pos,
          cres,
          Rel.discharge_guard env g_lbs

        | _ -> failwith "Impossible"

(******************************************************************************)
(* inner let rec's are never implicitly generalized *)
(******************************************************************************)
and check_inner_let_rec env top =
    let env = instantiate_both env in
    match top.n with
        | Tm_let((true, lbs), e2) ->
(*open*)  let lbs, e2 = SS.open_let_rec lbs e2 in

          let env0, topt = Env.clear_expected_typ env in
          let lbs, rec_env = build_let_rec_env false env0 lbs in
          let lbs, g_lbs = check_let_recs rec_env lbs in

          let env, lbs = lbs |> Util.fold_map (fun env lb ->
            let x = {left lb.lbname with sort=lb.lbtyp} in
            let lb = {lb with lbname=Inl x} in
            let env = Env.push_let_binding env lb.lbname ([], lb.lbtyp) in //local let recs are not universe polymorphic
            env, lb) env in

          let bvs = lbs |> List.map (fun lb -> left (lb.lbname)) in

          let e2, cres, g2 = tc_term env e2 in
          let guard = Rel.conj_guard g_lbs g2 in
          let cres = TcUtil.close_comp env bvs cres in
          let tres = norm env cres.res_typ in
          let cres = {cres with res_typ=tres} in

(*close*) let lbs, e2 = SS.close_let_rec lbs e2 in
          let e = mk (Tm_let((true, lbs), e2)) (Some tres.n) top.pos in

          begin match topt with
              | Some _ -> e, cres, guard //we have an annotation
              | None -> check_no_escape None env bvs tres;
                        e, cres, guard
          end

        | _ -> failwith "Impossible"

(******************************************************************************)
(* build an environment with recursively bound names.                         *)
(* refining the types of those names with decreases clauses is done in tc_abs *)
(******************************************************************************)
and build_let_rec_env top_level env lbs : list<letbinding> * env_t =
   let env0 = env in
   let lbs, env = List.fold_left (fun (lbs, env) lb -> //{lbname=x; lbtyp=t; lbdef=e}) ->
        let univ_vars, t, check_t = TcUtil.extract_let_rec_annotation env lb in
        let env = Env.push_univ_vars env univ_vars in //no polymorphic recursion on universes
        let e = Util.unascribe lb.lbdef in
        let t =
            if not check_t
            then t
            else if top_level && not(env.generalize) //t is from an already-checked val decl
            then t
            else (let t, _, g = tc_check_tot_or_gtot_term ({env0 with check_uvars=true}) t (fst <| U.type_u()) in
                  Rel.force_trivial_guard env0 g;
                  norm env0 t) in
        let env = if Util.is_pure_or_ghost_function t //termination check is enabled
                  && Options.should_verify env.curmodule.str (* store the let rec names separately for termination checks *)
                  then {env with letrecs=(lb.lbname,t)::env.letrecs}
                  else Env.push_let_binding env lb.lbname ([], t) in //no polymorphic recursion on universes
       let lb = {lb with lbtyp=t; lbunivs=univ_vars; lbdef=e} in
       lb::lbs,  env)
    ([],env)
    lbs  in
  List.rev lbs, env

and check_let_recs env lbs =
    let lbs, gs = lbs |> List.map (fun lb ->
        let e, c, g = tc_tot_or_gtot_term (Env.set_expected_typ env lb.lbtyp) lb.lbdef in
        if not (Util.is_total_lcomp c)
        then raise (Error ("Expected let rec to be a Tot term; got effect GTot", e.pos));
        let lb = Util.mk_letbinding lb.lbname lb.lbunivs lb.lbtyp Const.effect_Tot_lid e in
        lb, g) |> List.unzip in
    let g_lbs = List.fold_right Rel.conj_guard gs Rel.trivial_guard in
    lbs, g_lbs


(******************************************************************************)
(* Several utility functions follow                                           *)
(******************************************************************************)
and check_let_bound_def top_level env lb
                               : term       (* checked lbdef                   *)
                               * univ_names (* univ_vars, if any               *)
                               * lcomp      (* type of lbdef                   *)
                               * guard_t    (* well-formedness of lbtyp        *)
                               * bool       (* true iff lbtyp was annotated    *)
                               =
    let env1, _ = Env.clear_expected_typ env in
    let e1 = lb.lbdef in

    (* 1. extract the annotation of the let-bound term, e1, if any *)
    let topt, wf_annot, univ_vars, env1 = check_lbtyp top_level env lb in

    if not top_level && univ_vars <> []
    then raise (Error("Inner let-bound definitions cannot be universe polymorphic", e1.pos));

    (* 2. type-check e1 *)
    let e1, c1, g1 = tc_maybe_toplevel_term ({env1 with top_level=top_level}) e1 in

    (* and strengthen its VC with and well-formedness condition on its annotated type *)
    let c1, guard_f = TcUtil.strengthen_precondition
                        (Some (fun () -> Errors.ill_kinded_type))
                        (Env.set_range env1 e1.pos) e1 c1 wf_annot in
    let g1 = Rel.conj_guard g1 guard_f in

    if Env.debug env Options.Extreme
    then Util.print1 "checked top-level def, guard is %s\n" (Rel.guard_to_string env g1);

    e1, univ_vars, c1, g1, Option.isSome topt


(* Extracting the type of non-recursive let binding *)
and check_lbtyp top_level env lb : option<typ>  (* checked version of lb.lbtyp, if it was not Tm_unknown *)
                                 * guard_t      (* well-formedness condition for that type               *)
                                 * univ_names   (* explicit universe variables, if any                   *)
                                 * Env.env      (* env extended with univ_vars                           *)
                                 =
    let t = SS.compress lb.lbtyp in
    match t.n with
        | Tm_unknown ->
          if lb.lbunivs <> [] then failwith "Impossible: non-empty universe variables but the type is unknown";
          None, Rel.trivial_guard, [], env

        | _ ->
          let univ_vars, t = open_univ_vars lb.lbunivs t in
          let env1 = Env.push_univ_vars env univ_vars in
          if top_level
          && not (env.generalize) //clearly, x has an annotated type ... could env.generalize ever be true here?
                                  //yes. x may not have a val declaration, only an inline annotation
                                  //so, not (env.generalize) signals that x has been declared as val x : t, and t has already been checked
          then Some t, Rel.trivial_guard, univ_vars, Env.set_expected_typ env1 t //t has already been kind-checked
          else //we have an inline annotation
               let k, _ = U.type_u () in
               let t, _, g = tc_check_tot_or_gtot_term env1 t k in
               if debug env Options.Medium
               then Util.print2 "(%s) Checked type annotation %s\n"
                        (Range.string_of_range (range_of_lbname lb.lbname))
                        (Print.term_to_string t);
               let t = norm env1 t in
               Some t, g, univ_vars, Env.set_expected_typ env1 t


and tc_binder env (x, imp) =
    let tu, u = U.type_u () in
    let t, _, g = tc_check_tot_or_gtot_term env x.sort tu in //ghost effect ok in the types of binders
    let x = {x with sort=t}, imp in
    if Env.debug env Options.High
    then Util.print2 "Pushing binder %s at type %s\n" (Print.bv_to_string (fst x)) (Print.term_to_string t);
    x, maybe_push_binding env x, g, u

and tc_binders env bs =
    let rec aux env bs = match bs with
        | [] -> [], env, Rel.trivial_guard, []
        | b::bs ->
          let b, env', g, u = tc_binder env b in
          let bs, env', g', us = aux env' bs in
          b::bs, env', Rel.conj_guard g (Rel.close_guard [b] g'), u::us in
    aux env bs

and tc_pats env pats =
    let tc_args env args : Syntax.args * guard_t =
       //an optimization for checking arguments in cases where we know that their types match the types of the corresponding formal parameters
       //notably, this is used when checking the application  (?u x1 ... xn). NS: which we do not currently do!
       List.fold_right (fun (t, imp) (args, g) ->
                             let t, _, g' = tc_term env t in
                             (t, imp)::args, Rel.conj_guard g g')
          args ([], Rel.trivial_guard) in
    List.fold_right (fun p (pats, g) -> let args, g' = tc_args env p in (args::pats, Rel.conj_guard g g')) pats ([], Rel.trivial_guard)

and tc_tot_or_gtot_term env e : term
                                * lcomp
                                * guard_t =
  let e, c, g = tc_maybe_toplevel_term env e in
  if Util.is_tot_or_gtot_lcomp c
  then e, c, g
  else let g = Rel.solve_deferred_constraints env g in
       let c = c.comp() in
       let _ = if Env.debug env Options.High then Util.print1 "About to normalize %s\n" (Print.comp_to_string c) in
       let c = norm_c env c in
       let target_comp, allow_ghost =
            if TcUtil.is_pure_effect env (Util.comp_effect_name c)
            then S.mk_Total (Util.comp_result c), false
            else S.mk_GTotal (Util.comp_result c), true in
       match Rel.sub_comp env c target_comp with
        | Some g' -> e, Util.lcomp_of_comp target_comp, Rel.conj_guard g g'
        | _ ->
            if allow_ghost
            then raise (Error(Errors.expected_ghost_expression e c, e.pos))
            else raise (Error(Errors.expected_pure_expression e c, e.pos))

and tc_check_tot_or_gtot_term env e t : term
                                      * lcomp
                                      * guard_t =
    let env = Env.set_expected_typ env t in
    tc_tot_or_gtot_term env e

(*****************Type-checking the signature of a module*****************************)
let tc_trivial_guard env t =
  let t, c, g = tc_tot_or_gtot_term env t in
  Rel.force_trivial_guard env g;
  t,c

let tc_check_trivial_guard env t k =
  let t, c, g = tc_check_tot_or_gtot_term env t k in
  Rel.force_trivial_guard env g;
  t

let check_and_gen env t k =
    (* Util.print1 "Checking against expected type %s\n" (Print.term_to_string *)
    (*   (N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env k)); *)
    TcUtil.generalize_universes env (tc_check_trivial_guard env t k)

let check_nogen env t k =
    let t = tc_check_trivial_guard env t k in
    [], N.normalize [N.Beta] env t

let tc_tparams env (tps:binders) : (binders * Env.env * universes) =
    let tps, env, g, us = tc_binders env tps in
    Rel.force_trivial_guard env g;
    tps, env, us

let monad_signature env m s =
 let fail () = raise (Error(Errors.unexpected_signature_for_monad env m s, range_of_lid m)) in
 let s = SS.compress s in
 match s.n with
  | Tm_arrow(bs, c) ->
    let bs = SS.open_binders bs in
    begin match bs with
        | [(a, _);(wp, _); (_wlp, _)] -> a, wp.sort
        | _ -> fail()
    end
  | _ -> fail()

let open_univ_vars uvs binders c =
    match binders with
        | [] ->
          let uvs, c = SS.open_univ_vars_comp uvs c in
          uvs, [], c
        | _ ->
          let t' = Util.arrow binders c in
          let uvs, t' = SS.open_univ_vars uvs t' in
          match (SS.compress t').n with
            | Tm_arrow(binders, c) -> uvs, binders, c
            | _ -> failwith "Impossible"

let open_effect_signature env mname signature =
   let fail t = raise (Error(Errors.unexpected_signature_for_monad env mname t, range_of_lid mname)) in
   match (SS.compress signature).n with
      | Tm_arrow(bs, c) ->
        let bs = SS.open_binders bs in
        begin match bs with
            | [(a, _);(wp, _); (_wlp, _)] -> a, wp.sort
            | _ -> fail signature
        end
      | _ -> fail signature

let open_effect_decl env ed =
   let a, wp = open_effect_signature env ed.mname ed.signature in
   let ed =
    match ed.binders with
      | [] -> ed
      | _ ->
       let opening = SS.opening_of_binders ed.binders in
       let op ts =
            assert (fst ts = []);
            let t0 = snd ts in
            let t1 = SS.subst opening (snd ts) in
            ([], t1) in
         { ed with
               ret         =op ed.ret
             ; bind_wp     =op ed.bind_wp
             ; bind_wlp    =op ed.bind_wlp
             ; if_then_else=op ed.if_then_else
             ; ite_wp      =op ed.ite_wp
             ; ite_wlp     =op ed.ite_wlp
             ; wp_binop    =op ed.wp_binop
             ; wp_as_type  =op ed.wp_as_type
             ; close_wp    =op ed.close_wp
             ; assert_p    =op ed.assert_p
             ; assume_p    =op ed.assume_p
             ; null_wp     =op ed.null_wp
             ; trivial     =op ed.trivial } in
   ed, a, wp

let gen_wps_for_free env binders a wp_a (ed: Syntax.eff_decl): Syntax.eff_decl =
  (* A series of macros and combinators to automatically build WP's. In these
   * definitions, both [binders] and [a] are opened. This means that macros
   * close over [binders] and [a], and this means that combinators do not expect
   * [binders] and [a] when applied. *)
  let normalize = N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env in

  let d s = Util.print1 "\x1b[01;36m%s\x1b[00m\n" s in
  let normalize_and_make_binders_explicit tm =
    let tm = normalize tm in
    let rec visit_term tm =
      let n = match (SS.compress tm).n with
        | Tm_arrow (binders, comp) ->
            let comp = visit_comp comp in
            let binders = List.map visit_binder binders in
            Tm_arrow (binders, comp)
        | Tm_abs (binders, term, comp) ->
            let comp = visit_maybe_lcomp comp in
            let term = visit_term term in
            let binders = List.map visit_binder binders in
            Tm_abs (binders, term, comp)
        | _ ->
            tm.n
      in
      { tm with n = n }
    and visit_binder (bv, a) =
      { bv with sort = visit_term bv.sort }, S.as_implicit false
    and visit_maybe_lcomp lcomp =
      match lcomp with
      | Some (Inl lcomp) ->
          Some (Inl (U.lcomp_of_comp (visit_comp (lcomp.comp ()))))
      | comp ->
          comp
    and visit_comp comp =
      let n = match comp.n with
        | Total tm ->
            Total (visit_term tm)
        | GTotal tm ->
            GTotal (visit_term tm)
        | comp ->
            comp
      in
      { comp with n = n }
    and visit_args args =
      List.map (fun (tm, q) -> visit_term tm, q) args
    in
    visit_term tm
  in

  (* A debug / sanity check. *)
  let check str t =
    if Env.debug env (Options.Other "ED") then begin
      Util.print2 "Generated term for %s: %s\n" str (Print.term_to_string t);
      let t = normalize t in
      let t = SS.compress t in
      let e, { res_typ = res_typ }, _ = tc_term env t in
      Util.print2 "Inferred type for %s: %s\n" str (Print.term_to_string (normalize res_typ));
      Util.print2 "Elaborated term for %s: %s\n" str (Print.term_to_string (normalize e))
    end
  in

  (* Consider the predicate transformer st_wp:
   *   let st_pre_h  (heap:Type)          = heap -> GTot Type0
   *   let st_post_h (heap:Type) (a:Type) = a -> heap -> GTot Type0
   *   let st_wp_h   (heap:Type) (a:Type) = st_post_h heap a -> Tot (st_pre_h heap)
   * after reduction we get:
   *   let st_wp_h (heap: Type) (a: Type) = (a -> heap -> GTot Type0) -> heap -> GTot Type0
   * we want:
   *   type st2_gctx (heap: Type) (a:Type) (t:Type) = (a -> heap -> GTot Type0) -> heap -> GTot t
   * we thus generate macros parameterized over [e] that build the right
   * context. [gamma] is the series of binders the precede the return type of
   * the context. *)
  let rec collect_binders (t : term) =
    match (compress t).n with
    | Tm_arrow (bs, comp) ->
        let rest = match comp.n with
                   | Total t -> t
                   | _ -> failwith "wp_a contains non-Tot arrow" in
        bs @ (collect_binders rest)
    | Tm_type _ ->
        []
    | _ ->
        failwith "wp_a doesn't end in Type0" in

  let mk_ctx, mk_gctx, mk_gamma =
    let i = ref 0 in
    let wp_binders = collect_binders (normalize wp_a) in
    (fun t -> U.arrow wp_binders (mk_Total t)),
    (fun t -> U.arrow wp_binders (mk_GTotal t)),
    (fun () -> List.map (fun (bv, _) ->
          (* Note: just returning [wp_binders] here would be wrong, because the
           * identity of binders relies on the _physical equality_ of the [bv]
           * data structure. So, arguments passed to [mk_ctx] should never refer
           * to [wp_binders]; one way to enforce that is to generate fresh
           * binders whenever the client asks for it. *)
          i := !i + 1;
          S.gen_bv ("g" ^ string_of_int !i) None bv.sort
        ) wp_binders)
  in

  (* A variation where we can specify implicit parameters. *)
  let binders_of_list = List.map (fun (t, b) -> t, S.as_implicit b) in

  let implicit_binders_of_list = List.map (fun t -> t, S.as_implicit true) in

  let args_of_bv = List.map (fun bv -> S.as_arg (S.bv_to_name bv)) in

  (* val st2_pure : #heap:Type -> #a:Type -> #t:Type -> x:t ->
       Tot (st2_ctx heap a t)
     let st2_pure #heap #a #t x = fun _post _h -> x *)
  let c_pure =
    let t = S.gen_bv "t" None U.ktype in
    let x = S.gen_bv "x" None (S.bv_to_name t) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_ctx (S.bv_to_name t))))) in
    let gamma = mk_gamma () in
    let body = U.abs (implicit_binders_of_list gamma) (S.bv_to_name x) ret in
    U.abs (binders_of_list [ t, true; x, false ]) body ret
  in
  check "pure" (U.abs (binders @ [ S.mk_binder a ]) c_pure None);

  (* val st2_app : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                  l:st2_gctx heap a (t1 -> GTot t2) ->
                  r:st2_gctx heap a t1 ->
                  Tot (st2_gctx heap a t2)
    let st2_app #heap #a #t1 #t2 l r = fun p h -> l p h (r p h) *)
  let c_app =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let l = S.gen_bv "l" None (mk_gctx
      (U.arrow [ S.mk_binder (S.new_bv None (S.bv_to_name t1)) ] (S.mk_GTotal (S.bv_to_name t2))))
    in
    let r = S.gen_bv "r" None (mk_gctx (S.bv_to_name t1)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t2))))) in
    let outer_body =
      let gamma = mk_gamma () in
      let gamma_as_args = args_of_bv gamma in
      let inner_body =
        U.mk_app
          (S.bv_to_name l)
          (gamma_as_args @ [ S.as_arg (U.mk_app (S.bv_to_name r) gamma_as_args)])
      in
      U.abs (implicit_binders_of_list gamma) inner_body ret
    in
    U.abs (binders_of_list [ t1, true; t2, true; l, false; r, false ]) outer_body ret
  in
  check "app" (U.abs (binders @ [ S.mk_binder a ]) c_app None);

  (* val st2_liftGA1 : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                       f : (t1 -> GTot t2) ->
                       st2_gctx heap a t1 ->
                       Tot (st2_gctx heap a t2)
    let st2_liftGA1 #heap #a #t1 #t2 f a1 =
                    st2_app (st2_pure f) a1
  *)
  let unknown = mk Tm_unknown None Range.dummyRange in
  let c_lift1 =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t_f = U.arrow [ S.null_binder (S.bv_to_name t1) ] (S.mk_GTotal (S.bv_to_name t2)) in
    let f = S.gen_bv "f" None t_f in
    let a1 = S.gen_bv "a1" None (mk_gctx (S.bv_to_name t1)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t2))))) in
    U.abs (binders_of_list [ t1, true; t2, true; f, false; a1, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [ unknown; S.bv_to_name f ]);
        S.bv_to_name a1 ])
    ) ret
  in
  check "lift1" (U.abs (binders @ [ S.mk_binder a ]) c_lift1 None);


  (* val st2_liftGA2 : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type -> #t3:Type ->
                       f : (t1 -> t2 -> GTot t3) ->
                       a1: st2_gctx heap a t1 ->
                       a2: st2_gctx heap a t2 ->
                       Tot (st2_gctx heap a t3)
    let st2_liftGA2 #heap #a #t1 #t2 #t3 f a1 a2 =
      st2_app (st2_app (st2_pure f) a1) a2
  *)
  let c_lift2 =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t3 = S.gen_bv "t3" None U.ktype in
    let t_f = U.arrow
      [ S.null_binder (S.bv_to_name t1); S.null_binder (S.bv_to_name t2) ]
      (S.mk_GTotal (S.bv_to_name t3))
    in
    let f = S.gen_bv "f" None t_f in
    let a1 = S.gen_bv "a1" None (mk_gctx (S.bv_to_name t1)) in
    let a2 = S.gen_bv "a2" None (mk_gctx (S.bv_to_name t2)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t3))))) in
    U.abs (binders_of_list [ t1, true; t2, true; t3, true; f, false; a1, false; a2, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_app (List.map S.as_arg [
          unknown; unknown;
          U.mk_app c_pure (List.map S.as_arg [ unknown; S.bv_to_name f ]);
          S.bv_to_name a1 ]);
        S.bv_to_name a2 ])
    ) ret
  in
  check "lift2" (U.abs (binders @ [ S.mk_binder a ]) c_lift2 None);

  (* val st2_push : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                    f:(t1 -> Tot (st2_gctx heap a t2)) ->
                    Tot (st2_ctx heap a (t1->GTot t2))
    let st2_push #heap #a #t1 #t2 f = fun p h e1 -> f e1 p h *)
  let c_push =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t_f = U.arrow
      [ S.null_binder (S.bv_to_name t1) ]
      (S.mk_Total (mk_gctx (S.bv_to_name t2)))
    in
    let f = S.gen_bv "f" None t_f in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_ctx (
      U.arrow [ S.null_binder (S.bv_to_name t1) ] (S.mk_GTotal (S.bv_to_name t2)))))))
    in
    let e1 = S.gen_bv "e1" None (S.bv_to_name t1) in
    let gamma = mk_gamma () in
    let body = U.abs (S.binders_of_list gamma @ [ S.mk_binder e1 ]) (
      U.mk_app (S.bv_to_name f) (S.as_arg (S.bv_to_name e1) :: args_of_bv gamma)
    ) ret in
    U.abs (binders_of_list [ t1, true; t2, true; f, false ]) body ret
  in
  check "push" (U.abs (binders @ [ S.mk_binder a ]) c_push None);

  let ret_tot_wp_a = Some (Inl (U.lcomp_of_comp (mk_Total wp_a))) in

  (* val st2_if_then_else : heap:Type -> a:Type -> c:Type0 ->
                            st2_wp heap a -> st2_wp heap a ->
                            Tot (st2_wp heap a)
    let st2_if_then_else heap a c = st2_liftGA2 (l_ITE c) *)
  let wp_if_then_else =
    let c = S.gen_bv "c" None U.ktype in
    (* Note that this one *does* abstract over [a]. This is in line with the
     * expected shape of the combinator in the effect declaration. (But it does
     * not abstract over [binders]; [tc_eff_decl] will take care of closing
     * [binders]. *)
    U.abs (S.binders_of_list [ a; c ]) (
      let l_ite = fvar Const.ite_lid (S.Delta_unfoldable 2) None in
      U.mk_app c_lift2 (List.map S.as_arg [
        unknown; unknown; unknown;
        U.mk_app l_ite [S.as_arg (S.bv_to_name c)]
      ])
    ) ret_tot_wp_a
  in
  let wp_if_then_else = normalize_and_make_binders_explicit wp_if_then_else in
  check "wp_if_then_else" (U.abs binders wp_if_then_else None);

  (* val st2_wp_binop : heap:Type -> a:Type -> st2_wp heap a -> op:(Type0->Type0->GTot Type0) ->
                          st2_wp heap a ->
                          Tot (st2_wp heap a)
     let st2_wp_binop heap a l op r = st2_liftGA2 op l r *)
  let wp_binop =
    let l = S.gen_bv "l" None wp_a in
    let op = S.gen_bv "op" None (U.arrow
      [ S.null_binder U.ktype0; S.null_binder U.ktype0 ]
      (S.mk_GTotal U.ktype0)) in
    let r = S.gen_bv "r" None wp_a in
    U.abs
      (S.binders_of_list [ a; l; op; r ])
      (U.mk_app c_lift2 (List.map S.as_arg [
        unknown; unknown; unknown;
        S.bv_to_name op; S.bv_to_name l; S.bv_to_name r ]))
      ret_tot_wp_a
  in
  let wp_binop = normalize_and_make_binders_explicit wp_binop in
  check "wp_binop" (U.abs binders wp_binop None);

  (* val st2_assert_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assert_p heap a q wp = st2_app (st2_pure (l_and q)) wp *)
  let wp_assert =
    let q = S.gen_bv "q" None U.ktype0 in
    let wp = S.gen_bv "wp" None wp_a in
    let l_and = fvar Const.and_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          U.mk_app l_and [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assert = normalize_and_make_binders_explicit wp_assert in
  check "wp_assert" (U.abs binders wp_assert None);

  (* val st2_assume_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assume_p heap a q wp = st2_app (st2_pure (l_imp q)) wp *)
  let wp_assume =
    let q = S.gen_bv "q" None U.ktype0 in
    let wp = S.gen_bv "wp" None wp_a in
    let l_imp = fvar Const.imp_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          U.mk_app l_imp [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assume = normalize_and_make_binders_explicit wp_assume in
  check "wp_assume" (U.abs binders wp_assume None);

  let tforall = U.mk_app (S.mk_Tm_uinst U.tforall [ U_unknown ]) [ S.as_arg unknown ] in

  (* val st2_close_wp : heap:Type -> a:Type -> b:Type ->
                        f:(b->Tot (st2_wp heap a)) ->
                        Tot (st2_wp heap a)
    let st2_close_wp heap a b f = st2_app (st2_pure l_Forall) (st2_push f) *)
  let wp_close =
    let b = S.gen_bv "b" None U.ktype in
    let t_f = U.arrow [ S.null_binder (S.bv_to_name b) ] (S.mk_Total wp_a) in
    let f = S.gen_bv "f" None t_f in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          tforall]);
        U.mk_app c_push (List.map S.as_arg [
          unknown; unknown;
          S.bv_to_name f])])
    in
    U.abs (S.binders_of_list [ a; b; f ]) body ret_tot_wp_a
  in
  let wp_close = normalize_and_make_binders_explicit wp_close in
  check "wp_close" (U.abs binders wp_close None);

  let ret_tot_type0 = Some (Inl (U.lcomp_of_comp <| S.mk_Total U.ktype0)) in
  let mk_forall (x: S.bv) (body: S.term): S.term =
    let tforall = U.mk_app (S.mk_Tm_uinst U.tforall [ U_unknown ]) [ S.as_arg x.sort ] in
    S.mk (Tm_app (tforall, [ S.as_arg (U.abs [ S.mk_binder x ] body ret_tot_type0)])) None Range.dummyRange
  in

  (* For each (target) type t, we define a binary relation in t called ≤_t.

      x ≤_t y            =def=       x = y      [t is base type]
      x ≤_Type0 y        =def=       x ==> y
      x ≤_{a->b} y       =def=   ∀a1 a2, a1 ≤_a a2 ==> x a1 ≤_b y a2
  *)
  (* Invariant: [x] and [y] have type [t] *)
  let rec mk_leq t x y =
    match (normalize (SS.compress t)).n with
    | Tm_type _ ->
        (* Util.print2 "type0, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        U.mk_imp x y
    | Tm_arrow ([ binder ], { n = GTotal b })
    | Tm_arrow ([ binder ], { n = Total b }) when S.is_null_binder binder ->
        let a = (fst binder).sort in
        (* Util.print2 "arrow, a=%s, b=%s\n" (Print.term_to_string a) (Print.term_to_string b); *)
        let a1 = S.gen_bv "a1" None a in
        let a2 = S.gen_bv "a2" None a in
        let body = U.mk_imp
          (mk_leq a (S.bv_to_name a1) (S.bv_to_name a2))
          (mk_leq b
            (U.mk_app x [ S.as_arg (S.bv_to_name a1) ])
            (U.mk_app y [ S.as_arg (S.bv_to_name a2) ]))
        in
        mk_forall a1 (mk_forall a2 body)
    | Tm_arrow (binder :: binders, comp) ->
        let t = { t with n = Tm_arrow ([ binder ], S.mk_Total (U.arrow binders comp)) } in
        mk_leq t x y
    | Tm_arrow _ ->
        failwith "unhandled arrow"
    | _ ->
        (* TODO: assert that this is a base type. *)
        (* Util.print2 "base, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        U.mk_eq t t x y
  in
  let stronger =
    let wp1 = S.gen_bv "wp1" None wp_a in
    let wp2 = S.gen_bv "wp2" None wp_a in
    let body = mk_leq wp_a (S.bv_to_name wp1) (S.bv_to_name wp2) in
    U.abs (S.binders_of_list [ wp1; wp2 ]) body ret_tot_type0
  in
  check "stronger" (U.abs (binders @ [ S.mk_binder a ]) stronger None);

  let null_wp = snd ed.null_wp in

  (* val st2_trivial : heap:Type ->a:Type -> st2_wp heap a -> Tot Type0
    let st2_trivial heap a wp = st2_stronger heap a (st2_null_wp heap a) wp *)
  let wp_trivial =
    let wp = S.gen_bv "wp" None wp_a in
    let body = U.mk_app stronger (List.map S.as_arg [
      U.mk_app null_wp [ S.as_arg (S.bv_to_name a) ];
      S.bv_to_name wp
    ]) in
    U.abs (S.binders_of_list [ a; wp ]) body ret_tot_type0
  in
  let wp_trivial = normalize_and_make_binders_explicit wp_trivial in
  check "wp_trivial" (U.abs binders wp_trivial None);

  { ed with
    if_then_else = ([], wp_if_then_else);
    wp_binop     = ([], wp_binop);
    assert_p     = ([], wp_assert);
    assume_p     = ([], wp_assume);
    close_wp     = ([], wp_close);
    trivial      = ([], wp_trivial)
  }


let tc_eff_decl env0 (ed:Syntax.eff_decl) is_for_free =
  assert (ed.univs = []); //no explicit universe variables in the source; Q: But what about re-type-checking a program?
  let binders_un, signature_un = SS.open_term ed.binders ed.signature in
  let binders, env, _ = tc_tparams env0 binders_un in
  let signature, _    = tc_trivial_guard env signature_un in
  let ed = {ed with binders=binders;
                    signature=signature} in

  let ed, a, wp_a = open_effect_decl env ed in
  let get_effect_signature ()  =
    let signature, _ = tc_trivial_guard env signature_un in
    open_effect_signature env ed.mname signature in

  //put the signature in the environment to prevent generalizing its free universe variables until we're done
  let env = Env.push_bv env (S.new_bv None ed.signature) in

  if Env.debug env0 <| Options.Other "ED"
  then Util.print3 "Checking effect signature: %s %s : %s\n"
                        (Print.lid_to_string ed.mname)
                        (Print.binders_to_string " " ed.binders)
                        (Print.term_to_string ed.signature);

  let check_and_gen' env (_,t) k =
    check_and_gen env t k in

  (* Override dummy fields with automatically-generated combinators, if needed. *)
  let ed =
    match is_for_free with
    | NotForFree -> ed
    | ForFree -> gen_wps_for_free env binders a wp_a ed in

  let ret =
    let expected_k = Util.arrow [S.mk_binder a; S.null_binder (S.bv_to_name a)] (S.mk_GTotal wp_a) in
    check_and_gen' env ed.ret expected_k in

  let bind_wp =
    let wlp_a = wp_a in
    let b, wp_b = get_effect_signature () in
    let a_wp_b = Util.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_b) in
    let a_wlp_b = a_wp_b in
    let expected_k = Util.arrow [S.mk_binder a; S.mk_binder b;
                                 S.null_binder wp_a;   S.null_binder wlp_a;
                                 S.null_binder a_wp_b; S.null_binder a_wlp_b]
                                 (S.mk_Total wp_b) in
    check_and_gen' env ed.bind_wp expected_k in

  let bind_wlp =
    let wlp_a = wp_a in
    let b, wlp_b = get_effect_signature ()  in
    let a_wlp_b = Util.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wlp_b) in
    let expected_k = Util.arrow [S.mk_binder a; S.mk_binder b;
                                 S.null_binder wlp_a;
                                 S.null_binder a_wlp_b]
                                 (S.mk_Total wlp_b) in
    check_and_gen' env ed.bind_wlp expected_k in

  let if_then_else =
    let p = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let expected_k = Util.arrow [S.mk_binder a; S.mk_binder p;
                                 S.null_binder wp_a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.if_then_else expected_k in

  let ite_wp =
    let wlp_a = wp_a in
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder wlp_a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.ite_wp expected_k in

  let ite_wlp =
    let wlp_a = wp_a in
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder wlp_a]
                                (S.mk_Total wlp_a) in
    check_and_gen' env ed.ite_wlp expected_k in

  let wp_binop =
    let bin_op =
        let t1, u1 = U.type_u() in
        let t2, u2 = U.type_u() in
        let t = mk (Tm_type(S.U_max [u1; u2])) None (Env.get_range env) in
        Util.arrow [S.null_binder t1; S.null_binder t2] (S.mk_GTotal t) in
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder wp_a;
                                 S.null_binder bin_op;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.wp_binop expected_k in

  let wp_as_type =
    let t, _ = U.type_u() in
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder wp_a]
                                (S.mk_Total t) in
    check_and_gen' env ed.wp_as_type expected_k in

  let close_wp =
    let b = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let b_wp_a = Util.arrow [S.null_binder (S.bv_to_name b)] (S.mk_Total wp_a) in
    let expected_k = Util.arrow [S.mk_binder a; S.mk_binder b; S.null_binder b_wp_a]
                                (S.mk_Total wp_a) in
    check_and_gen' env ed.close_wp expected_k in

  let assert_p =
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder (U.type_u() |> fst);
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.assert_p expected_k in

  let assume_p =
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder (U.type_u() |> fst);
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.assume_p expected_k in

  let null_wp =
    let expected_k = Util.arrow [S.mk_binder a]
                                (S.mk_Total wp_a) in
    check_and_gen' env ed.null_wp expected_k in

  let trivial_wp =
    let t, _ = Util.type_u() in
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder wp_a]
                                (S.mk_GTotal t) in
    check_and_gen' env ed.trivial expected_k in

  //generalize and close
  let t = U.arrow ed.binders (S.mk_Total ed.signature) in
  let (univs, t) = TcUtil.generalize_universes env0 t in
  let binders, signature = match binders, (SS.compress t).n with
    | [], _ -> [], t
    | _, Tm_arrow(binders, c) -> binders, Util.comp_result c
    | _ -> failwith "Impossible" in
  let close n ts =
    let ts = SS.close_univ_vars_tscheme univs (SS.close_tscheme binders ts) in
    assert (List.length (fst ts) = n);
    ts in
  let ed = { ed with
      univs       = univs
    ; binders     = binders
    ; signature   = signature
    ; ret         = close 0 ret
    ; bind_wp     = close 1 bind_wp
    ; bind_wlp    = close 1 bind_wlp
    ; if_then_else= close 0 if_then_else
    ; ite_wp      = close 0 ite_wp
    ; ite_wlp     = close 0 ite_wlp
    ; wp_binop    = close 0 wp_binop
    ; wp_as_type  = close 0 wp_as_type
    ; close_wp    = close 1 close_wp
    ; assert_p    = close 0 assert_p
    ; assume_p    = close 0 assume_p
    ; null_wp     = close 0 null_wp
    ; trivial     = close 0 trivial_wp } in

  if Env.debug env Options.Low
  then Util.print_string (Print.eff_decl_to_string ed);
  ed

let tc_lex_t env ses quals lids =
    (* We specifically type lex_t as:

          type lex_t<u> : Type(u) =
          datacon LexTop<utop>  : lex_t<utop>
          datacon LexCons<ucons1, ucons2> : #a:Type(ucons1) -> hd:a -> tl:lex_t<ucons2> -> lex_t<max ucons1 ucons2>
    *)
    assert (quals = []);
    begin match lids with
        | [lex_t; lex_top; lex_cons] when
            (lid_equals lex_t Const.lex_t_lid
             && lid_equals lex_top Const.lextop_lid
             && lid_equals lex_cons Const.lexcons_lid) -> ()
        | _ -> assert false
    end;
    begin match ses with
      | [Sig_inductive_typ(lex_t, [], [], t, _, _, [], r);
         Sig_datacon(lex_top, [], _t_top, _lex_t_top, 0, [], _, r1);
         Sig_datacon(lex_cons, [], _t_cons, _lex_t_cons, 0, [], _, r2)]
         when (lid_equals lex_t Const.lex_t_lid
            && lid_equals lex_top Const.lextop_lid
            && lid_equals lex_cons Const.lexcons_lid) ->

        let u = S.new_univ_name (Some r) in
        let t = mk (Tm_type(U_name u)) None r in
        let t = Subst.close_univ_vars [u] t in
        let tc = Sig_inductive_typ(lex_t, [u], [], t, [], [Const.lextop_lid; Const.lexcons_lid], [], r) in

        let utop = S.new_univ_name (Some r1) in
        let lex_top_t = mk (Tm_uinst(S.fvar (Ident.set_lid_range Const.lex_t_lid r1) Delta_constant None, [U_name utop])) None r1 in
        let lex_top_t = Subst.close_univ_vars [utop] lex_top_t in
        let dc_lextop = Sig_datacon(lex_top, [utop], lex_top_t, Const.lex_t_lid, 0, [], [], r1) in

        let ucons1 = S.new_univ_name (Some r2) in
        let ucons2 = S.new_univ_name (Some r2) in
        let lex_cons_t =
            let a = S.new_bv (Some r2) (mk (Tm_type(U_name ucons1)) None r2) in
            let hd = S.new_bv (Some r2) (S.bv_to_name a) in
            let tl = S.new_bv (Some r2) (mk (Tm_uinst(S.fvar (Ident.set_lid_range Const.lex_t_lid r2) Delta_constant None, [U_name ucons2])) None r2) in
            let res = mk (Tm_uinst(S.fvar (Ident.set_lid_range Const.lex_t_lid r2) Delta_constant None, [U_max [U_name ucons1; U_name ucons2]])) None r2 in
            Util.arrow [(a, Some S.imp_tag); (hd, None); (tl, None)] (S.mk_Total res) in
        let lex_cons_t = Subst.close_univ_vars [ucons1;ucons2]  lex_cons_t in
        let dc_lexcons = Sig_datacon(lex_cons, [ucons1;ucons2], lex_cons_t, Const.lex_t_lid, 0, [], [], r2) in
        Sig_bundle([tc; dc_lextop; dc_lexcons], [], lids, Env.get_range env)
      | _ ->
        failwith (Util.format1 "Unexpected lex_t: %s\n" (Print.sigelt_to_string (Sig_bundle(ses, [], lids, Range.dummyRange))))
    end

let tc_inductive env ses quals lids =
    (*  Consider this illustrative example:

         type T (a:Type) : (b:Type) -> Type =
             | C1 : x:a -> y:Type -> T a y
             | C2 : x:a -> z:Type -> w:Type -> T a z

         (1). We elaborate the type of T to
                T :  a:Type(ua) -> b:Type(ub) -> Type(u)

         (2). In a context
              G = a:Type(ua), T: (a:Type(ua) -> b:Type(ub) -> Type(u))
              we elaborate the type of

                C1 to x:a -> y:Type(uy) -> T a y
                C2 to x:a -> z:Type(uz) -> w:Type(uw) -> T a z

              Let the elaborated type of constructor i be of the form
                 xs:ts_i -> ti

              For each constructor i, we check

                 - G, [xs:ts_i]_j |- ts_i_j : Type(u_i_j)
                 - u_i_j <= u
                 - G, [xs:ts_i]   |- ti : Type _
                 - ti is an instance of T a


         (3). We jointly generalize the term

                (a:Type(ua) -> b:Type(ub) -> Type u)
                -> (xs:ts_1 -> t1)
                -> (xs:ts_2 -> t2)
                -> unit

             computing

                (uvs,            (a:Type(ua') -> b:Type(ub') -> Type u')
                                -> (xs:ts_1' -> t1')
                                -> (xs:ts_2' -> t2')
                                -> unit)

             The inductive is generalized to

                T<uvs> (a:Type(ua')) : b:Type(ub') -> Type u'


         (4). We re-typecheck and elaborate the type of each constructor to
              capture the proper instantiations of T

              i.e., we check

                G, T<uvs> : a:Type(ua') -> b:Type(ub') -> Type u', uvs |-
                       xs:ts_i' -> t_i'
                  ~>   xs:ts_i'' -> t_i''


             What we get, in effect, is

             type T<ua, ub, uw> (a:Type(ua)) : Type(ub) -> Type (max ua (ub + 1) (uw + 1)) =
                | C1 : (ua, ub, uw) => a:Type(ua) -> y:Type(ub) -> T<ua,ub,uw> a y
                | C2 : (ua, ub, uw) => a:Type(ua) -> z:Type(ub) -> w:Type(uw) -> T<ua,ub,uw> a z
    *)
    let warn_positivity l r =
        Errors.diag r (Util.format1 "Positivity check is not yet implemented (%s)" (Print.lid_to_string l)) in
    let env0 = env in

    (* 1. Checking each tycon *)
    let tc_tycon env (s:sigelt) : env_t          (* environment extended with a refined type for the type-constructor *)
                                * sigelt         (* the typed version of s, with universe variables still TBD *)
                                * universe       (* universe of the constructed type *)
                                = match s with
       | Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> //the only valid qual is Private
         assert (uvs = []);
         warn_positivity tc r;
 (*open*)let tps, k = SS.open_term tps k in
         let tps, env_tps, us = tc_tparams env tps in
         let indices, t = Util.arrow_formals k in
         let indices, env', us' = tc_tparams env_tps indices in
         let t, _ = tc_trivial_guard env' t in
         let k = Util.arrow indices (S.mk_Total t) in
         let t_type, u = U.type_u() in
         Rel.force_trivial_guard env' (Rel.teq env' t t_type);

(*close*)let t_tc = Util.arrow (tps@indices) (S.mk_Total t) in
         let tps = SS.close_binders tps in
         let k = SS.close tps k in
         let fv_tc = S.lid_as_fv tc Delta_constant None in
         Env.push_let_binding env_tps (Inr fv_tc) ([], t_tc),
         Sig_inductive_typ(tc, [], tps, k, mutuals, data, quals, r),
         u

        | _ -> failwith "impossible" in

    let positive_if_pure (_:term) (l:lid) = () in

    (* 2. Checking each datacon *)
    let tc_data env tcs = function
       | Sig_datacon(c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) ->
         assert (_uvs = []);

         let (tps, u_tc) = //u_tc is the universe of the inductive that c constructs
            let tps_u_opt = Util.find_map tcs (fun (se, u_tc) ->
                if lid_equals tc_lid (must (Util.lid_of_sigelt se))
                then let tps = match se with
                        | Sig_inductive_typ(_, _, tps, _, _, _, _, _) ->
                          tps |> List.map (fun (x, _) -> (x, Some S.imp_tag))
                        | _ -> failwith "Impossible" in
                     Some (tps, u_tc)
                else None) in
           match tps_u_opt with
            | Some x -> x
            | None ->
              if lid_equals tc_lid Const.exn_lid
              then [], U_zero
              else raise (Error("Unexpected data constructor", r)) in

         let arguments, result =
            match (SS.compress t).n with
                | Tm_arrow(bs, res) ->
                  //the type of each datacon is already a function with the type params as arguments
                  //need to map the prefix of bs corresponding to params to the tps of the inductive
                  let _, bs' = Util.first_N ntps bs in
                  let t = mk (Tm_arrow(bs', res)) None t.pos in
                  let subst = tps |> List.mapi (fun i (x, _) -> DB(ntps - (1 + i), x)) in
(*open*)          Util.arrow_formals (SS.subst subst t)
                | _ -> [], t in

         if Env.debug env Options.Low then Util.print3 "Checking datacon  %s : %s -> %s \n"
                (Print.lid_to_string c)
                (Print.binders_to_string "->" arguments)
                (Print.term_to_string result);


         let arguments, env', us = tc_tparams env arguments in
         let result, _ = tc_trivial_guard env' result in
         let head, _ = Util.head_and_args result in
         let _ = match (SS.compress head).n with
            | Tm_fvar fv when S.fv_eq_lid fv tc_lid -> ()
            | _ -> raise (Error(Util.format1 "Expected a constructor of type %s" (Print.lid_to_string tc_lid), r)) in
         let g =List.fold_left2 (fun g (x, _) u_x ->
                positive_if_pure x.sort tc_lid;
                Rel.conj_guard g (Rel.universe_inequality u_x u_tc))
            Rel.trivial_guard
            arguments
            us in

(*close*)let t = Util.arrow ((tps |> List.map (fun (x, _) -> (x, Some (Implicit true))))@arguments) (S.mk_Total result) in
                        //NB: the tps are tagged as Implicit inaccessbile arguments of the data constructor
         Sig_datacon(c, [], t, tc_lid, ntps, quals, [], r),
         g

      | _ -> failwith "impossible" in

    (* 3. Generalizing universes and 4. instantiate inductives within the datacons *)
    let generalize_and_inst_within env g tcs datas =
        Rel.force_trivial_guard env g;
        let binders = tcs |> List.map (function
            | Sig_inductive_typ(_, _, tps, k, _, _, _, _) -> S.null_binder (Util.arrow tps <| mk_Total k)
            | _ -> failwith "Impossible")  in
        let binders' = datas |> List.map (function
            | Sig_datacon(_, _, t, _, _, _, _, _) -> S.null_binder t
            | _ -> failwith "Impossible") in
        let t = Util.arrow (binders@binders') (S.mk_Total Common.t_unit) in
        if Env.debug env Options.Low then Util.print1 "@@@@@@Trying to generalize universes in %s\n" (N.term_to_string env t);
        let (uvs, t) = TcUtil.generalize_universes env t in
        if Env.debug env Options.Low then Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                                (uvs |> List.map (fun u -> u.idText) |> String.concat ", ")
                                (Print.term_to_string t);
        let uvs, t = SS.open_univ_vars uvs t in
        let args, _ = Util.arrow_formals t in
        let tc_types, data_types = Util.first_N (List.length binders) args in
        let tcs = List.map2 (fun (x, _) se -> match se with
            | Sig_inductive_typ(tc, _, tps, _, mutuals, datas, quals, r) ->
              let ty = SS.close_univ_vars uvs x.sort in
              let tps, t = match (SS.compress ty).n with
                | Tm_arrow(binders, c) ->
                  let tps, rest = Util.first_N (List.length tps) binders in
                  let t = match rest with
                    | [] -> Util.comp_result c
                    | _ -> mk (Tm_arrow(rest, c)) !x.sort.tk x.sort.pos in
                  tps, t
                | _ -> [], ty in
               Sig_inductive_typ(tc, uvs, tps, t, mutuals, datas, quals, r)
            | _ -> failwith "Impossible")
            tc_types tcs in

        //4. Instantiate the inductives in each datacon with the generalized universes
        let datas = match uvs with
            | [] -> datas
            | _ ->
             let uvs_universes = uvs |> List.map U_name in
             let tc_insts = tcs |> List.map (function Sig_inductive_typ(tc, _, _, _, _, _, _, _) -> (tc, uvs_universes) | _ -> failwith "Impossible") in
             List.map2 (fun (t, _) d ->
                match d with
                    | Sig_datacon(l, _, _, tc, ntps, quals, mutuals, r) ->
                        let ty = InstFV.instantiate tc_insts t.sort |> SS.close_univ_vars uvs in
                        Sig_datacon(l, uvs, ty, tc, ntps, quals, mutuals, r)
                    | _ -> failwith "Impossible")
             data_types datas in
        tcs, datas in

    let tys, datas = ses |> List.partition (function Sig_inductive_typ _ -> true | _ -> false) in

    let env0 = env in

    (* Check each tycon *)
    let env, tcs, g = List.fold_right (fun tc (env, all_tcs, g)  ->
            let env, tc, tc_u = tc_tycon env tc in
            let g' = Rel.universe_inequality S.U_zero tc_u in
            if Env.debug env Options.Low
            then Util.print1 "Checked inductive: %s\n" (Print.sigelt_to_string tc);
            env, (tc, tc_u)::all_tcs, Rel.conj_guard g g')
        tys
        (env, [], Rel.trivial_guard) in

    (* Check each datacon *)
    let datas, g = List.fold_right (fun se (datas, g) ->
            let data, g' = tc_data env tcs se in
            data::datas, Rel.conj_guard g g')
        datas
        ([], g) in

    let tcs, datas = generalize_and_inst_within env0 g (List.map fst tcs) datas in
    Sig_bundle(tcs@datas, quals, lids, Env.get_range env0)

let rec tc_decl env se = match se with
    | Sig_inductive_typ _
    | Sig_datacon _ ->
      failwith "Impossible bare data-constructor"

    | Sig_bundle(ses, quals, lids, r) when (lids |> Util.for_some (lid_equals Const.lex_t_lid)) ->
      //lex_t is very special; it uses a more expressive form of universe polymorphism than is allowed elsewhere
      //Instead of this special treatment, we could make use of explicit lifts, but LexCons is used pervasively
      (*
          type lex_t<u> =
           | LexTop<u>  : lex_t<u>
           | LexCons<u1, u2> : #a:Type(u1) -> a -> lex_t<u2> -> lex_t<max u1 u2>
      *)
      let env = Env.set_range env r in
      let se = tc_lex_t env ses quals lids  in
      se, Env.push_sigelt env se

    | Sig_bundle(ses, quals, lids, r) ->
      let env = Env.set_range env r in
      let se = tc_inductive env ses quals lids  in
      se, Env.push_sigelt env se

    | Sig_pragma(p, r) ->
       let set_options t s = match Options.set_options t s with
            | Getopt.GoOn -> ()
            | Getopt.Help  -> raise (Error ("Failed to process pragma: use 'fstar --help' to see which options are available", r))
            | Getopt.Die s -> raise (Error ("Failed to process pragma: " ^s, r)) in
        begin match p with
            | SetOptions o ->
                set_options Options.Set o;
                se, env
            | ResetOptions sopt ->
                Options.restore_cmd_line_options() |> ignore;
                let _ = match sopt with
                    | None -> ()
                    | Some s -> set_options Options.Reset s in
                env.solver.refresh();
                se, env
        end

    | Sig_new_effect_for_free(ne, r) ->
      let ne = tc_eff_decl env ne ForFree in
      (* Fields have been synthesized by [tc_eff_decl] *)
      let se = Sig_new_effect(ne, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_new_effect(ne, r) ->
      let ne = tc_eff_decl env ne NotForFree in
      let se = Sig_new_effect(ne, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_sub_effect(sub, r) ->
      let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
      let b, wp_b_tgt = monad_signature env sub.target (Env.lookup_effect_lid env sub.target) in
      let wp_a_tgt    = SS.subst [NT(b, S.bv_to_name a)] wp_b_tgt in
      let expected_k   = Util.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
      let lift = check_and_gen env (snd sub.lift) expected_k in
      let sub = {sub with lift=lift} in
      let se = Sig_sub_effect(sub, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_effect_abbrev(lid, uvs, tps, c, tags, r) ->
      assert (uvs = []);
      let env0 = env in
      let env = Env.set_range env r in
      let tps, c = SS.open_comp tps c in
      let tps, env, us = tc_tparams env tps in
      let c, u, g = tc_comp env c in
      Rel.force_trivial_guard env g;
      let tps = SS.close_binders tps in
      let c = SS.close_comp tps c in
      let uvs, t = Util.generalize_universes env0 (mk (Tm_arrow(tps, c)) None r) in
      let tps, c = match tps, (SS.compress t).n with
        | [], Tm_arrow(_, c) -> [], c
        | _,  Tm_arrow(tps, c) -> tps, c
        | _ -> failwith "Impossible" in
      let se = Sig_effect_abbrev(lid, uvs, tps, c, tags, r) in
      let env = Env.push_sigelt env0 se in
      se, env

    | Sig_declare_typ(lid, uvs, t, quals, r) -> //NS: No checks on the qualifiers?
      let env = Env.set_range env r in
      assert (uvs = []);
      let uvs, t = check_and_gen env t (fst (U.type_u())) in
      let se = Sig_declare_typ(lid, uvs, t, quals, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_assume(lid, phi, quals, r) ->
      let env = Env.set_range env r in
      let k, _ = U.type_u() in
      let phi = tc_check_trivial_guard env phi k |> norm env in
      TcUtil.check_uvars r phi;
      let se = Sig_assume(lid, phi, quals, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_main(e, r) ->
      let env = Env.set_range env r in
      let env = Env.set_expected_typ env Common.t_unit in
      let e, c, g1 = tc_term env e in
      let e, _, g = check_expected_effect env (Some (Util.ml_comp Common.t_unit r)) (e, c.comp()) in
      Rel.force_trivial_guard env (Rel.conj_guard g1 g);
      let se = Sig_main(e, r) in
      let env = Env.push_sigelt env se in
      se, env

    | Sig_let(lbs, r, lids, quals) ->
      let env = Env.set_range env r in
      let check_quals_eq l qopt q = match qopt with
        | None -> Some q
        | Some q' ->
          if List.length q = List.length q'
          && List.forall2 Util.qualifier_equal q q'
          then Some q
          else raise (Error(Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                                (Print.lid_to_string l)
                                (Print.quals_to_string q)
                                (Print.quals_to_string q'), r)) in

      (* 1. (a) Annotate each lb in lbs with a type from the corresponding val decl, if there is one
            (b) Generalize the type of lb only if none of the lbs have val decls
       *)
      let should_generalize, lbs', quals_opt = snd lbs |> List.fold_left (fun (gen, lbs, quals_opt) lb ->
            let lbname = right lb.lbname in //this is definitely not a local let binding
            let gen, lb, quals_opt = match Env.try_lookup_val_decl env lbname.fv_name.v with
              | None -> gen, lb, quals_opt //no annotation found; use whatever was in the let binding

              | Some ((uvs,tval), quals) ->
                let quals_opt = check_quals_eq lbname.fv_name.v quals_opt quals in
                let _ = match lb.lbtyp.n with
                  | Tm_unknown -> ()
                  | _ -> Errors.warn r "Annotation from val declaration overrides inline type annotation" in
                false, //explicit annotation provided; do not generalize
                mk_lb (Inr lbname, uvs, Const.effect_ALL_lid, tval, lb.lbdef),
                quals_opt  in

             gen, lb::lbs, quals_opt) (true, [], (if quals=[] then None else Some quals)) in

      let quals = match quals_opt with
        | None -> [Unfoldable]
        | Some q ->
          if q |> Util.for_some (function Irreducible | Unfoldable | Inline -> true | _ -> false)
          then q
          else Unfoldable::q in //the default visibility for a let binding is Unfoldable

      let lbs' = List.rev lbs' in

      (* 2. Turn the top-level lb into a Tm_let with a unit body *)
      let e = mk (Tm_let((fst lbs, lbs'), mk (Tm_constant (Const_unit)) None r)) None r in

      (* 3. Type-check the Tm_let and then convert it back to a Sig_let *)
      let se, lbs = match tc_maybe_toplevel_term ({env with top_level=true; generalize=should_generalize}) e with
         | {n=Tm_let(lbs, e)}, _, g when Rel.is_trivial g ->
            //propagate the MaskedEffect tag to the qualifiers
            let quals = match e.n with
                | Tm_meta(_, Meta_desugared Masked_effect) -> HasMaskedEffect::quals
                | _ -> quals in
            Sig_let(lbs, r, lids, quals), lbs
        | _ -> failwith "impossible" in

      (* 4. Print the type of top-level lets, if requested *)
      if log env
      then Util.print1 "%s\n" (snd lbs |> List.map (fun lb ->
            let should_log = match Env.try_lookup_val_decl env (right lb.lbname).fv_name.v with
                | None -> true
                | _ -> false in
            if should_log
            then Util.format2 "let %s : %s" (Print.lbname_to_string lb.lbname) (Print.term_to_string (*env*) lb.lbtyp)
            else "") |> String.concat "\n");

      let env = Env.push_sigelt env se in
      se, env


let for_export hidden se : list<sigelt> * list<lident> =
   (* Exporting symbols based on whether they have been marked 'abstract'


        -- NB> Symbols marked 'private' are restricted by the visibility rules enforced during desugaring.
           i.e., if a module A marks symbol x as private, then a module B simply cannot refer to A.x
           OTOH, if A marks x as abstract, B can refer to A.x, but cannot see its definition.

      Here, if a symbol is abstract, we only export its declaration, not its definition.
      The reason we export the declaration of private symbols is to account for cases like this:

        module A
           abstract let x = 0
           let y = x

        When encoding A to the SMT solver, we need to encode the definition of y.
        If we simply eliminated x altogether when exporting it, the body of y would no longer be well formed.
        So, instead, in effect, we export A as

        module A
            assume val x : int
            let y = x

   *)
   let is_abstract quals = quals |> Util.for_some (function Abstract-> true | _ -> false) in
   let is_hidden_proj_or_disc q = match q with
        | Projector(l, _)
        | Discriminator l -> hidden |> Util.for_some (lid_equals l)
        | _ -> false in
   match se with
    | Sig_pragma         _ -> [], hidden

    | Sig_inductive_typ _
    | Sig_datacon _ -> failwith "Impossible"

    | Sig_bundle(ses, quals, _, _) ->
      if is_abstract quals
      then List.fold_right (fun se (out, hidden) -> match se with
            | Sig_inductive_typ(l, us, bs, t, _, _, quals, r) ->
              let dec = Sig_declare_typ(l, us, mk (Tm_arrow(bs, S.mk_Total t)) None r, Assumption::New::quals, r) in
              dec::out, hidden
            | Sig_datacon(l, us, t, _, _, _, _, r) -> //logically, each constructor just becomes an uninterpreted function
              let dec = Sig_declare_typ(l, us, t, [Assumption], r) in
              dec::out, l::hidden
            | _ ->
              out, hidden) ses ([], hidden)
      else [se], hidden

    | Sig_assume(_, _, quals, _) ->
      if is_abstract quals
      then [], hidden
      else [se], hidden

    | Sig_declare_typ(l, us, t, quals, r) ->
      if quals |> Util.for_some is_hidden_proj_or_disc //hidden projectors/discriminators become uninterpreted
      then [Sig_declare_typ(l, us, t, [Assumption], r)], l::hidden
      else if quals |> Util.for_some (function
        | Assumption
        | Projector _
        | Discriminator _ -> true
        | _ -> false)
      then [se], hidden //Assumptions, Intepreted proj/disc are retained
      else [], hidden   //other declarations vanish
                        //they will be replaced by the definitions that must follow

    | Sig_main  _ -> [], hidden

    | Sig_new_effect     _
    | Sig_new_effect_for_free _
    | Sig_sub_effect     _
    | Sig_effect_abbrev  _ -> [se], hidden

    | Sig_let((false, [lb]), _, _, quals) when (quals |> Util.for_some is_hidden_proj_or_disc) ->
      let fv = right lb.lbname in
      let lid = fv.fv_name.v in
      if hidden |> Util.for_some (S.fv_eq_lid fv)
      then [], hidden //this projector definition already has a declare_typ
      else let dec = Sig_declare_typ(fv.fv_name.v, lb.lbunivs, lb.lbtyp, [Assumption], Ident.range_of_lid lid) in
           [dec], lid::hidden

    | Sig_let(lbs, r, l, quals) ->
      if is_abstract quals
      then snd lbs |> List.map (fun lb ->
           Sig_declare_typ((right lb.lbname).fv_name.v, lb.lbunivs, lb.lbtyp, Assumption::quals, r)), hidden
      else [se], hidden

let tc_decls env ses =
 let ses, exports, env, _ =
  ses |> List.fold_left (fun (ses, exports, env, hidden) se ->
          if Env.debug env Options.Low
          then Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" (Print.sigelt_to_string se);

          let se, env = tc_decl env se  in

          if !Options.log_types || Env.debug env <| Options.Other "LogTypes"
          then Util.print1 "Checked: %s\n" (Print.sigelt_to_string se);

          env.solver.encode_sig env se;

          let exported, hidden = for_export hidden se in
          se::ses, exported::exports, env, hidden)
  ([], [], env, []) in
  List.rev ses, List.rev exports |> List.flatten, env

let tc_partial_modul env modul =
  let name = Util.format2 "%s %s"  (if modul.is_interface then "interface" else "module") modul.name.str in
  let msg = "Internals for " ^name in
  let env = {env with Env.is_iface=modul.is_interface; admit=not (Options.should_verify modul.name.str)} in
  if not (lid_equals modul.name Const.prims_lid) then env.solver.push msg;
  let env = Env.set_current_module env modul.name in
  let ses, exports, env = tc_decls env modul.declarations in
  {modul with declarations=ses}, exports, env

let tc_more_partial_modul env modul decls =
  let ses, exports, env = tc_decls env decls in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, exports, env

let finish_partial_modul env modul exports =
  let modul = {modul with exports=exports; is_interface=modul.is_interface} in
  let env = Env.finish_module env modul in
  if not (lid_equals modul.name Const.prims_lid)
  then begin
    env.solver.pop ("Ending modul " ^ modul.name.str);
    env.solver.encode_modul env modul;
    env.solver.refresh();
    Options.restore_cmd_line_options() |> ignore
  end;
  modul, env

let tc_modul env modul =
  let modul, non_private_decls, env = tc_partial_modul env modul in
  finish_partial_modul env modul non_private_decls

let type_of env e =
    if Env.debug env <| Options.Other "RelCheck" then Util.print1 "Checking term %s\n" (Print.term_to_string e);
    //let env, _ = Env.clear_expected_typ env in
    let env = {env with top_level=false} in
    let t, c, g =
        try tc_tot_or_gtot_term env e
        with Error(msg, _) -> raise (Error("Implicit argument: " ^ msg, Env.get_range env)) in
    if Util.is_total_lcomp c
    then t, c.res_typ, g
    else raise (Error(Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" (Print.term_to_string e), Env.get_range env))

let check_module env m =
    if List.length !Options.debug <> 0
    then Util.print2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.lid_to_string m.name);
    let m, env = tc_modul env m in
    if Options.should_dump m.name.str then Util.print1 "%s\n" (Print.modul_to_string m);
    m, env


