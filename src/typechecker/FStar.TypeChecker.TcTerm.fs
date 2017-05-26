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
module FStar.TypeChecker.TcTerm
open FStar.All

open FStar
open FStar.Errors
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
module BU = FStar.Util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print



(* Some local utilities *)
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
let steps env = [N.Beta; N.Eager_unfolding]
let norm   env t = N.normalize (steps env) env t
let norm_c env c = N.normalize_comp (steps env) env c
let check_no_escape head_opt env (fvs:list<bv>) kt =
    let rec aux try_norm t = match fvs with
        | [] -> t
        | _ ->
          let t = if try_norm then norm env t else t in
          let fvs' = Free.names t in
          begin match List.tryFind (fun x -> BU.set_mem x fvs') fvs with
            | None -> t
            | Some x ->
              if not try_norm
              then aux true t
              else let fail () =
                       let msg = match head_opt with
                        | None -> BU.format1 "Bound variables '%s' escapes; add a type annotation" (Print.bv_to_string x)
                        | Some head -> BU.format2 "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                        (Print.bv_to_string x) (N.term_to_string env head) in
                       raise (Error(msg, Env.get_range env)) in
                   let s = TcUtil.new_uvar env (fst <| U.type_u()) in
                   match Rel.try_teq true env t s with
                    | Some g -> Rel.force_trivial_guard env g; s
                    | _ -> fail ()
         end in
    aux false kt

let push_binding env b =
  Env.push_bv env (fst b)

let maybe_extend_subst s b v : subst_t =
    if is_null_binder b then s
    else NT(fst b, v)::s

let set_lcomp_result lc t =
    {lc with res_typ=t; comp=fun () -> U.set_result_typ (lc.comp()) t}

let memo_tk (e:term) (t:typ) = e.tk := Some t.n; e

//Interface to FStar.TypeChecker.Rel:

(************************************************************************************************************)
(* value_check_expected_type env e tlc g                                                                    *)
(*     e is computed to have type or computation type, tlc                                                  *)
(*          subject to the guard g                                                                          *)
(* This function compares tlc to the expected type from the context, augmenting the guard if needed         *)
(************************************************************************************************************)
let value_check_expected_typ env (e:term) (tlc:either<term,lcomp>) (guard:guard_t)
    : term * lcomp * guard_t =
  let should_return t =
    match (SS.compress t).n with
    | Tm_arrow(_, c) ->
      if TcUtil.is_pure_or_ghost_effect env (U.comp_effect_name c)
      then let t = U.unrefine <| (U.comp_result c) in
           match (SS.compress t).n with
           | Tm_fvar fv when (S.fv_eq_lid fv Const.unit_lid) -> false //uninformative function
           | Tm_constant _ -> false
           | _ -> true
      else false //can't reason about effectful function definitions, so not worth returning this
//    | Tm_type _ -> false
    | _ -> true in
  (* if term, then lc is a trivial lazy computation (lcomp_of_comp) *)
  let lc = match tlc with
    | Inl t -> U.lcomp_of_comp (if not (should_return t)
                                || not (Env.should_verify env)
                                then mk_Total t //don't add a return if we're not verifying; or if we're returning a function
                                else TcUtil.return_value env t e)
    | Inr lc -> lc in
  let t = lc.res_typ in
  let e, lc, g = match Env.expected_typ env with
   | None -> memo_tk e t, lc, guard
   | Some t' ->
     if debug env Options.High
     then BU.print2 "Computed return type %s; expected type %s\n" (Print.term_to_string t) (Print.term_to_string t');
     let e, lc = TcUtil.maybe_coerce_bool_to_type env e lc t' in //add a b2t coercion is e:bool and t'=Type
     let t = lc.res_typ in
     let e, g = TcUtil.check_and_ascribe env e t t' in
     if debug env Options.High
     then BU.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                (Print.term_to_string t) (Print.term_to_string t')
                (Rel.guard_to_string env g) (Rel.guard_to_string env guard);
     let msg = if Rel.is_trivial g then None else (Some <| Err.subtyping_failed env t t') in
     let g = Rel.conj_guard g guard in
     (* adding a guard for confirming that the computed type t is a subtype of the expected type t' *)
     let lc, g = TcUtil.strengthen_precondition msg env e lc g in
     memo_tk e t', set_lcomp_result lc t', g in
  if debug env Options.Low
  then BU.print1 "Return comp type is %s\n" (Print.lcomp_to_string lc);
  e, lc, g

(************************************************************************************************************)
(* comp_check_expected_type env e lc g                                                                      *)
(*    similar to value_check_expected_typ, except this time e is a non-value                                *)
(************************************************************************************************************)
let comp_check_expected_typ env e lc : term * lcomp * guard_t =
  match Env.expected_typ env with
   | None -> e, lc, Rel.trivial_guard
   | Some t ->
     let e, lc = TcUtil.maybe_coerce_bool_to_type env e lc t in //Add a b2t coercion if e:bool and t=Type
     TcUtil.weaken_result_typ env e lc t

(************************************************************************************************************)
(* check_expected_effect: triggers a sub-effecting, WP implication, etc. if needed                          *)
(************************************************************************************************************)
let check_expected_effect env (copt:option<comp>) (e, c) : term * comp * guard_t =
  let tot_or_gtot c = //expects U.is_pure_or_ghost_comp c
     if U.is_pure_comp c
     then mk_Total (U.comp_result c)
     else if U.is_pure_or_ghost_comp c
     then mk_GTotal (U.comp_result c)
     else failwith "Impossible: Expected pure_or_ghost comp"
  in
  let expected_c_opt, c =
    match copt with
    | Some _ -> copt, c
    | None  ->
        if (Options.ml_ish()
            && Ident.lid_equals Const.effect_ALL_lid (U.comp_effect_name c))
        || (Options.ml_ish ()
            && env.lax
            && not (U.is_pure_or_ghost_comp c))
        then Some (U.ml_comp (U.comp_result c) e.pos), c
        else if U.is_tot_or_gtot_comp c //these are already the defaults for their particular effects
        then None, tot_or_gtot c //but, force c to be exactly ((G)Tot t), since otherwise it may actually contain a return
        else if U.is_pure_or_ghost_comp c
             then Some (tot_or_gtot c), c
             else None, c
  in
  let c = norm_c env c in
  match expected_c_opt with
    | None ->
      e, c, Rel.trivial_guard
    | Some expected_c -> //expected effects should already be normalized
       let e, _, g = TcUtil.check_comp env e c expected_c in
       let g = TcUtil.label_guard (Env.get_range env) "could not prove post-condition" g in
       if debug env Options.Low then BU.print2 "(%s) DONE check_expected_effect; guard is: %s\n" (Range.string_of_range e.pos) (guard_to_string env g);
       let e = TcUtil.maybe_lift env e (U.comp_effect_name c) (U.comp_effect_name expected_c) (U.comp_result c) in
       e, expected_c, g

let no_logical_guard env (te, kt, f) =
  match guard_form f with
    | Trivial -> te, kt, f
    | NonTrivial f -> raise (Error(Err.unexpected_non_trivial_precondition_on_term env f, Env.get_range env))

let print_expected_ty env = match Env.expected_typ env with
    | None -> BU.print_string "Expected type is None"
    | Some t -> BU.print1 "Expected type is %s" (Print.term_to_string t)

(************************************************************************************************************)
(* check the patterns in an SMT lemma to make sure all bound vars are mentiond *)
(************************************************************************************************************)
let check_smt_pat env t bs c =
    if U.is_smt_lemma t //check patterns cover the bound vars
    then match c.n with
        | Comp ({effect_args=[_pre; _post; (pats, _)]}) ->
            let pat_vars = Free.names (N.normalize [N.Beta] env pats) in
            begin match bs |> BU.find_opt (fun (b, _) -> not(BU.set_mem b pat_vars)) with
                | None -> ()
                | Some (x,_) -> Errors.warn t.pos (BU.format1 "Pattern misses at least one bound variable: %s" (Print.bv_to_string x))
            end
        | _ -> failwith "Impossible"

(************************************************************************************************************)
(* Building the environment for the body of a let rec;                                                      *)
(* guards the recursively bound names with a termination check                                              *)
(************************************************************************************************************)
let guard_letrecs env actuals expected_c : list<(lbname*typ)> =
    if not (Env.should_verify env) then env.letrecs else
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
                    let t = N.unfold_whnf env (U.unrefine b.sort) in
                    match t.n with
                        | Tm_type _
                        | Tm_arrow _ -> []
                        | _ -> [S.bv_to_name b]) in
          let as_lex_list dec =
                let head, _ = U.head_and_args dec in
                match head.n with (* The decreases clause is always an expression of type lex_t; promote if it isn't *)
                    | Tm_fvar fv when S.fv_eq_lid fv Const.lexcons_lid -> dec
                    | _ -> mk_lex_list [dec] in
          let cflags = U.comp_flags c in
          match cflags |> List.tryFind (function DECREASES _ -> true | _ -> false) with
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
                  let bs, (last, imp) = BU.prefix formals in
                  let last = {last with sort=U.refine last precedes} in
                  let refined_formals = bs@[(last,imp)] in
        (*close*) let t' = U.arrow refined_formals c in
                  if debug env Options.Low
                  then BU.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                        (Print.lbname_to_string l) (Print.term_to_string t) (Print.term_to_string t');
                  l,t'

                | _ -> raise (Error ("Annotated type of 'let rec' must be an arrow", t.pos)) in

        letrecs |> List.map guard_one_letrec

(************************************************************************************************************)
(* Main type-checker begins here                                                                            *)
(************************************************************************************************************)
let rec tc_term env e = tc_maybe_toplevel_term ({env with top_level=false}) e

and tc_maybe_toplevel_term env (e:term) : term                  (* type-checked and elaborated version of e            *)
                                        * lcomp                 (* computation type where the WPs are lazily evaluated *)
                                        * guard_t =             (* well-formedness condition                           *)
  let env = if e.pos=Range.dummyRange then env else Env.set_range env e.pos in
  if debug env Options.Low then BU.print2 "%s (%s)\n" (Range.string_of_range <| Env.get_range env) (Print.tag_of_term e);
  let top = SS.compress e in
  match top.n with
  | Tm_delayed _ -> failwith "Impossible"

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
          let c = TcUtil.bind e1.pos env (Some e1) c1 (None, c2) in
          let e1 = TcUtil.maybe_lift env e1 c1.eff_name c.eff_name c1.res_typ in
          let e2 = TcUtil.maybe_lift env e2 c2.eff_name c.eff_name c2.res_typ in
          let e = mk (Tm_let((false, [mk_lb (x, [], c1.eff_name, Common.t_unit, e1)]), e2)) (Some c.res_typ.n) e.pos in
          let e = TcUtil.maybe_monadic env e c.eff_name c.res_typ in
          let e = mk (Tm_meta(e, Meta_desugared Sequence)) (Some c.res_typ.n) top.pos in
          e, c, Rel.conj_guard g1 g2
        | _ ->
          let e, c, g = tc_term env e in
          let e = mk (Tm_meta(e, Meta_desugared Sequence)) (Some c.res_typ.n) top.pos in
          e, c, g
    end

  | Tm_meta(e, Meta_monadic _) ->
    (* KM : This case should not happen when typechecking once but is it really *)
    (* okay to just drop the annotation ? And what about Meta_monadic_lift then ? *)
    tc_term env e

  | Tm_meta(e, m) ->
    let e, c, g = tc_term env e in
    let e = mk (Tm_meta(e, m)) (Some c.res_typ.n) top.pos in
    e, c, g

  | Tm_ascribed (e, (Inr expected_c, topt), _) ->
    let env0, _ = Env.clear_expected_typ env in
    let expected_c, _, g = tc_comp env0 expected_c in
    let t_res = U.comp_result expected_c in
    let e, c', g' = tc_term (Env.set_expected_typ env0 t_res) e in
    let e, expected_c, g'' = check_expected_effect env0 (Some expected_c) (e, c'.comp()) in
    let e = mk (Tm_ascribed(e, (Inl t_res, None), Some (U.comp_effect_name expected_c))) (Some t_res.n) top.pos in
    let lc = U.lcomp_of_comp expected_c in
    let f = Rel.conj_guard g (Rel.conj_guard g' g'') in
    let topt = tc_tactic_opt env0 topt in
    let f = match topt with
            | None -> f
            | Some tactic -> Rel.map_guard f (Common.mk_by_tactic tactic) in
    let e, c, f2 = comp_check_expected_typ env e lc in
    e, c, Rel.conj_guard f f2

  | Tm_ascribed (e, (Inl t, topt), _) ->
    let k, u = U.type_u () in
    let t, _, f = tc_check_tot_or_gtot_term env t k in
    let e, c, g = tc_term (Env.set_expected_typ env t) e in
    let c, f = TcUtil.strengthen_precondition (Some (fun () -> Err.ill_kinded_type)) (Env.set_range env t.pos) e c f in
    let e, c, f2 = comp_check_expected_typ env (mk (Tm_ascribed(e, (Inl t, None), Some c.eff_name)) (Some t.n) top.pos) c in
    e, c, Rel.conj_guard f (Rel.conj_guard g f2)

  | Tm_app({n=Tm_constant Const_reify}, a::hd::rest)
  | Tm_app({n=Tm_constant (Const_reflect _)}, a::hd::rest) ->
    //reify and reflect are a unary operators;
    //if there are more args, then explicitly curry them
    let rest = hd::rest in //no 'as' clauses in F* yet, so we need to do this ugliness
    let unary_op, _ = U.head_and_args top in
    let head = mk (Tm_app(unary_op, [a])) None (Range.union_ranges unary_op.pos (fst a).pos) in
    let t = mk (Tm_app(head, rest)) None top.pos in
    tc_term env t

  | Tm_app({n=Tm_constant Const_reify}, [(e, aqual)]) ->
    if Option.isSome aqual
    then Errors.warn e.pos "Qualifier on argument to reify is irrelevant and will be ignored";
    let e, c, g =
      let env0, _ = Env.clear_expected_typ env in
      tc_term env0 e
    in
    let reify_op, _ = U.head_and_args top in
    let u_c =
        (* c' is the computation type of the computation type and as such should be Type u *)
        let _, c', _ = tc_term env c.res_typ in
        match (SS.compress c'.res_typ).n with
        | Tm_type u -> u
        | _ ->
            (* We constrain this unification variable to be of the shape Type u *)
            (* for some new unification variable u *)
            let t, u = U.type_u () in
            let g_opt = Rel.try_teq true env c'.res_typ t in
            begin match g_opt with
            | Some g' -> Rel.force_trivial_guard env g'
            | None ->
                failwith (BU.format3
                  "Unexpected result type of computation. \
                   The computation type %s of the term %s should have \
                   type Type n for some level n but has type %s"
                  (Print.lcomp_to_string c')
                  (Print.term_to_string c.res_typ)
                  (Print.term_to_string c'.res_typ))
            end ;
            u
    in
    let repr = Env.reify_comp env (c.comp()) u_c in
    let e = mk (Tm_app(reify_op, [(e, aqual)])) (Some repr.n) top.pos in
    let c = S.mk_Total repr |> U.lcomp_of_comp in
    let e, c, g' = comp_check_expected_typ env e c in
    e, c, Rel.conj_guard g g'

  | Tm_app({n=Tm_constant (Const_reflect l)}, [(e, aqual)])->
    if Option.isSome aqual
    then Errors.warn e.pos "Qualifier on argument to reflect is irrelevant and will be ignored";
    let no_reflect () = raise (Error(BU.format1 "Effect %s cannot be reified" l.str, e.pos)) in
    let reflect_op, _ = U.head_and_args top in
    begin match Env.effect_decl_opt env l with
    | None -> no_reflect()
    | Some (ed, qualifiers) ->
      if not (qualifiers |> S.contains_reflectable) then
        no_reflect ()
      else
        let env_no_ex, topt = Env.clear_expected_typ env in
        let expected_repr_typ, res_typ, wp, g0 =
          let u = Env.new_u_univ () in
          let repr = Env.inst_effect_fun_with [u] env ed ([], ed.repr) in
          let t = mk (Tm_app(repr, [as_arg S.tun; as_arg S.tun])) None top.pos in
          let t, _, g = tc_tot_or_gtot_term (Env.clear_expected_typ env |> fst) t in
          match (SS.compress t).n with
          | Tm_app(_, [(res, _); (wp, _)]) -> t, res, wp, g
          | _ -> failwith "Impossible"
        in
        let e, g =
          let e, c, g = tc_tot_or_gtot_term env_no_ex e in
          if not <| U.is_total_lcomp c
          then Err.add_errors env ["Expected Tot, got a GTot computation", e.pos];
          match Rel.try_teq true env_no_ex c.res_typ expected_repr_typ with
          | None -> Err.add_errors env [BU.format2 "Expected an instance of %s; got %s" (Print.term_to_string ed.repr) (Print.term_to_string c.res_typ), e.pos];
                    e, Rel.conj_guard g g0
          | Some g' -> e, Rel.conj_guard g' (Rel.conj_guard g g0)
        in
        let c = S.mk_Comp ({
              comp_univs=[env.universe_of env res_typ];
              effect_name = ed.mname;
              result_typ=res_typ;
              effect_args=[as_arg wp];
              flags=[]
            }) |> U.lcomp_of_comp
        in
        let e = mk (Tm_app(reflect_op, [(e, aqual)])) (Some res_typ.n) top.pos in
        let e, c, g' = comp_check_expected_typ env e c in
        e, c, Rel.conj_guard g' g
    end

  | Tm_app(head, args) ->
    let env0 = env in
    let env = Env.clear_expected_typ env |> fst |> instantiate_both in
    if debug env Options.High then BU.print2 "(%s) Checking app %s\n" (Range.string_of_range top.pos) (Print.term_to_string top);

    //Don't instantiate head; instantiations will be computed below, accounting for implicits/explicits
    let head, chead, g_head = tc_term (no_inst env) head in
    let e, c, g = if not env.lax && TcUtil.short_circuit_head head
                  then let e, c, g = check_short_circuit_args env head chead g_head args (Env.expected_typ env0) in
                       //TODO: this is not efficient:
                       //      It is quadratic in the size of boolean terms
                       //      e.g., a && b && c && d ... & zzzz will be huge
                       let c = if Env.should_verify env &&
                               not (U.is_lcomp_partial_return c) &&
                               U.is_pure_or_ghost_lcomp c
                               then TcUtil.maybe_assume_result_eq_pure_term env e c
                               else c in
                       e, c, g
                  else check_application_args env head chead g_head args (Env.expected_typ env0) in
    if Env.debug env Options.Extreme
    then BU.print1 "Introduced {%s} implicits in application\n" (Rel.print_pending_implicits g);
    let e, c, g' = comp_check_expected_typ env0 e c in
    let gimp =
        match (SS.compress head).n with
        | Tm_uvar(u, _) ->
            let imp = ("head of application is a uvar", env0, u, e, c.res_typ, head.pos) in
            {Rel.trivial_guard with implicits=[imp]}
        | _ -> Rel.trivial_guard in
    let gres = Rel.conj_guard g (Rel.conj_guard g' gimp) in
    if Env.debug env Options.Extreme
    then BU.print2 "Guard from application node %s is %s\n"
                (Print.term_to_string e)
                (Rel.guard_to_string env gres);
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

    if Env.debug env Options.Extreme
    then BU.print1 "Tm_match: expected type of branches is %s\n" (Print.term_to_string res_t);

    let guard_x = S.new_bv (Some e1.pos) c1.res_typ in
    let t_eqns = eqns |> List.map (tc_eqn guard_x env_branches) in
    let c_branches, g_branches =
      let cases, g = List.fold_right (fun (_, f, c, g) (caccum, gaccum) ->
        (f, c)::caccum, Rel.conj_guard g gaccum) t_eqns ([], Rel.trivial_guard) in
      (* bind_cases adds an exhaustiveness check *)
      TcUtil.bind_cases env res_t cases, g
    in

    let cres = TcUtil.bind e1.pos env (Some e1) c1 (Some guard_x, c_branches) in
    let e =
      let mk_match scrutinee =
        (* TODO (KM) : I have the impression that lifting here is useless/wrong : the scrutinee should always be pure... *)
        (* let scrutinee = TypeChecker.Util.maybe_lift env scrutinee c1.eff_name cres.eff_name c1.res_typ in *)
        let branches = t_eqns |> List.map (fun ((pat, wopt, br), _, lc, _) ->
              (pat, wopt, TcUtil.maybe_lift env br lc.eff_name cres.eff_name lc.res_typ ))
        in
        let e = mk (Tm_match(scrutinee, branches)) (Some cres.res_typ.n) top.pos in
        let e = TcUtil.maybe_monadic env e cres.eff_name cres.res_typ in
        //The ascription with the result type is useful for re-checking a term, translating it to Lean etc.
        mk (Tm_ascribed(e, (Inl cres.res_typ, None), Some cres.eff_name)) None e.pos
      in
      //see issue #594: if the scrutinee is impure, then explicitly sequence it with an impure let binding
      //                to protect it from the normalizer optimizing it away
      if TcUtil.is_pure_or_ghost_effect env c1.eff_name
      then mk_match e1
      else
        (* generate a let binding for e1 *)
        let e_match = mk_match (S.bv_to_name guard_x) in
        let lb = {
          lbname=Inl guard_x;
          lbunivs=[];
          lbtyp=c1.res_typ;
          lbeff=Env.norm_eff_name env c1.eff_name;
          lbdef=e1;
        } in
        let e = mk (Tm_let((false, [lb]), SS.close [S.mk_binder guard_x] e_match)) (Some cres.res_typ.n) top.pos in
        TcUtil.maybe_monadic env e cres.eff_name cres.res_typ
    in
    if debug env Options.Extreme
    then BU.print2 "(%s) comp type = %s\n"
                      (Range.string_of_range top.pos) (Print.comp_to_string <| cres.comp());

    e, cres, Rel.conj_guard g1 g_branches

  | Tm_let ((false, [{lbname=Inr _}]), _) ->
    if Env.debug env Options.Low then BU.print1 "%s\n" (Print.term_to_string top);
    check_top_level_let env top

  | Tm_let ((false, _), _) ->
    check_inner_let env top

  | Tm_let ((true, {lbname=Inr _}::_), _) ->
    if Env.debug env Options.Low then BU.print1 "%s\n" (Print.term_to_string top);
    check_top_level_let_rec env top

  | Tm_let ((true, _), _) ->
    check_inner_let_rec env top

and tc_tactic_opt env topt =
    match topt with
    | None -> None
    | Some tactic ->
      let tactic, _, _ = tc_check_tot_or_gtot_term env tactic Common.t_tactic_unit in
      Some tactic
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
    let tc = if Env.should_verify env then Inl t else Inr (U.lcomp_of_comp <| mk_Total t) in
    let is_data_ctor = function
        | Some Data_ctor
        | Some (Record_ctor _) -> true
        | _ -> false in
    if is_data_ctor dc && not(Env.is_datacon env v.v)
    then raise (Error(BU.format1 "Expected a data constructor; got %s" v.v.str, Env.get_range env))
    else value_check_expected_typ env e tc implicits in

  //As a general naming convention, we use e for the term being analyzed and its subterms as e1, e2, etc.
  //We use t and its variants for the type of the term being analyzed
  let env = Env.set_range env e.pos in
  let top = SS.compress e in
  match top.n with
  | Tm_bvar x ->
    failwith (BU.format1 "Impossible: Violation of locally nameless convention: %s" (Print.term_to_string top))

  | Tm_uvar(u, t1) -> //the type of a uvar is given directly with it; we do not recheck the type
    let g = match (SS.compress t1).n with
        | Tm_arrow _ -> Rel.trivial_guard
        | _ -> let imp = ("uvar in term", env, u, top, t1, top.pos) in
               {Rel.trivial_guard with implicits=[imp]} in
//    let g = Rel.trivial_guard in
    value_check_expected_typ env e (Inl t1) g

  | Tm_unknown -> //only occurs where type annotations are missing in source programs
    let r = Env.get_range env in
    let t, _, g0 =
        match Env.expected_typ env with
        | None ->  let k, u = U.type_u () in
                   TcUtil.new_implicit_var "type of user-provided implicit term" r env k
        | Some t -> t, [], Rel.trivial_guard in
    let e, _, g1 = TcUtil.new_implicit_var "user-provided implicit term" r env t in
    e, S.mk_Total t |> U.lcomp_of_comp, (Rel.conj_guard g0 g1)

  | Tm_name x ->
    let t, rng =
        if env.use_bv_sorts
        then x.sort, S.range_of_bv x
        else Env.lookup_bv env x in
    let x = S.set_range_of_bv ({x with sort=t}) rng in
    FStar.TypeChecker.Common.insert_bv x t;
    let e = S.bv_to_name x in
    let e, t, implicits = TcUtil.maybe_instantiate env e t in
    let tc = if Env.should_verify env then Inl t else Inr (U.lcomp_of_comp <| mk_Total t) in
    value_check_expected_typ env e tc implicits

  | Tm_uinst({n=Tm_fvar fv}, us) ->
    let us = List.map (tc_universe env) us in
    let (us', t), range = Env.lookup_lid env fv.fv_name.v in
    if List.length us <> List.length us'
    then raise (Error("Unexpected number of universe instantiations", Env.get_range env))
    else List.iter2 (fun u' u -> match u' with
            | U_unif u'' -> Unionfind.change u'' (Some u)
            | _ -> failwith "Impossible") us' us;
    let fv' = {fv with fv_name={fv.fv_name with ty=t}} in
    let fv' = S.set_range_of_fv fv' range in
    FStar.TypeChecker.Common.insert_fv fv' t;
    let e = S.mk_Tm_uinst (mk (Tm_fvar fv') (Some t.n) e.pos) us in
    check_instantiated_fvar env fv'.fv_name fv'.fv_qual e t

  | Tm_fvar fv ->
    let (us, t), range = Env.lookup_lid env fv.fv_name.v in
    if Env.debug env <| Options.Other "Range"
    then BU.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
            (Print.lid_to_string (lid_of_fv fv))
            (Range.string_of_range e.pos)
            (Range.string_of_range range)
            (Range.string_of_use_range range)
            (Print.term_to_string t);
    let fv' = {fv with fv_name={fv.fv_name with ty=t}} in
    let fv' = S.set_range_of_fv fv' range in
    FStar.TypeChecker.Common.insert_fv fv' t;
    let e = S.mk_Tm_uinst (mk (Tm_fvar fv') (Some t.n) e.pos) us in
    check_instantiated_fvar env fv'.fv_name fv'.fv_qual e t

  | Tm_constant c ->
    let t = tc_constant top.pos c in
    let e = mk (Tm_constant c) (Some t.n) e.pos in
    value_check_expected_typ env e (Inl t) Rel.trivial_guard

  | Tm_arrow(bs, c) ->
    let bs, c = SS.open_comp bs c in
    let env0 = env in
    let env, _ = Env.clear_expected_typ env in
    (* type checking the binders *)
    let bs, env, g, us = tc_binders env bs in
    (* type checking the computation *)
    let c, uc, f = tc_comp env c in
    let e = {U.arrow bs c with pos=top.pos} in
    (* checks the SMT pattern associated with this function is properly defined with regard to context *)
    check_smt_pat env e bs c;
    (* taking the maximum of the universes of the computation and of all binders *)
    let u = S.U_max (uc::us) in
    (* create a universe of level u *)
    let t = mk (Tm_type u) None top.pos in
    let g = Rel.conj_guard g (Rel.close_guard_univs us bs f) in
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
    then BU.print3 "(%s) Checking refinement formula %s; binder is %s\n"
        (Range.string_of_range top.pos) (Print.term_to_string phi) (Print.bv_to_string (fst x));
    let t_phi, _ = U.type_u () in
    let phi, _, f2 = tc_check_tot_or_gtot_term env phi t_phi in
    let e = {U.refine (fst x) phi with pos=top.pos} in
    let t = mk (Tm_type u) None top.pos in
    let g = Rel.conj_guard f1 (Rel.close_guard_univs [u] [x] f2) in
    value_check_expected_typ env0 e (Inl t) g

  | Tm_abs(bs, body, _) ->
    (* in case we use type variables which are implicitly quantified, we add quantifiers here *)
    let bs = TcUtil.maybe_add_implicit_binders env bs in
    if Env.debug env Options.Low
    then BU.print1 "Abstraction is: %s\n" (Print.term_to_string ({top with n=Tm_abs(bs, body, None)}));
    let bs, body = SS.open_term bs body in
    tc_abs env top bs body

  | _ ->
    failwith (BU.format2 "Unexpected value: %s (%s)" (Print.term_to_string top) (Print.tag_of_term top))

and tc_constant r (c:sconst) : typ =
     match c with
      | Const_unit -> t_unit
      | Const_bool _ -> t_bool
      | Const_int (_, None) -> t_int
      | Const_int (_, Some _) -> failwith "machine integers should be desugared"
      | Const_string _ -> t_string
      | Const_float _ -> t_float
      | Const_char _ -> t_char
      (* TODO (KM) : Try to change this to U.ktype1 *)
      (* (because that's the minimal universe level of the WP) *)
      (* and see how much code breaks *)
      | Const_effect -> U.ktype0 //NS: really?
      | Const_range _ -> t_range

      | _ -> raise (Error("Unsupported constant", r))


(************************************************************************************************************)
(* Type-checking computation types                                                                          *)
(************************************************************************************************************)
and tc_comp env c : comp                                      (* checked version of c                       *)
                  * universe                                  (* universe of c.result_typ                   *)
                  * guard_t =                                 (* logical guard for the well-formedness of c *)
  let c0 = c in
  match c.n with
    | Total (t, _) ->
      let k, u = U.type_u () in
      let t, _, g = tc_check_tot_or_gtot_term env t k in
      mk_Total' t (Some u), u, g

    | GTotal (t, _) ->
      let k, u = U.type_u () in
      let t, _, g = tc_check_tot_or_gtot_term env t k in
      mk_GTotal' t (Some u), u, g

    | Comp c ->
      let head = S.fvar c.effect_name Delta_constant None in
      let head = match c.comp_univs with
         | [] -> head
         | us -> S.mk (Tm_uinst(head, us)) None c0.pos in
      let tc = mk_Tm_app head ((as_arg c.result_typ)::c.effect_args) None c.result_typ.pos in
      let tc, _, f = tc_check_tot_or_gtot_term env tc S.teff in
      let head, args = U.head_and_args tc in
      let comp_univs = match (SS.compress head).n with
        | Tm_uinst(_, us) -> us
        | _ -> [] in
      let _, args = U.head_and_args tc in
      let res, args = List.hd args, List.tl args in
      let flags, guards = c.flags |> List.map (function
        | DECREASES e ->
            let env, _ = Env.clear_expected_typ env in
            let e, _, g = tc_tot_or_gtot_term env e in
            DECREASES e, g
        | f -> f, Rel.trivial_guard) |> List.unzip in
      let u = env.universe_of env (fst res) in
      let c = mk_Comp ({c with
          comp_univs=comp_univs;
          result_typ=fst res;
          effect_args=args}) in
      let u_c =
        match Env.effect_repr env c u with
        | None -> u
        | Some tm -> env.universe_of env tm in
      c, u_c, List.fold_left Rel.conj_guard f guards

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
        | U_name x  -> u
            (* TODO : Is that really okay ? (any free variable should be automatically bound at top-level) *)
            // if env.use_bv_sorts || Env.lookup_univ env x
            // then u
            // else raise (Error (BU.format1 "Universe variable '%s' not found" x.idText, Env.get_range env))
   in if env.lax_universes then U_zero
      else match u with
           | U_unknown -> U.type_u () |> snd
           | _ -> aux u

(* Several complex cases from the main type-checker are factored in to separate functions below *)

(*******************************************************************************************************************)
(* Type-checking abstractions, aka lambdas                                                                         *)
(*    top = fun bs -> body, although bs and body must already be opened                                            *)
(*******************************************************************************************************************)
and tc_abs env (top:term) (bs:binders) (body:term) : term * lcomp * guard_t =
    let fail :string -> typ -> 'a = fun msg t ->
        raise (Error(Err.expected_a_term_of_type_t_got_a_function env msg t top, top.pos)) in

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
                      raise (Error(BU.format1 "Inconsistent implicit argument annotation on argument %s" (Print.bv_to_string hd),
                                                  S.range_of_bv hd))
                    | _ -> ()
               end;
               (* since binders depend on previous ones, we accumulate a substitution *)
               let expected_t = SS.subst subst hd_expected.sort in
               let t, g = match (U.unmeta hd.sort).n with
                    | Tm_unknown -> expected_t, g
                    (* in case we have an annotation on both implementation and declaration, we:
                      * 1) type check the implementation type
                      * 2) add an extra guard that the two types must be equal (use_eq will be used in Rel.teq
                    *)
                    | _ ->
                      if Env.debug env Options.High then BU.print1 "Checking binder %s\n" (Print.bv_to_string hd);
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
                let env = push_binding env b in
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
        * option<term>        (* a tactic to apply when checking the expected computation type *)
        * Env.env             (* environment for the body *)
        * term                (* the body itself *)
        * guard_t)            (* accumulated guard from checking the binders *)
    =
      match t0 with
      | None -> (* no expected type; just build a function type from the binders in the term *)
          (* env.letrecs are the current letrecs we are checking *)
          let _ = match env.letrecs with
              | [] -> ()
              | _ -> failwith "Impossible: Can't have a let rec annotation but no expected type"
          in
          let bs, envbody, g, _ = tc_binders env bs in
          let copt, tacopt, body, g = match (SS.compress body).n with
              | Tm_ascribed(e, (Inr c, tacopt), _) ->
                let c, _, g' = tc_comp envbody c in
                Some c, tc_tactic_opt envbody tacopt, body, Rel.conj_guard g g'
              | _ -> None, None, body, g
          in
          None, bs, [], copt, tacopt, envbody, body, g

      | Some t ->
          let t = SS.compress t in
          let rec as_function_typ norm t =
              match (SS.compress t).n with
              (* we are type checking abs so all cases except arrow are required for definitional equality *)
              | Tm_uvar _
              | Tm_app({n=Tm_uvar _}, _) ->
                (* expected a uvar; build a function type from the term and unify with it *)
                let _ = match env.letrecs with | [] -> () | _ -> failwith "Impossible" in
                let bs, envbody, g, _ = tc_binders env bs in
                let envbody, _ = Env.clear_expected_typ envbody in
                Some (t, true), bs, [], None, None, envbody, body, g

              (* CK: add this case since the type may be f:(a -> M b wp){φ}, in which case I drop the refinement *)
              (* NS: 07/21 dropping the refinement is not sound; we need to check that f validates phi. See Bug #284 *)
              | Tm_refine (b, _) ->
                let _, bs, bs', copt, tacopt, env, body, g = as_function_typ norm b.sort in
                Some (t, false), bs, bs', copt, tacopt, env, body, g

              | Tm_arrow(bs_expected, c_expected) ->
                let bs_expected, c_expected = SS.open_comp bs_expected c_expected in
                  (* Two main interesting bits here;
                      1. The expected type may have
                            a. more immediate binders, whereas the function may itself return a function
                            b. fewer immediate binders, meaning that the function type is explicitly curried
                      2. If the function is a let-rec and it is to be total, then we need to add termination checks.
                  *)
                let check_actuals_against_formals env bs bs_expected =
                    let rec handle_more (env, bs, more, guard, subst) c_expected = match more with
                      | None -> //number of binders match up
                        env, bs, guard, SS.subst_comp subst c_expected

                      | Some (Inr more_bs_expected) -> //more formal parameters; expect the body to return a total function
                        let c = S.mk_Total (U.arrow more_bs_expected c_expected) in
                        env, bs, guard, SS.subst_comp subst c

                      | Some (Inl more_bs) ->  //more actual args
                        let c = SS.subst_comp subst c_expected in
                        (* the expected type is explicitly curried *)
                        if U.is_named_tot c then
                          let t = N.unfold_whnf env (U.comp_result c) in
                          match t.n with
                          | Tm_arrow(bs_expected, c_expected) ->
                            let bs_expected, c_expected = SS.open_comp bs_expected c_expected in
                            let (env, bs', more, guard', subst) = check_binders env more_bs bs_expected in
                            handle_more (env, bs@bs', more, Rel.conj_guard guard guard', subst) c_expected
                          | _ -> fail (BU.format1 "More arguments than annotated type (%s)" (Print.term_to_string t)) t
                        else fail "Function definition takes more arguments than expected from its annotated type" t
                      in

                      handle_more (check_binders env bs bs_expected) c_expected
                in

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
                      (envbody, [])
                in

                let envbody, bs, g, c = check_actuals_against_formals env bs bs_expected in
                let envbody, letrecs = if Env.should_verify env then mk_letrec_env envbody bs c else envbody, [] in
                let envbody = Env.set_expected_typ envbody (U.comp_result c) in
                Some (t, false), bs, letrecs, Some c, None, envbody, body, g

              | _ -> (* expected type is not a function;
                        try normalizing it first;
                        otherwise synthesize a type and check it against the given type *)
                if not norm
                then as_function_typ true (N.unfold_whnf env t)
                else let _, bs, _, c_opt, tacopt, envbody, body, g = expected_function_typ env None body in
                      Some (t, false), bs, [], c_opt, tacopt, envbody, body, g in
          as_function_typ false t
    in

    (* whether to try first to use unification for solving sub-typing constraints or only propagate to the SMT solver *)
    let use_eq = env.use_eq in
    (* topt is the expected type of the expression obtained from the env *)
    let env, topt = Env.clear_expected_typ env in

    if Env.debug env Options.High
    then BU.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
          (match topt with | None -> "None" | Some t -> Print.term_to_string t)
          (if env.top_level then "true" else "false");

    let tfun_opt, bs, letrec_binders, c_opt, tacopt, envbody, body, g = expected_function_typ env topt body in
    let body, cbody, guard_body = tc_term ({envbody with top_level=false; use_eq=use_eq}) body in

    let guard_body =  //we don't abstract over subtyping constraints; so solve them now
        Rel.solve_deferred_constraints envbody guard_body in

    if Env.debug env <| Options.Other "Implicits"
    then BU.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
        (string_of_int <| List.length guard_body.implicits)
        (Print.comp_to_string <| cbody.comp());

    let body, cbody, guard = check_expected_effect ({envbody with use_eq=use_eq}) c_opt (body, cbody.comp()) in
    let guard = Rel.conj_guard guard_body guard in
//    let guard = match tacopt with
//                | None -> guard
//                | Some tac -> Rel.map_guard guard (Common.mk_by_tactic tac) in
    let guard = if env.top_level || not(Env.should_verify env)
                then Rel.discharge_guard envbody (Rel.conj_guard g guard)
                else let guard = Rel.close_guard env (bs@letrec_binders) (Rel.conj_guard g guard) in
                     guard in

    let tfun_computed = U.arrow bs cbody in
    let e = U.abs bs body (Some (dflt cbody c_opt |> U.lcomp_of_comp |> Inl)) in
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
                        else TcUtil.check_and_ascribe env e tfun_computed t
                    in
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
    if debug env Options.High then BU.print2 "(%s) Type of head is %s\n" (Range.string_of_range head.pos) (Print.term_to_string thead);

    (* given |- head : chead | ghead
           where head is a computation returning a function of type (bs0@bs -> cres)
           and the paramters bs0 have been applied to the arguments in arg_comps_rev (in reverse order)
        and args_comps_rev = [(argn, _, cn), ..., (arg0, _, c0)]


        This function builds
            head arg0 ... argn : M (bs -> cres) wp
        where in the case where
            bs = [], i.e., a full application
                M, wp is built using
                         bind chead (bind c0 (bind c1 ... (bind cn cres)))
            bs = _::_, i.e., a partial application
                M, wp is built using
                         bind chead (bind c0 (bind c1 ... (bind cn (Tot (bs -> cres))))
    *)
    let monadic_application
      (head, chead, ghead, cres)
      subst
      (arg_comps_rev:list<(arg * option<bv> * lcomp)>)
      arg_rets_rev
      guard
      fvs
      bs
        : term   //application of head to args
        * lcomp  //its computation type
        * guard_t //and whatever guard remains
    =
      let rt = check_no_escape (Some head) env fvs cres.res_typ in
      let cres = {cres with res_typ=rt} in
      let cres, guard =
          match bs with
          | [] -> (* full app *)
              let cres = TcUtil.subst_lcomp subst cres in
              (* If we have f e1 e2
                  where e1 or e2 is impure but f is a pure function,
                  then refine the result to be equal to f x1 x2,
                  where xi is the result of ei. (See the last two tests in examples/unit-tests/unit1.fst)
              *)
              let g = Rel.conj_guard ghead guard in
              cres, g

          | _ ->  (* partial app *)
              let g = Rel.conj_guard ghead guard |> Rel.solve_deferred_constraints env in
              U.lcomp_of_comp <| mk_Total  (SS.subst subst <| U.arrow bs (cres.comp())), g
      in
      if debug env Options.Low then BU.print1 "\t Type of result cres is %s\n" (Print.lcomp_to_string cres);

      (* Note: The outargs are in reverse order. e.g., f e1 e2 e3, we have *)
      (* outargs = [(e3, _, c3); (e2; _; c2); (e1; _; c1)] *)
      (* We build comp = bind chead (bind c1 (bind c2 (bind c3 cres))) *)
      (* The typing rule for monadic application should be something like *)

      (* G |- head : chead      G |- ei :ci                *)
      (* ------------------------------------------------- *)
      (*  G |- let xhead = lift_{chead}^{comp} head in     *)
      (*       let x1 = lift_{ci}^{comp} e1 in             *)
      (*       ...                                         *)
      (*       lift_{cres}^{comp} (xhead x1 ... xn) : cres *)

      (* where chead = b1 -> ... bn -> cres *)

      (* if cres is pure or ghost, we augment it with a return
           i.e., in the case where the head f is a pure or ghost function,
                 treat the application as (e e1 e2 .. en) as
                    f <-- e;
                    x1 <-- e1; ...
                    xn <-- en;
                    return (f x1 ... xn)
           1. The return at the end enhances f's result type with an equality
                e.g., if (f : xs -> Tot t)
                the type of the application becomes
                      Pure t (ensures (fun y -> y = f x1 ...xn))
           2. It's VERY important that the return is inserted using the bound names x1...xn.
              Previously, in case e1..en were pure, we were inserting
                      Pure t (ensures (fun y -> y = f e1 ...en))
              But this leads to a massive blow up in the size of generated VCs (cf issue #971)
              arg_rets below are those xn...x1 bound variables
       *)
      let cres =
        if Util.is_pure_or_ghost_lcomp cres
        then let term = S.mk_Tm_app head (List.rev arg_rets_rev) None head.pos in
             TcUtil.maybe_assume_result_eq_pure_term env term cres
        else cres
      in

      (* 1. We compute the final computation type comp  *)
      let comp =
        List.fold_left
          (fun out_c ((e, q), x, c) ->
              if Util.is_pure_or_ghost_lcomp c
              then TcUtil.bind e.pos env (Some e) c (x, out_c)
              else TcUtil.bind e.pos env None c (x, out_c))
          cres
          arg_comps_rev
      in
      let comp = TcUtil.bind head.pos env None chead (None, comp) in

      (* TODO : This is a really syntactic criterion to check if we can evaluate *)
      (* applications left-to-right, can we do better ? *)
      let shortcuts_evaluation_order =
        match (SS.compress head).n with
        | Tm_fvar fv ->
			     S.fv_eq_lid fv Syntax.Const.op_And ||
			     S.fv_eq_lid fv Syntax.Const.op_Or
        | _ -> false
      in

      let app =
        if shortcuts_evaluation_order then
          (* Question (NS): Why is this even possible here?
                            I thought this would be taken care of in
                            check_short_circuit_args
          *)
          (* If the head is shortcutting we cannot hoist its arguments *)
          (* Leaving it `as is` is a little dubious, it would fail whenever we try to reify it *)
          let args = List.fold_left (fun args (arg, _, _) -> arg::args) [] arg_comps_rev in
          let app = mk_Tm_app head args (Some comp.res_typ.n) r in
          let app = TcUtil.maybe_lift env app cres.eff_name comp.eff_name comp.res_typ in
          TcUtil.maybe_monadic env app comp.eff_name comp.res_typ

        else
          (* 2. For each monadic argument (including the head of the application) we introduce *)
          (*    a fresh variable and lift the actual argument to comp.       *)
          let lifted_args, head, args =
            let map_fun ((e, q), _ , c) =
               if U.is_pure_or_ghost_lcomp c
               then None, (e, q)
               else let x = S.new_bv None c.res_typ in
                    let e = TcUtil.maybe_lift env e c.eff_name comp.eff_name c.res_typ in
                    Some (x, c.eff_name, c.res_typ, e), (S.bv_to_name x, q)
            in
            let lifted_args, reverse_args =
                List.split <| List.map map_fun ((as_arg head, None, chead)::arg_comps_rev)
            in
            lifted_args, fst (List.hd reverse_args), List.rev (List.tl reverse_args)
          in

          (* 3. We apply the (non-monadic) head to the non-monadic arguments, lift the *)
          (*    result to comp and then bind each monadic arguments to close over the *)
          (*    variables introduces at step 2. *)
          let app = mk_Tm_app head args (Some comp.res_typ.n) r in
          let app = TcUtil.maybe_lift env app cres.eff_name comp.eff_name comp.res_typ in
          let app = TcUtil.maybe_monadic env app comp.eff_name comp.res_typ in
          let bind_lifted_args e = function
            | None -> e
            | Some (x, m, t, e1) ->
              let lb = U.mk_letbinding (Inl x) [] t m e1 in
              let letbinding = mk (Tm_let ((false, [lb]), SS.close [S.mk_binder x] e)) None e.pos in
              mk (Tm_meta(letbinding, Meta_monadic(m, comp.res_typ))) None e.pos
          in
          List.fold_left bind_lifted_args app lifted_args
      in

      (* Each conjunct in g is already labeled *)
      let comp, g = TcUtil.strengthen_precondition None env app comp guard in
      app, comp, g
    in

    let rec tc_args (head_info:(term * lcomp * guard_t * lcomp)) //the head of the application, its lcomp and guard, returning a bs -> cres
                    (subst,   (* substituting actuals for formals seen so far, when actual is pure *)
                     outargs, (* type-checked actual arguments, so far; in reverse order *)
                     arg_rets,(* The results of each argument at the logic level, in reverse order *)
                     g,       (* conjoined guard formula for all the actuals *)
                     fvs)     (* unsubstituted formals, to check that they do not occur free elsewhere in the type of f *)
                     bs       (* formal parameters *)
                     args     (* remaining actual arguments *) : (term * lcomp * guard_t) =
        match bs, args with
        | (x, Some (Implicit _))::rest, (_, None)::_ -> (* instantiate an implicit arg *)
            let t = SS.subst subst x.sort in
            let t = check_no_escape (Some head) env fvs t in
            let varg, _, implicits = TcUtil.new_implicit_var "Instantiating implicit argument in application" head.pos env t in //new_uvar env t in
            let subst = NT(x, varg)::subst in
            let arg = varg, as_implicit true in
            tc_args head_info (subst, (arg, None, S.mk_Total t |> U.lcomp_of_comp)::outargs, arg::arg_rets, Rel.conj_guard implicits g, fvs) rest args

        | (x, aqual)::rest, (e, aq)::rest' -> (* a concrete argument *)
            let _ =
                match aqual, aq with
                | Some (Implicit _), Some (Implicit _)
                | None, None
                | Some Equality, None -> ()
                | _ -> raise (Error("Inconsistent implicit qualifier", e.pos)) in
            let targ = SS.subst subst x.sort in
            let x = {x with sort=targ} in
            if debug env Options.Extreme then  BU.print1 "\tType of arg (after subst) = %s\n" (Print.term_to_string targ);
            let targ = check_no_escape (Some head) env fvs targ in
            let env = Env.set_expected_typ env targ in
            let env = {env with use_eq=is_eq aqual} in
            if debug env Options.High then  BU.print3 "Checking arg (%s) %s at type %s\n" (Print.tag_of_term e) (Print.term_to_string e) (Print.term_to_string targ);
            let e, c, g_e = tc_term env e in
            let g = Rel.conj_guard g g_e in
//                if debug env Options.High then BU.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" (guard_to_string env g_e) (guard_to_string env g);
            let arg = e, aq in
            let xterm = S.as_arg (S.bv_to_name x) in
            if U.is_tot_or_gtot_lcomp c //early in prims, Tot and GTot are primitive, not defined in terms of Pure/Ghost yet
            || TcUtil.is_pure_or_ghost_effect env c.eff_name
            then let subst = maybe_extend_subst subst (List.hd bs) e in
                 tc_args head_info (subst, (arg, Some x, c)::outargs, xterm::arg_rets, g, fvs) rest rest'
            else tc_args head_info (subst, (arg, Some x, c)::outargs, xterm::arg_rets, g, x::fvs) rest rest'

        | _, [] -> (* no more args; full or partial application *)
            monadic_application head_info subst outargs arg_rets g fvs bs

        | [], arg::_ -> (* too many args, except maybe c returns a function *)
            let head, chead, ghead = monadic_application head_info subst outargs arg_rets g fvs [] in
            let rec aux norm tres =
                let tres = SS.compress tres |> U.unrefine in
                match tres.n with
                    | Tm_arrow(bs, cres') ->
                        let bs, cres' = SS.open_comp bs cres' in
                        let head_info = (head, chead, ghead, U.lcomp_of_comp cres') in
                        if debug env Options.Low
                        then BU.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n"
                            (Range.string_of_range tres.pos);
                        tc_args head_info ([], [], [], Rel.trivial_guard, []) bs args
                    | _ when not norm ->
                        aux true (N.unfold_whnf env tres)
                    | _ -> raise (Error(BU.format2 "Too many arguments to function of type %s; got %s arguments"
                                            (N.term_to_string env thead) (BU.string_of_int n_args), argpos arg)) in
            aux false chead.res_typ
    in //end tc_args

    let rec check_function_app tf =
       match (N.unfold_whnf env tf).n with
        | Tm_uvar _
        | Tm_app({n=Tm_uvar _}, _) ->
            let rec tc_args env args : (Syntax.args * list<(Range.range * lcomp)> * guard_t) = match args with
                | [] -> ([], [], Rel.trivial_guard)
                | (e, imp)::tl ->
                    let e, c, g_e = tc_term env e in
                    let args, comps, g_rest = tc_args env tl in
                    (e, imp)::args, (e.pos, c)::comps, Rel.conj_guard g_e g_rest in
            (* Infer: t1 -> ... -> tn -> C ('u x1...xm),
                    where ti are the result types of each arg
                    and   xi are the free type/term variables in the environment
               where C = Tot,
                except when Options.ml_ish(), where C = ML (for compatibility with ML)
            *)
            let args, comps, g_args = tc_args env args in
            let bs = null_binders_of_tks (comps |> List.map (fun (_, c) -> c.res_typ, None)) in
            let ml_or_tot t r =
                if Options.ml_ish ()
                then U.ml_comp t r
                else S.mk_Total t
            in
            let cres = ml_or_tot (TcUtil.new_uvar env (U.type_u () |> fst)) r in
            let bs_cres = U.arrow bs cres in
            if Env.debug env <| Options.Extreme
            then BU.print3 "Forcing the type of %s from %s to %s\n"
                            (Print.term_to_string head)
                            (Print.term_to_string tf)
                            (Print.term_to_string bs_cres);
            Rel.force_trivial_guard env <| Rel.teq env tf bs_cres;
            let comp =
                  List.fold_right (fun (r1, c) out ->
                       TcUtil.bind r1 env None c (None, out))
                  ((head.pos, chead)::comps)
                  (U.lcomp_of_comp <| cres) in
            mk_Tm_app head args (Some comp.res_typ.n) r, comp, Rel.conj_guard ghead g_args

        | Tm_arrow(bs, c) ->
            let bs, c = SS.open_comp bs c in
            let head_info = head, chead, ghead, U.lcomp_of_comp c in
            tc_args head_info ([], [], [], Rel.trivial_guard, []) bs args

        | Tm_refine (bv,_) ->
            check_function_app bv.sort

        | Tm_ascribed (t, _, _) ->
            check_function_app t

        | _ ->
            raise (Error(Err.expected_function_typ env tf, head.pos)) in

    check_function_app thead

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
        | Tm_arrow(bs, c) when (U.is_total_comp c && List.length bs=List.length args) ->
          let res_t = U.comp_result c in
          let args, guard, ghost = List.fold_left2 (fun (seen, guard, ghost) (e, aq) (b, aq') ->
                if aq<>aq' then raise (Error("Inconsistent implicit qualifiers", e.pos));
                let e, c, g = tc_check_tot_or_gtot_term env e b.sort in //NS: this forbids stuff like !x && y, maybe that's ok
                let short = TcUtil.short_circuit head seen in
                let g = Rel.imp_guard (Rel.guard_of_guard_formula short) g in
                let ghost = ghost
                          || (not (U.is_total_lcomp c)
                              && not (TcUtil.is_pure_effect env c.eff_name)) in
                seen@[as_arg e], Rel.conj_guard guard g, ghost) ([], g_head, false) args bs in
          let e = mk_Tm_app head args (Some res_t.n) r  in
          let c = if ghost then S.mk_GTotal res_t |> U.lcomp_of_comp else U.lcomp_of_comp c in
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
    then BU.print2 "Pattern %s elaborated to %s\n" (Print.pat_to_string p0) (Print.pat_to_string p);
    let pat_env = List.fold_left Env.push_bv env pat_bvs in
    let env1, _ = Env.clear_expected_typ pat_env in
    let env1 = {env1 with Env.is_pattern=true} in  //just a flag for a better error message
    let expected_pat_t = Rel.unrefine env pat_t in
    let exps, norm_exps = exps |> List.map (fun e ->
        if Env.debug env Options.High
        then BU.print2 "Checking pattern expression %s against expected type %s\n" (Print.term_to_string e) (Print.term_to_string pat_t);

        let e, lc, g =  tc_term env1 e in //only keep the unification/subtyping constraints; discard the logical guard for patterns
                                          //Q: where is it being discarded? A: we only use lc.res_typ below, and forget abouts its WP
        if Env.debug env Options.High
        then BU.print2 "Pre-checked pattern expression %s at type %s\n" (N.term_to_string env e) (N.term_to_string env lc.res_typ);

        let g' = Rel.teq env lc.res_typ expected_pat_t in
        let g = Rel.conj_guard g g' in
        let _ = Rel.discharge_guard env ({g with guard_f=Trivial}) |> Rel.resolve_implicits in
        let e' = N.normalize [N.Beta] env e in
        let uvars_to_string uvs = uvs |> BU.set_elements |> List.map (fun (u, _) -> Print.uvar_to_string u) |> String.concat ", " in
        let uvs1 = Free.uvars e' in
        let uvs2 = Free.uvars expected_pat_t in
        if not <| BU.set_is_subset_of uvs1 uvs2
        then (let unresolved = BU.set_difference uvs1 uvs2 |> BU.set_elements in
              raise (Error(BU.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;\
                                         Variables {%s} were unresolved; please bind them explicitly"
                                    (N.term_to_string env e')
                                    (N.term_to_string env expected_pat_t)
                                    (unresolved |> List.map (fun (u, _) -> Print.uvar_to_string u) |> String.concat ", "), p.p)));

        if Env.debug env Options.High
        then BU.print1 "Done checking pattern expression %s\n" (N.term_to_string env e);

        //explicitly return e here, not its normal form, since pattern decoration relies on it
        e,e') |> List.unzip in
    let p = TcUtil.decorate_pattern env p exps in
    p, pat_bvs, pat_env, exps, norm_exps
  in
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
        if Env.should_verify env
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
        | Some w -> Some <| U.mk_eq2 U_zero U.t_bool w Const.exp_true_bool in

  (* 5 (a). Build equality conditions between the pattern and the scrutinee                                   *)
  (*   (b). Weaken the VCs of the branch and when clause with the equalities from 5(a) and the when condition *)
  (*   (c). Close the VCs so that they no longer have the pattern-bound variables occurring free in them      *)
  let c, g_when, g_branch =

    (* (a) eqs are equalities between the scrutinee and the pattern *)
    let eqs =
        if not (Env.should_verify env)
        then None
        else disj_exps |> List.fold_left (fun fopt e ->
                let e = SS.compress e in
                match e.n with
                    | Tm_uvar _
                    | Tm_constant _
                    | Tm_fvar _ -> fopt (* Equation for non-binding forms are handled with the discriminators below *)
                    | _ ->
                      let clause = U.mk_eq2 (env.universe_of env pat_t) pat_t scrutinee_tm e in
                      match fopt with
                        | None -> Some clause
                        | Some f -> Some <| U.mk_disj clause f) None in

    let c, g_branch = TcUtil.strengthen_precondition None env branch_exp c g_branch in
    //g_branch is trivial, its logical content is now incorporated within c

    (* (b) *)
    let c_weak, g_when_weak =
     match eqs, when_condition with
      | _ when not (Env.should_verify env) ->
        c, g_when

      | None, None ->
        c, g_when

      | Some f, None ->
        let gf = NonTrivial f in
        let g = Rel.guard_of_guard_formula gf in
        TcUtil.weaken_precondition env c gf,
        Rel.imp_guard g g_when

      | Some f, Some w ->
        let g_f = NonTrivial f in
        let g_fw = NonTrivial (U.mk_conj f w) in
        TcUtil.weaken_precondition env c g_fw,
        Rel.imp_guard (Rel.guard_of_guard_formula g_f) g_when

      | None, Some w ->
        let g_w = NonTrivial w in
        let g = Rel.guard_of_guard_formula g_w in
        TcUtil.weaken_precondition env c g_w,
        g_when in

    (* (c) *)
    let binders = List.map S.mk_binder pat_bvs in
    TcUtil.close_lcomp env pat_bvs c_weak,
    Rel.close_guard env binders g_when_weak,
    g_branch
  in

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
      if not (Env.should_verify env)
      then U.t_true
      else (* 6 (a) *)
          let rec build_branch_guard scrutinee_tm pat_exp : list<typ> =
            let discriminate scrutinee_tm f =
                if List.length (snd (Env.datacons_of_typ env (Env.typ_of_datacon env f.v))) > 1
                then
                    let discriminator = U.mk_discriminator f.v in
                    match Env.try_lookup_lid env discriminator with
                        | None -> []  // We don't use the discriminator if we are typechecking it
                        | _ ->
                            let disc = S.fvar discriminator Delta_equational None in
                            let disc = mk_Tm_app disc [as_arg scrutinee_tm] None scrutinee_tm.pos in
                            [U.mk_eq2 U_zero U.t_bool disc Const.exp_true_bool]
                else []
            in

            let fail () =
                failwith (BU.format3 "tc_eqn: Impossible (%s) %s (%s)"
                                            (Range.string_of_range pat_exp.pos)
                                            (Print.term_to_string pat_exp)
                                            (Print.tag_of_term pat_exp))  in

            let rec head_constructor t = match t.n with
                | Tm_fvar fv -> fv.fv_name
                | Tm_uinst(t, _) -> head_constructor t
                | _ -> fail () in

            let pat_exp = SS.compress pat_exp |> U.unmeta in
            match pat_exp.n with
                | Tm_uvar _
                | Tm_app({n=Tm_uvar _}, _)
                | Tm_name _
                | Tm_constant Const_unit -> []
                | Tm_constant c -> [U.mk_eq2 U_zero (tc_constant pat_exp.pos c) scrutinee_tm pat_exp]
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
                | _ -> [] //a non-pattern sub-term: must be from a dot pattern
          in

          (* 6 (b) *)
          let build_and_check_branch_guard scrutinee_tm pat =
             if not (Env.should_verify env)
             then TcUtil.fvar_const env Const.true_lid //if we're not verifying, then don't even bother building it
             else let t = U.mk_conj_l <| build_branch_guard scrutinee_tm pat in
                  let k, _ = U.type_u() in
                  let t, _, _ = tc_check_tot_or_gtot_term scrutinee_env t k in //NS: discarding the guard here means that the VC is not fully type-checked and may contain unresolved unification variables, e.g. FIXME!
                  t in

          (* 6 (c) *)
         let branch_guard = norm_disj_exps |> List.map (build_and_check_branch_guard scrutinee_tm) |> U.mk_disj_l  in

          (* 6 (d) *)
         let branch_guard = match when_condition with
            | None -> branch_guard
            | Some w -> U.mk_conj branch_guard w in

          branch_guard
  in

  let guard = Rel.conj_guard g_when g_branch in

  if Env.debug env Options.High
  then BU.print1 "Carrying guard from match: %s\n" <| guard_to_string env guard;

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
            then g1, N.reduce_uvar_solutions env e1, univ_vars, c1
            else let g1 = Rel.solve_deferred_constraints env g1 |> Rel.resolve_implicits in
                 assert (univ_vars = []) ;
                 let _, univs, e1, c1 = List.hd (TcUtil.generalize env [lb.lbname, e1, c1.comp()]) in
                 g1, e1, univs, U.lcomp_of_comp c1
         in

         (* Check that it doesn't have a top-level effect; warn if it does *)
         let e2, c1 =
            if Env.should_verify env
            then
                let ok, c1 = TcUtil.check_top_level env g1 c1 in //check that it has no effect and a trivial pre-condition
                if ok
                then e2, c1
                else (Errors.warn (Env.get_range env) Err.top_level_effect;
                      mk (Tm_meta(e2, Meta_desugared Masked_effect)) None e2.pos, c1) //and tag it as masking an effect
            else //even if we're not verifying, still need to solve remaining unification/subtyping constraints
                 let _ = Rel.force_trivial_guard env g1 in
                 let c = c1.comp () |> N.normalize_comp [N.Beta] env in
                 let e2 = if Util.is_pure_comp c
                          then e2
                          else mk (Tm_meta(e2, Meta_desugared Masked_effect)) None e2.pos in
                 e2, c
         in


         (* the result has the same effect as c1, except it returns unit *)
         let cres = Env.null_wp_for_eff env (U.comp_effect_name c1) U_zero Common.t_unit in

         e2.tk := Some (Common.t_unit.n);

(*close*)let lb = U.close_univs_and_mk_letbinding None lb.lbname univ_vars (U.comp_result c1) (U.comp_effect_name c1) e1 in
         mk (Tm_let((false, [lb]), e2))
            (Some (Common.t_unit.n))
            e.pos,
         U.lcomp_of_comp cres,
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
       let x = {BU.left lb.lbname with sort=c1.res_typ} in
       let xb, e2 = SS.open_term [S.mk_binder x] e2 in
       let xbinder = List.hd xb in
       let x = fst xbinder in
       let e2, c2, g2 = tc_term (Env.push_bv env x) e2 in
       let cres = TcUtil.bind e1.pos env (Some e1) c1 (Some x, c2) in
       let e1 = TcUtil.maybe_lift env e1 c1.eff_name cres.eff_name c1.res_typ in
       let e2 = TcUtil.maybe_lift env e2 c2.eff_name cres.eff_name c2.res_typ in
       let lb = U.mk_letbinding (Inl x) [] c1.res_typ c1.eff_name e1 in
       let e = mk (Tm_let((false, [lb]), SS.close xb e2)) (Some cres.res_typ.n) e.pos in
       let e = TcUtil.maybe_monadic env e cres.eff_name cres.res_typ in
       let x_eq_e1 = NonTrivial <| U.mk_eq2 (env.universe_of env c1.res_typ) c1.res_typ (S.bv_to_name x) e1 in
       let g2 = Rel.close_guard env xb
                      (Rel.imp_guard (Rel.guard_of_guard_formula x_eq_e1) g2) in
       let guard = Rel.conj_guard g1 g2 in

       if Option.isSome (Env.expected_typ env)
       then (let tt = Env.expected_typ env |> Option.get in
             if Env.debug env <| Options.Other "Exports"
             then BU.print2 "Got expected type from env %s\ncres.res_typ=%s\n"
                        (Print.term_to_string tt)
                        (Print.term_to_string cres.res_typ);
             e, cres, guard)
       else (* no expected type; check that x doesn't escape it's scope *)
            (let t = check_no_escape None env [x] cres.res_typ in
             if Env.debug env <| Options.Other "Exports"
             then BU.print2 "Checked %s has no escaping types; normalized to %s\n"
                        (Print.term_to_string cres.res_typ)
                        (Print.term_to_string t);
             e, ({cres with res_typ=t}), guard)

    | _ -> failwith "Impossible"

(******************************************************************************)
(* top-level let rec's may be generalized, if they are not annotated          *)
(******************************************************************************)
and check_top_level_let_rec env top =
    let env = instantiate_both env in
    match top.n with
        | Tm_let((true, lbs), e2) ->
           (* replace bound variables in terms and of universes with new names (free variables) *)
(*open*)   let lbs, e2 = SS.open_let_rec lbs e2 in

           (* expected types for top level definitions are stored in the lbs and we therefore just
            * remove previous, unrelated, expected type in env
            * the expected type is defined within lbs
            * *)
           let env0, topt = Env.clear_expected_typ env in
           let lbs, rec_env = build_let_rec_env true env0 lbs in
           (* now we type check each let rec *)
           let lbs, g_lbs = check_let_recs rec_env lbs in
           let g_lbs = Rel.solve_deferred_constraints env g_lbs |> Rel.resolve_implicits in

           let all_lb_names = lbs |> List.map (fun lb -> right lb.lbname) |> Some in

           let lbs =
              if not env.generalize
              then lbs |> List.map (fun lb ->
            (* TODO : Should we gather the fre univnames ? e.g. (TcUtil.gather_free_univnames env e1)@lb.lbunivs *)
                    let lbdef = N.reduce_uvar_solutions env lb.lbdef in
                    if lb.lbunivs = []
                    then lb
                    else U.close_univs_and_mk_letbinding all_lb_names lb.lbname lb.lbunivs lb.lbtyp lb.lbeff lbdef)
              else let ecs = TcUtil.generalize env (lbs |> List.map (fun lb ->
                                lb.lbname,
                                lb.lbdef,
                                S.mk_Total lb.lbtyp)) in
                   ecs |> List.map (fun (x, uvs, e, c) ->
                      U.close_univs_and_mk_letbinding all_lb_names x uvs (U.comp_result c) (U.comp_effect_name c) e) in

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

          let env, lbs = lbs |> BU.fold_map (fun env lb ->
            let x = {left lb.lbname with sort=lb.lbtyp} in
            let lb = {lb with lbname=Inl x} in
            let env = Env.push_let_binding env lb.lbname ([], lb.lbtyp) in //local let recs are not universe polymorphic
            env, lb) env in

          let bvs = lbs |> List.map (fun lb -> left (lb.lbname)) in

          let e2, cres, g2 = tc_term env e2 in
          let guard = Rel.conj_guard g_lbs (Rel.close_guard env (List.map S.mk_binder bvs) g2) in
          let cres = TcUtil.close_lcomp env bvs cres in
          let tres = norm env cres.res_typ in
          let cres = {cres with res_typ=tres} in

(*close*) let lbs, e2 = SS.close_let_rec lbs e2 in
          let e = mk (Tm_let((true, lbs), e2)) (Some tres.n) top.pos in

          begin match topt with
              | Some _ -> e, cres, guard //we have an annotation
              | None ->
                let tres = check_no_escape None env bvs tres in
                let cres = {cres with res_typ=tres} in
                e, cres, guard
          end

        | _ -> failwith "Impossible"

(******************************************************************************)
(* build an environment with recursively bound names.                         *)
(* refining the types of those names with decreases clauses is done in tc_abs *)
(******************************************************************************)
and build_let_rec_env top_level env lbs : list<letbinding> * env_t =
   let env0 = env in
   let termination_check_enabled lbname lbdef lbtyp =
     let t = N.unfold_whnf env lbtyp in
     match (SS.compress t).n, (SS.compress lbdef).n with
     | Tm_arrow (formals, c), Tm_abs(actuals, _, _) ->
       //add implicit binders, in case, for instance
       //lbtyp is of the form x:'a -> t
       //lbdef is of the form (fun x -> t)
       //in which case, we need to add (#'a:Type) to the actuals
       //See the handling in Tm_abs case of tc_value, roughly line 703 (location may have changed since this comment was written)
       let actuals = TcUtil.maybe_add_implicit_binders (Env.set_expected_typ env lbtyp) actuals in
       if List.length formals <> List.length actuals
       then begin
            let actuals_msg =
                let n = List.length actuals in
                if n = 1
                then "1 argument was found"
                else BU.format1 "%s arguments were found" (string_of_int n)
            in
            let formals_msg =
                let n = List.length formals in
                if n = 1
                then "1 argument"
                else BU.format1 "%s arguments" (string_of_int n)
            in
            let msg =
                BU.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                            (Print.term_to_string lbtyp)
                            (Print.lbname_to_string lbname)
                            formals_msg
                            actuals_msg in
            raise (Error(msg, lbdef.pos))
       end;
       let quals = Env.lookup_effect_quals env (U.comp_effect_name c) in
       quals |> List.contains TotalEffect
     | _ ->
       raise (Error(BU.format2 "Only function literals with arrow types can be defined recursively; got %s : %s"
                               (Print.term_to_string lbdef)
                               (Print.term_to_string lbtyp),
                    lbtyp.pos))
   in
   let lbs, env = List.fold_left (fun (lbs, env) lb -> //{lbname=x; lbtyp=t; lbdef=e}) ->
        let univ_vars, t, check_t = TcUtil.extract_let_rec_annotation env lb in
        let env = Env.push_univ_vars env univ_vars in //no polymorphic recursion on universes
        let e = U.unascribe lb.lbdef in
        let t =
            if not check_t
            then t
            else (let t, _, g = tc_check_tot_or_gtot_term ({env0 with check_uvars=true}) t (fst <| U.type_u()) in
                  let g = Rel.resolve_implicits g in
                  ignore <| Rel.discharge_guard env g;
                  norm env0 t) in
        let env = if termination_check_enabled lb.lbname e t
                  && Env.should_verify env (* store the let rec names separately for termination checks *)
                  then {env with letrecs=(lb.lbname,t)::env.letrecs}
                  else Env.push_let_binding env lb.lbname ([], t) in //no polymorphic recursion on universes
        let lb = {lb with lbtyp=t; lbunivs=univ_vars; lbdef=e} in
        lb::lbs,  env)
    ([],env)
    lbs  in
  List.rev lbs, env

and check_let_recs env lbs =
    let lbs, gs = lbs |> List.map (fun lb ->
        (* here we set the expected type in the environment to the annotated expected type
         * and use it in order to type check the body of the lb
         * *)
        let _ = //see issue #1017
           match (SS.compress lb.lbdef).n with
            | Tm_abs _ -> ()
            | _ -> raise (Error("Only function literals may be defined recursively",
                                 S.range_of_lbname lb.lbname))
        in
        let e, c, g = tc_tot_or_gtot_term (Env.set_expected_typ env lb.lbtyp) lb.lbdef in
        if not (U.is_total_lcomp c)
        then raise (Error ("Expected let rec to be a Tot term; got effect GTot", e.pos));
        (* replace the body lb.lbdef with the type checked body e with elaboration on monadic application *)
        let lb = U.mk_letbinding lb.lbname lb.lbunivs lb.lbtyp Const.effect_Tot_lid e in
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
    let topt, wf_annot, univ_vars, univ_opening, env1 = check_lbtyp top_level env lb in

    if not top_level && univ_vars <> []
    then raise (Error("Inner let-bound definitions cannot be universe polymorphic", e1.pos));

    (* 2. type-check e1 *)
    (* Only toplevel terms should have universe openings *)
    assert ( top_level || List.length univ_opening = 0 );
    let e1 = subst univ_opening e1 in
    let e1, c1, g1 = tc_maybe_toplevel_term ({env1 with top_level=top_level}) e1 in

    (* and strengthen its VC with and well-formedness condition on its annotated type *)
    let c1, guard_f = TcUtil.strengthen_precondition
                        (Some (fun () -> Err.ill_kinded_type))
                        (Env.set_range env1 e1.pos) e1 c1 wf_annot in
    let g1 = Rel.conj_guard g1 guard_f in

    if Env.debug env Options.Extreme
    then BU.print3 "checked top-level def %s, result type is %s, guard is %s\n"
            (Print.lbname_to_string lb.lbname)
            (Print.term_to_string c1.res_typ)
            (Rel.guard_to_string env g1);

    e1, univ_vars, c1, g1, Option.isSome topt


(* Extracting the type of non-recursive let binding *)
and check_lbtyp top_level env lb : option<typ>  (* checked version of lb.lbtyp, if it was not Tm_unknown *)
                                 * guard_t      (* well-formedness condition for that type               *)
                                 * univ_names   (* explicit universe variables, if any                   *)
                                 * list<subst_elt> (* subtistution of the opened universes               *)
                                 * Env.env      (* env extended with univ_vars                           *)
                                 =
    let t = SS.compress lb.lbtyp in
    match t.n with
        | Tm_unknown ->
          if lb.lbunivs <> [] then failwith "Impossible: non-empty universe variables but the type is unknown";
          None, Rel.trivial_guard, [], [], env

        | _ ->
          let univ_opening, univ_vars = univ_var_opening lb.lbunivs in
          let t = subst univ_opening t in
          let env1 = Env.push_univ_vars env univ_vars in
          if top_level
          && not (env.generalize) //clearly, x has an annotated type ... could env.generalize ever be true here?
                                  //yes. x may not have a val declaration, only an inline annotation
                                  //so, not (env.generalize) signals that x has been declared as val x : t, and t has already been checked
          then Some t, Rel.trivial_guard, univ_vars, univ_opening, Env.set_expected_typ env1 t //t has already been kind-checked
          else //we have an inline annotation
               let k, _ = U.type_u () in
               let t, _, g = tc_check_tot_or_gtot_term env1 t k in
               if debug env Options.Medium
               then BU.print2 "(%s) Checked type annotation %s\n"
                        (Range.string_of_range (range_of_lbname lb.lbname))
                        (Print.term_to_string t);
               let t = norm env1 t in
               Some t, g, univ_vars, univ_opening, Env.set_expected_typ env1 t


and tc_binder env (x, imp) =
    let tu, u = U.type_u () in
    if Env.debug env Options.Extreme
    then BU.print3 "Checking binders %s:%s at type %s\n" (Print.bv_to_string x) (Print.term_to_string x.sort) (Print.term_to_string tu);
    let t, _, g = tc_check_tot_or_gtot_term env x.sort tu in //ghost effect ok in the types of binders
    let x = {x with sort=t}, imp in
    if Env.debug env Options.High
    then BU.print2 "Pushing binder %s at type %s\n" (Print.bv_to_string (fst x)) (Print.term_to_string t);
    x, push_binding env x, g, u

and tc_binders env bs =
    let rec aux env bs = match bs with
        | [] -> [], env, Rel.trivial_guard, []
        | b::bs ->
          let b, env', g, u = tc_binder env b in
          let bs, env', g', us = aux env' bs in
          b::bs, env', Rel.conj_guard g (Rel.close_guard_univs [u] [b] g'), u::us in
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
  if U.is_tot_or_gtot_lcomp c
  then e, c, g
  else let g = Rel.solve_deferred_constraints env g in
       let c = c.comp() in
       let c = norm_c env c in
       let target_comp, allow_ghost =
            if TcUtil.is_pure_effect env (U.comp_effect_name c)
            then S.mk_Total (U.comp_result c), false
            else S.mk_GTotal (U.comp_result c), true in
       match Rel.sub_comp env c target_comp with
        | Some g' -> e, U.lcomp_of_comp target_comp, Rel.conj_guard g g'
        | _ ->
            if allow_ghost
            then raise (Error(Err.expected_ghost_expression e c, e.pos))
            else raise (Error(Err.expected_pure_expression e c, e.pos))

and tc_check_tot_or_gtot_term env e t : term
                                      * lcomp
                                      * guard_t =
    let env = Env.set_expected_typ env t in
    tc_tot_or_gtot_term env e

and tc_trivial_guard env t =
  let t, c, g = tc_tot_or_gtot_term env t in
  Rel.force_trivial_guard env g;
  t,c

(* type_of_tot_term env e : e', t, g
      checks that env |- e' : Tot t' <== g
      i.e., e' is an elaboration of e
            such that it has type Tot t
            subject to the guard g
            in environment env
 *)
let type_of_tot_term env e =
    if Env.debug env <| Options.Other "RelCheck" then BU.print1 "Checking term %s\n" (Print.term_to_string e);
    //let env, _ = Env.clear_expected_typ env in
    let env = {env with top_level=false; use_bv_sorts=true; letrecs=[]} in
    let t, c, g =
        try tc_tot_or_gtot_term env e
        with Error(msg, _) -> raise (Error("Implicit argument: " ^ msg, Env.get_range env)) in
    if U.is_total_lcomp c
    then t, c.res_typ, g
    else raise (Error(BU.format1 "Implicit argument: Expected a total term; got a ghost term: %s" (Print.term_to_string e), Env.get_range env))

let level_of_type_fail env e t =
    raise (Error(BU.format2 "Expected a term of type 'Type'; got %s : %s"
                                (Print.term_to_string e)
                                t,
                      Env.get_range env))

let level_of_type env e t =
    let rec aux retry t =
        match (U.unrefine t).n with
        | Tm_type u -> u
        | _ ->
          if retry
          then let t = Normalize.normalize [N.UnfoldUntil Delta_constant] env t in
               aux false t
          else let t_u, u = U.type_u() in
               let env = {env with lax=true} in
               let g = FStar.TypeChecker.Rel.teq env t t_u in
               begin match g.guard_f with
                     | NonTrivial f ->
                       level_of_type_fail env e (Print.term_to_string t)
                     | _ ->
                       Rel.force_trivial_guard env g
               end;
               u
    in aux true t

(* universe_of_aux env e:
      During type-inference, we build terms like WPs for which we need to compute
      explicit universe instantiations.

      This is generally called from within TypeChecker.Util
      when building WPs. For example, in building (return_value<u> t e),
      u=universe_of env t.

      We don't aim to compute a precise type for e.
      Rather, we look to compute the universe level of e's type,
      presuming that e must have type Type

      For instance, if e is an application (f _), we compute the type of f to be bs -> C,
      and we take the universe level of e to be (level_of (comp_result C)),
      disregarding the arguments of f.
 *)
let rec universe_of_aux env e =
   match (SS.compress e).n with
   | Tm_bvar _
   | Tm_unknown
   | Tm_delayed _ -> failwith "Impossible"
   //normalize let bindings away and then compute the universe
   | Tm_let _ ->
     let e = N.normalize [] env e in
     universe_of_aux env e
   //we expect to compute (Type u); so an abstraction always fails
   | Tm_abs(bs, t, _) ->
     level_of_type_fail env e "arrow type"
   //these next few cases are easy; we just use the type stored at the node
   | Tm_uvar(_, t) -> t
   | Tm_meta(t, _) -> universe_of_aux env t
   | Tm_name n -> n.sort
   | Tm_fvar fv ->
     let (_, t), _ = Env.lookup_lid env fv.fv_name.v in
     t
   | Tm_ascribed(_, (Inl t, _), _) -> t
   | Tm_ascribed(_, (Inr c, _), _) -> U.comp_result c
   //also easy, since we can quickly recompute the type
   | Tm_type u -> S.mk (Tm_type (U_succ u)) None e.pos
   | Tm_constant sc -> tc_constant e.pos sc
   //slightly subtle, since fv is a type-scheme; instantiate it with us
   | Tm_uinst({n=Tm_fvar fv}, us) ->
     let (us', t), _ = Env.lookup_lid env fv.fv_name.v in
     if List.length us <> List.length us'
     then raise (Error("Unexpected number of universe instantiations", Env.get_range env))
     else List.iter2 (fun u' u -> match u' with
        | U_unif u'' -> Unionfind.change u'' (Some u)
        | _ -> failwith "Impossible") us' us;
     t
   | Tm_uinst _ ->
     failwith "Impossible: Tm_uinst's head must be an fvar"
   //the refinement formula plays no role in the universe computation; so skip it
   | Tm_refine(x, _) -> universe_of_aux env x.sort
   //U_max(univ_of bs, univ_of c)
   | Tm_arrow(bs, c) ->
     let bs, c = SS.open_comp bs c in
     let us = List.map (fun (b, _) -> level_of_type env b.sort (universe_of_aux env b.sort)) bs in
     let u_res =
        let res = U.comp_result c in
        level_of_type env res (universe_of_aux env res) in
     let u_c =
        match Env.effect_repr env c u_res with
        | None -> u_res
        | Some trepr -> level_of_type env trepr (universe_of_aux env trepr) in
     let u = N.normalize_universe env (S.U_max (u_c::us)) in
     S.mk (Tm_type u) None e.pos
   //See the comment at the top of this function; we just compute the universe of hd's result type
   | Tm_app(hd, args) ->
     let rec type_of_head retry hd args =
        let hd = SS.compress hd in
        match hd.n with
        | Tm_unknown
        | Tm_bvar _
        | Tm_delayed _ ->
          failwith "Impossible"
        | Tm_fvar _
        | Tm_name _
        | Tm_uvar _
        | Tm_uinst _
        | Tm_ascribed _
        | Tm_refine _
        | Tm_constant _
        | Tm_arrow _
        | Tm_meta _
        | Tm_type _ ->
          universe_of_aux env hd, args
        | Tm_match(_, hd::_) ->
          let (_, _, hd) = SS.open_branch hd in
          let hd, args = U.head_and_args hd in
          type_of_head retry hd args
        | _ when retry ->
          //head is either an abs, so we have a beta-redex
          //      or a let,
          let e = N.normalize [N.Beta; N.NoDeltaSteps] env e in
          let hd, args = U.head_and_args e in
          type_of_head false hd args
        | _ ->
          let env, _ = Env.clear_expected_typ env in
          let env = {env with lax=true; use_bv_sorts=true; top_level=false} in
          if Env.debug env <| Options.Other "UniverseOf"
          then BU.print2 "%s: About to type-check %s\n"
                        (Range.string_of_range (Env.get_range env))
                        (Print.term_to_string hd);
          let _, ({res_typ=t}), g = tc_term env hd in
          Rel.solve_deferred_constraints env g |> ignore;
          t, args
     in
     let t, args = type_of_head true hd args in
     let t = N.normalize [N.UnfoldUntil Delta_constant] env t in
     let bs, res = U.arrow_formals_comp t in
     let res = U.comp_result res in
     if List.length bs = List.length args
     then let subst = U.subst_of_list bs args in
          SS.subst subst res
     else level_of_type_fail env e (Print.term_to_string res)
   | Tm_match(_, hd::_) ->
     let (_, _, hd) = SS.open_branch hd in
     universe_of_aux env hd
   | Tm_match(_, []) ->
     level_of_type_fail env e "empty match cases"

let universe_of env e = level_of_type env e (universe_of_aux env e)

let tc_tparams env (tps:binders) : (binders * Env.env * universes) =
    let tps, env, g, us = tc_binders env tps in
    Rel.force_trivial_guard env g;
    tps, env, us
