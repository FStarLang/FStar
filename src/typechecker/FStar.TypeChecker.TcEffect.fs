(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.TypeChecker.TcEffect

open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Syntax
open FStar.TypeChecker

open FStar.Util
open FStar.Ident
open FStar.Errors
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.TypeChecker.TcTerm

module PC = FStar.Parser.Const
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Syntax.Util
module Env = FStar.TypeChecker.Env
module N = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util

module BU = FStar.Util

let dmff_cps_and_elaborate env ed =
  (* This is only an elaboration rule not a typechecking one *)

  // Let the power of Dijkstra generate everything "for free", then defer
  // the rest of the job to [tc_decl].
  DMFF.cps_and_elaborate env ed

(*
 * Typechecking of layered effects
 *)
let tc_layered_eff_decl env0 (ed : S.eff_decl) (quals : list<qualifier>) =
  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "Typechecking layered effect: \n\t%s\n" (Print.eff_decl_to_string false ed);

  //we don't support effect binders in layered effects yet
  if List.length ed.univs <> 0 || List.length ed.binders <> 0 then
    raise_error
      (Errors.Fatal_UnexpectedEffect, "Binders are not supported for layered effects (" ^ ed.mname.str ^")")
      (range_of_lid ed.mname);

  (*
   * Helper function used to typecheck and generalize various effect combinators
   *
   * comb is the name of the combinator (used for error messages)
   * n is the number of universes that the combinator should be polymorphic in
   * (us, t) is the tscheme to check and generalize (us will be [] in the first phase)
   *)
  let check_and_gen (comb:string) (n:int) (us, t) : (univ_names * term * typ) =
    let us, t = SS.open_univ_vars us t in
    let t, ty =
      let t, lc, g = tc_tot_or_gtot_term (Env.push_univ_vars env0 us) t in
      Rel.force_trivial_guard env0 g;
      t, lc.res_typ in
    let g_us, t = TcUtil.generalize_universes env0 t in
    let ty = SS.close_univ_vars g_us ty in
    //check that n = List.length g_us and that if us is set, it is same as g_us
    let univs_ok =
      if List.length g_us <> n then
        let error = BU.format5
          "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
          ed.mname.str comb (string_of_int n) (g_us |> List.length |> string_of_int)
          (Print.tscheme_to_string (g_us, t)) in
        raise_error (Errors.Fatal_MismatchUniversePolymorphic, error) t.pos;
      match us with
      | [] -> ()
      | _ ->
       if List.length us = List.length g_us &&
          List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) us g_us
       then ()
       else raise_error (Errors.Fatal_UnexpectedNumberOfUniverse,
              (BU.format4 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                 ed.mname.str comb (Print.univ_names_to_string us) (Print.univ_names_to_string g_us)))
            t.pos in
    g_us, t, ty in

  let log_combinator s (us, t, ty) =
    if Env.debug env0 <| Options.Other "LayeredEffects" then
      BU.print4 "Typechecked %s:%s = %s:%s\n"
        ed.mname.str s
        (Print.tscheme_to_string (us, t)) (Print.tscheme_to_string (us, ty)) in

  //helper function to get (a:Type ?u), returns the binder and ?u
  let fresh_a_and_u_a (a:string) : binder * universe = U.type_u () |> (fun (t, u) -> S.gen_bv a None t |> S.mk_binder, u) in
  //helper function to get (x:a)
  let fresh_x_a (x:string) (a:binder) : binder = S.gen_bv x None (a |> fst |> S.bv_to_name) |> S.mk_binder in


  (*
   * We now typecheck various combinators
   * In all the cases we take the following approach:
   *   - Typecheck the combinator (with no expected type)
   *   - Construct an expected type (k) using uvars
   *   - Unify the type of the combinator (as typechecked) with k
   *   - Record k in the effect declaration (along with the combinator)
   *)


  (*
   * Effect signature
   *
   * The signature term must have the form:
   *   a:Type -> <some binders> -> Effect  //polymorphic in one universe (that of a)
   *
   * The binders become the effect indices
   *)
  let signature =
    let r = (snd ed.signature).pos in
    let sig_us, sig_t, sig_ty = check_and_gen "signature" 1 ed.signature in

    let us, t = SS.open_univ_vars sig_us sig_t in
    let env = Env.push_univ_vars env0 us in

    let a, u = fresh_a_and_u_a "a" in
    let rest_bs = TcUtil.layered_effect_indices_as_binders env r ed.mname (sig_us, sig_t) u (a |> fst |> S.bv_to_name) in
    let bs = a::rest_bs in
    let k = U.arrow bs (S.mk_Total S.teff) in  //U.arrow does closing over bs
    let g_eq = Rel.teq env t k in
    Rel.force_trivial_guard env g_eq;
    sig_us, SS.close_univ_vars us (k |> N.remove_uvar_solutions env), sig_ty in

  log_combinator "signature" signature;

  (*
   * Effect repr
   *
   * The repr must have the type:
   *   a:Type -> <binders for effect indices> -> Type  //polymorphic in one universe (that of a)
   *)
  let repr, underlying_effect_lid =
    let repr_ts = ed |> U.get_eff_repr |> must in
    let r = (snd repr_ts).pos in
    let repr_us, repr_t, repr_ty = check_and_gen "repr" 1 repr_ts in

    let underlying_effect_lid =
      let repr_t =
        N.normalize
          [Env.UnfoldUntil (S.Delta_constant_at_level 0); Env.AllowUnboundUniverses]
          env0 repr_t in
        match (SS.compress repr_t).n with
        | Tm_abs (_, t, _) ->
          (match (SS.compress t).n with
           | Tm_arrow (_, c) -> c |> U.comp_effect_name |> Env.norm_eff_name env0
           | _ -> 
             raise_error (Errors.Fatal_UnexpectedEffect,
               BU.format2 "repr body for %s is not an arrow (%s)"
               (ed.mname |> Ident.string_of_lid) (Print.term_to_string t)) r)
        | _ ->
          raise_error (Errors.Fatal_UnexpectedEffect,
            BU.format2 "repr for %s is not an abstraction (%s)"
              (ed.mname |> Ident.string_of_lid) (Print.term_to_string repr_t)) r in

    //check that if the effect is marked total, then the underlying effect is also total
    if quals |> List.contains TotalEffect &&
       not (Env.is_total_effect env0 underlying_effect_lid)
    then raise_error (Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                      BU.format2 "Effect %s is marked total but its underlying effect %s is not total"
                        (ed.mname |> Ident.string_of_lid) (underlying_effect_lid |> Ident.string_of_lid)) r;

    
    let us, ty = SS.open_univ_vars repr_us repr_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u = fresh_a_and_u_a "a" in
    let rest_bs =
      let signature_ts = let us, t, _ = signature in (us, t) in
      TcUtil.layered_effect_indices_as_binders env r ed.mname signature_ts u (a |> fst |> S.bv_to_name) in
    let bs = a::rest_bs in
    let k = U.arrow bs (U.type_u () |> (fun (t, u) -> S.mk_Total' t (Some (new_u_univ ())))) in  //note the universe of Tot need not be u
    let g = Rel.teq env ty k in
    Rel.force_trivial_guard env g;
    (repr_us, repr_t, SS.close_univ_vars us (k |> N.remove_uvar_solutions env)),
    underlying_effect_lid in

  log_combinator "repr" repr;

  //helper function that creates an application node (repr<u> a_tm ?u1 ... ?un)
  //returns the application term and the guard for the introduced uvars (see TcUtil.fresh_layered_effect_repr)
  let fresh_repr r env u a_tm =
    let signature_ts = let us, t, _ = signature in (us, t) in
    let repr_ts = let us, t, _ = repr in (us, t) in
    TcUtil.fresh_effect_repr env r ed.mname signature_ts (Some repr_ts) u a_tm in

  let not_an_arrow_error comb n t r =
    raise_error (Errors.Fatal_UnexpectedEffect,
      BU.format5 "Type of %s:%s is not an arrow with >= %s binders (%s::%s)" ed.mname.str comb
        (string_of_int n) (Print.tag_of_term t) (Print.term_to_string t)
    ) r in

  (*
   * return_repr
   *
   * return_repr must have type:
   *   a:Type -> <some binders> -> x:a -> repr a i_1 ... i_n  //polymorphic in one universe (that of a)
   *   where i_1 ... i_n are terms of effect indices types (as in the signature)
   *
   * The binders have arbitrary sorts
   *)
  let return_repr =
    let return_repr_ts = ed |> U.get_return_repr |> must in
    let r = (snd return_repr_ts).pos in
    let ret_us, ret_t, ret_ty = check_and_gen "return_repr" 1 return_repr_ts in

    let us, ty = SS.open_univ_vars ret_us ret_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u_a = fresh_a_and_u_a "a" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 2 ->
        let ((a', _)::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 1) |> fst
           |> SS.subst_binders [NT (a', bv_to_name (fst a))]
      | _ -> not_an_arrow_error "return" 2 ty r in
    let bs = a::(rest_bs@[fresh_x_a "x" a]) in
    let repr, g = fresh_repr r (Env.push_binders env bs) u_a (fst a |> S.bv_to_name) in
    let k = U.arrow bs (S.mk_Total' repr (Some u_a)) in
    let g_eq = Rel.teq env ty k in
    Rel.force_trivial_guard env (Env.conj_guard g g_eq);
    ret_us, ret_t, SS.close_univ_vars us (k |> N.remove_uvar_solutions env) in

  log_combinator "return_repr" return_repr;

  (*
   * bind_repr
   *
   * bind_repr must have type:
   *   a:Type -> b:Type -> <some binders> -> f:repr a i_1 ... i_n -> (g:a -> repr a j_1 ... j_n)
   *   : repr a k_1 ... k_n  //polymorphic in two universes (that of a and b)
   *   where i, j, k are terms of effect indices types (as in the signature)
   *
   * The binders have arbitrary sorts
   *)
  let bind_repr =
    let bind_repr_ts = ed |> U.get_bind_repr |> must in
    let r = (snd bind_repr_ts).pos in
    let bind_us, bind_t, bind_ty = check_and_gen "bind_repr" 2 bind_repr_ts in

    let us, ty = SS.open_univ_vars bind_us bind_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u_a = fresh_a_and_u_a "a" in
    let b, u_b = fresh_a_and_u_a "b" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 4 ->
        let ((a', _)::(b', _)::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 2) |> fst
           |> SS.subst_binders [NT (a', bv_to_name (fst a)); NT (b', bv_to_name (fst b))] 
      | _ -> not_an_arrow_error "bind" 4 ty r in
    let bs = a::b::rest_bs in
    let f, guard_f =
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (fst a |> S.bv_to_name) in
      S.gen_bv "f" None repr |> S.mk_binder, g in
    let g, guard_g =
      let x_a = fresh_x_a "x" a in
      let repr, g = fresh_repr r (Env.push_binders env (bs@[x_a])) u_b (fst b |> S.bv_to_name) in
      S.gen_bv "g" None (U.arrow [x_a] (S.mk_Total' repr (Some (new_u_univ ())))) |> S.mk_binder, g in
    let repr, guard_repr = fresh_repr r (Env.push_binders env bs) u_b (fst b |> S.bv_to_name) in
    let k = U.arrow (bs@[f; g]) (S.mk_Total' repr (Some u_b)) in
    let guard_eq = Rel.teq env ty k in
    List.iter (Rel.force_trivial_guard env) [guard_f; guard_g; guard_repr; guard_eq];
    bind_us, bind_t, SS.close_univ_vars bind_us (k |> N.remove_uvar_solutions env) in

  log_combinator "bind_repr" bind_repr;

  (*
   * stronger_repr
   *
   * stronger_repr must have type:
   *   a:Type -> <some binders> -> f:repr a i_1 ... i_n -> PURE (repr a j_1 ... j_n) wp //polymorphic in one universe (that of a)
   *   where i, j are terms of effect indices types (as in the signature)
   *
   * The binders have arbitrary sorts
   *)
  let stronger_repr =
    let stronger_repr = ed |> U.get_stronger_repr |> must in
    let r = (snd stronger_repr).pos in

    let stronger_us, stronger_t, stronger_ty = check_and_gen "stronger_repr" 1 stronger_repr in

    if Env.debug env0 <| Options.Other "LayeredEffects" then
      BU.print2 "stronger combinator typechecked with term: %s and type: %s\n"
        (Print.tscheme_to_string (stronger_us, stronger_t))
        (Print.tscheme_to_string (stronger_us, stronger_ty));

    let us, ty = SS.open_univ_vars stronger_us stronger_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u = fresh_a_and_u_a "a" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 2 ->
        let ((a', _)::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 1) |> fst
           |> SS.subst_binders [NT (a', bv_to_name (fst a))]
      | _ -> not_an_arrow_error "stronger" 2 ty r in
    let bs = a::rest_bs in
    let f, guard_f =
      let repr, g = fresh_repr r (Env.push_binders env bs) u (fst a |> S.bv_to_name) in
      S.gen_bv "f" None repr |> S.mk_binder, g in
    let ret_t, guard_ret_t = fresh_repr r (Env.push_binders env bs) u (fst a |> S.bv_to_name) in

    let pure_wp_t =
      let pure_wp_ts = Env.lookup_definition [Env.NoDelta] env PC.pure_wp_lid |> must in
      let _, pure_wp_t = Env.inst_tscheme pure_wp_ts in
      S.mk_Tm_app
        pure_wp_t
        [ret_t |> S.as_arg]
        None r in
    let pure_wp_uvar, _, guard_wp =
      let reason = BU.format1 "implicit for pure_wp in checking stronger for %s" ed.mname.str in
      TcUtil.new_implicit_var reason r (Env.push_binders env bs) pure_wp_t in
    let c = S.mk_Comp ({
      comp_univs = [ Env.new_u_univ () ];
      effect_name = PC.effect_PURE_lid;
      result_typ = ret_t;
      effect_args = [ pure_wp_uvar |> S.as_arg ];
      flags = [] }) in

    let k = U.arrow (bs@[f]) c in

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Expected type before unification: %s\n"
        (Print.term_to_string k);

    let guard_eq = Rel.teq env ty k in
    List.iter (Rel.force_trivial_guard env) [guard_f; guard_ret_t; guard_wp; guard_eq];
    let k = N.remove_uvar_solutions env k in
    stronger_us, stronger_t, k |> N.normalize [Env.Beta; Env.Eager_unfolding] env |> SS.close_univ_vars stronger_us in

  log_combinator "stronger_repr" stronger_repr;

  let if_then_else =
    let if_then_else_ts = ed |> U.get_layered_if_then_else_combinator |> must in
    let r = (snd if_then_else_ts).pos in
    let if_then_else_us, if_then_else_t, if_then_else_ty = check_and_gen "if_then_else" 1 if_then_else_ts in

    let us, t = SS.open_univ_vars if_then_else_us if_then_else_t in
    let _, ty = SS.open_univ_vars if_then_else_us if_then_else_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u_a = fresh_a_and_u_a "a" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 4 ->
        let ((a', _)::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 3) |> fst
           |> SS.subst_binders [NT (a', a |> fst |> S.bv_to_name)]
      | _ -> not_an_arrow_error "if_then_else" 4 ty r in
    let bs = a::rest_bs in
    let f_bs, guard_f =
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (a |> fst |> S.bv_to_name) in
      S.gen_bv "f" None repr |> S.mk_binder, g in
    let g_bs, guard_g =
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (a |> fst |> S.bv_to_name) in
      S.gen_bv "g" None repr |> S.mk_binder, g in
    let p_b = S.gen_bv "p" None U.ktype0 |> S.mk_binder in
    let t_body, guard_body = fresh_repr r (Env.push_binders env (bs@[p_b])) u_a (a |> fst |> S.bv_to_name) in
    let k = U.abs (bs@[f_bs; g_bs; p_b]) t_body None in
    let guard_eq = Rel.teq env t k in
    [guard_f; guard_g; guard_body; guard_eq] |> List.iter (Rel.force_trivial_guard env);

    if_then_else_us, SS.close_univ_vars if_then_else_us (k |> N.remove_uvar_solutions env), if_then_else_ty in

  log_combinator "if_then_else" if_then_else;


  (*
   * Checking the soundness of the if_then_else combinator
   *
   * In all combinators, other than if_then_else, the soundess is ensured
   *   by extracting the application of those combinators to their definitions
   * For if_then_else, the combinator does not have an extraction equivalent
   *   It is only used in VC generation
   *
   * So we need to make sure that the combinator is sound
   *
   * Informally, we want to check that:
   *
   *     p ==> (subcomp f <: if_then_else f g)  and
   * not p ==> (subcomp g <: if_then_else f g)
   *
   * Basically when p holds, the computation type of f should be coercible to if_then_else f g
   *   and similarly for the (not p) case
   *
   * The way we program it, we first build the term:
   *   subcomp <some number of _> f <: if_then_else bs f g
   *   where bs are some variables for the extra binders of if_then_else, and f and g are also variables
   *
   * Then, we typecheck this term which fills in the _ in subcomp application and returns a guard
   * We refine the guard to add an implication p ==> guard,
   *   and then discharge it
   * 
   * Similarly for the g case
   *)
  let _if_then_else_is_sound =
    let r = (ed |> U.get_layered_if_then_else_combinator |> must |> snd).pos in

    let ite_us, ite_t, _ = if_then_else in

    let us, ite_t = SS.open_univ_vars ite_us ite_t in
    let env, ite_t_applied, f_t, g_t, p_t =
      match (SS.compress ite_t).n with
      | Tm_abs (bs, _, _) ->
        let bs = SS.open_binders bs in
        let f, g, p =
          bs
          |> List.splitAt (List.length bs - 3)
          |> snd
          |> List.map fst
          |> List.map S.bv_to_name
          |> (fun l -> let (f::g::p::[]) = l in f, g, p) in
        Env.push_binders (Env.push_univ_vars env0 us) bs,
        S.mk_Tm_app ite_t
          (bs |> List.map fst |> List.map S.bv_to_name |> List.map S.as_arg)
          None r,
        f, g, p
      | _ -> failwith "Impossible! ite_t must have been an abstraction with at least 3 binders" in

    let subcomp_f, subcomp_g =
      let _, subcomp_t, subcomp_ty = stronger_repr in
      let _, subcomp_t = SS.open_univ_vars us subcomp_t in

      let bs_except_last =
        let _, subcomp_ty = SS.open_univ_vars us subcomp_ty in
        match (SS.compress subcomp_ty).n with
        | Tm_arrow (bs, _) -> bs |> List.splitAt (List.length bs - 1) |> fst
        | _ -> failwith "Impossible! subcomp_ty must have been an arrow with at lease 1 binder" in

     let aux t = 
      S.mk_Tm_app
        subcomp_t
        (((bs_except_last |> List.map (fun _ -> S.tun))@[t]) |> List.map S.as_arg)
        None r in

     aux f_t, aux g_t in

    let tm_subcomp_ascribed_f, tm_subcomp_ascribed_g =
      let aux t =
        S.mk
          (Tm_ascribed (t, (Inr (S.mk_Total ite_t_applied), None), None))
          None r in

      aux subcomp_f, aux subcomp_g in

    if Env.debug env <| Options.Other "LayeredEffects"
    then BU.print2 "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
           (Print.term_to_string tm_subcomp_ascribed_f)
           (Print.term_to_string tm_subcomp_ascribed_g);


    let _, _, g_f = tc_tot_or_gtot_term env tm_subcomp_ascribed_f in
    let g_f = Env.imp_guard (Env.guard_of_guard_formula (NonTrivial p_t)) g_f in
    Rel.force_trivial_guard env g_f;


    let _, _, g_g = tc_tot_or_gtot_term env tm_subcomp_ascribed_g in
    let g_g =
      let not_p = S.mk_Tm_app
        (S.lid_as_fv PC.not_lid S.delta_constant None |> S.fv_to_tm)
        [p_t |> S.as_arg]
        None r in
      Env.imp_guard (Env.guard_of_guard_formula (NonTrivial not_p)) g_g in
    Rel.force_trivial_guard env g_g in


  (*
   * Actions
   *
   * Actions must have type:
   *   <some binders> -> repr a i_1 ... i_n
   *   so that we can inject them into the effect
   *
   * Other than this, no polymorphism etc. restrictions
   *
   * TODO: this code has a lot in common with actions for non-layered effects, we should reuse
   *)
  let tc_action env (act:action) : action =
    let env0 = env in
    let r = act.action_defn.pos in
    if List.length act.action_params <> 0
    then raise_error (Errors.Fatal_MalformedActionDeclaration,
      BU.format3 "Action %s:%s has non-empty action params (%s)"
        ed.mname.str act.action_name.str (Print.binders_to_string "; " act.action_params)) r;

    let env, act =
      let usubst, us = SS.univ_var_opening act.action_univs in
      Env.push_univ_vars env us,
      { act with 
        action_univs = us;
        action_defn  = SS.subst usubst act.action_defn;
        action_typ   = SS.subst usubst act.action_typ } in
    
    let act_typ =
      match (SS.compress act.action_typ).n with
      | Tm_arrow (bs, c) ->
        let ct = U.comp_to_comp_typ c in
        if lid_equals ct.effect_name ed.mname
        then
          let repr_ts = let us, t, _ = repr in (us, t) in
          let repr = Env.inst_tscheme_with repr_ts ct.comp_univs |> snd in
          let repr = S.mk_Tm_app
            repr
            (S.as_arg ct.result_typ::ct.effect_args)
            None r in
          let c = S.mk_Total' repr (Some (new_u_univ ())) in
          U.arrow bs c
        else act.action_typ
      | _ -> act.action_typ in
    
    let act_typ, _, g_t = tc_tot_or_gtot_term env act_typ in
    let act_defn, _, g_d = tc_tot_or_gtot_term
      ({ Env.set_expected_typ env act_typ with instantiate_imp = false })
      act.action_defn in
    
    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print2 "Typechecked action definition: %s and action type: %s\n"
        (Print.term_to_string act_defn) (Print.term_to_string act_typ);

    let k, g_k =
      let act_typ = N.normalize [Beta] env act_typ in
      match (SS.compress act_typ).n with
      | Tm_arrow (bs, _) ->
        let bs = SS.open_binders bs in
        let env = Env.push_binders env bs in
        let t, u = U.type_u () in
        let reason = BU.format2 "implicit for return type of action %s:%s"
          ed.mname.str act.action_name.str in
        let a_tm, _, g_tm = TcUtil.new_implicit_var reason r env t in
        let repr, g = fresh_repr r env u a_tm in
        U.arrow bs (S.mk_Total' repr (Env.new_u_univ () |> Some)), Env.conj_guard g g_tm
      | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType,
        BU.format3 "Unexpected non-function type for action %s:%s (%s)"
          ed.mname.str act.action_name.str (Print.term_to_string act_typ)) r in

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Expected action type: %s\n" (Print.term_to_string k);

    let g = Rel.teq env act_typ k in
    List.iter (Rel.force_trivial_guard env) [g_t; g_d; g_k; g];

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Expected action type after unification: %s\n" (Print.term_to_string k);
    
    let act_typ =
      let err_msg t = BU.format3
        "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
        ed.mname.str act.action_name.str (Print.term_to_string t) in
      let repr_args t : universes * term * args =
        match (SS.compress t).n with
        | Tm_app (head, a::is) ->
          (match (SS.compress head).n with
           | Tm_uinst (_, us) -> us, fst a, is
           | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType, err_msg t) r)
        | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType, err_msg t) r in

      let k = N.normalize [Beta] env k in
      match (SS.compress k).n with
      | Tm_arrow (bs, c) ->
        let bs, c = SS.open_comp bs c in
        let us, a, is = repr_args (U.comp_result c) in
        let ct = {
          comp_univs = us;
          effect_name = ed.mname;
          result_typ = a;
          effect_args = is;
          flags = [] } in
        U.arrow bs (S.mk_Comp ct)
      | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType, err_msg k) r in

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Action type after injecting it into the monad: %s\n" (Print.term_to_string act_typ);
    
    let act =
      let us, act_defn = TcUtil.generalize_universes env act_defn in
      if act.action_univs = []
      then
        { act with
          action_univs = us;
          action_defn = act_defn;
          action_typ = SS.close_univ_vars us act_typ }
      else
        if List.length us = List.length act.action_univs &&
           List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) us act.action_univs
        then { act with
          action_defn = act_defn;
          action_typ = SS.close_univ_vars act.action_univs act_typ }
        else raise_error (Errors.Fatal_UnexpectedNumberOfUniverse,
               (BU.format4 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                 ed.mname.str act.action_name.str (Print.univ_names_to_string us) (Print.univ_names_to_string act.action_univs)))
             r in

    act in

  let tschemes_of (us, t, ty) : tscheme * tscheme = (us, t), (us, ty) in

  let combinators = Layered_eff ({
    l_base_effect = underlying_effect_lid;
    l_repr = tschemes_of repr;
    l_return = tschemes_of return_repr;
    l_bind = tschemes_of bind_repr;
    l_subcomp = tschemes_of stronger_repr;
    l_if_then_else = tschemes_of if_then_else
  }) in

  { ed with
    signature     = (let us, t, _ = signature in (us, t));
    combinators   = combinators;
    actions       = List.map (tc_action env0) ed.actions }

let check_and_gen env t k =
    // BU.print1 "\x1b[01;36mcheck and gen \x1b[00m%s\n" (Print.term_to_string t);
    TcUtil.generalize_universes env (tc_check_trivial_guard env t k)

let tc_non_layered_eff_decl env0 (ed:S.eff_decl) (_quals : list<qualifier>) : S.eff_decl =
  if Env.debug env0 <| Options.Other "ED" then
    BU.print1 "Typechecking eff_decl: \n\t%s\n" (Print.eff_decl_to_string false ed);

  let us, bs =
    //ed.univs are free universes in the binders
    //first open them
    let ed_univs_subst, ed_univs = SS.univ_var_opening ed.univs in

    //ed.binders are effect parameters (e.g. heap in STATE_h), typecheck them after opening them
    let bs = SS.open_binders (SS.subst_binders ed_univs_subst ed.binders) in
    let bs, _, _ = tc_tparams (Env.push_univ_vars env0 ed_univs) bs in  //tc_tparams forces the guard from checking the binders

    //generalize the universes in bs
    //bs are closed with us and closed
    let us, bs =
      let tmp_t = U.arrow bs (S.mk_Total' S.t_unit (U_zero |> Some)) in  //create a temporary bs -> Tot unit
      let us, tmp_t = TcUtil.generalize_universes env0 tmp_t in
      us, tmp_t |> U.arrow_formals |> fst |> SS.close_binders in

    match ed_univs with
    | [] -> us, bs  //if no annotated universes, return us, bs
    | _ ->
      //if ed.univs is already set, it must be the case that us = ed.univs, else error out
      if List.length ed_univs = List.length us &&
         List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) ed_univs us
      then us, bs
      else raise_error (Errors.Fatal_UnexpectedNumberOfUniverse,
             (BU.format3 "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
               ed.mname.str (BU.string_of_int (List.length ed_univs)) (BU.string_of_int (List.length us))))
             (range_of_lid ed.mname)
  in

  //at this points, bs are closed and closed with us also
  //they are in scope for rest of the ed

  let ed = { ed with univs = us; binders = bs } in

  //now open rest of the ed with us and bs
  let ed_univs_subst, ed_univs = SS.univ_var_opening us in
  let ed_bs, ed_bs_subst = SS.open_binders' (SS.subst_binders ed_univs_subst bs) in
  
  
  let ed =
    let op (us, t) =
      let t = SS.subst (SS.shift_subst (List.length ed_bs + List.length us) ed_univs_subst) t in
      us, SS.subst (SS.shift_subst (List.length us) ed_bs_subst) t in

    { ed with
      signature     =op ed.signature;
      combinators   = U.apply_eff_combinators op ed.combinators;
      actions       = List.map (fun a ->
        { a with action_defn = snd (op (a.action_univs, a.action_defn));
                 action_typ  = snd (op (a.action_univs, a.action_typ)) }) ed.actions;
    } in

  if Env.debug env0 <| Options.Other "ED" then
    BU.print1 "After typechecking binders eff_decl: \n\t%s\n" (Print.eff_decl_to_string false ed);

  let env = Env.push_binders (Env.push_univ_vars env0 ed_univs) ed_bs in

  (*
   * AR: check that (us, t) has type k, and generalize (us, t)
   *     comb is the name of the combinator (useful for error messages)
   *     n is the expected number of free universes (after generalization)
   *     env_opt is an optional env (e.g. bind_repr is typechecked lax)
   *)
  let check_and_gen' (comb:string) (n:int) env_opt (us, t) k : tscheme =
    let env = if is_some env_opt then env_opt |> must else env in
    let us, t = SS.open_univ_vars us t in
    let t =
      match k with
      | Some k -> tc_check_trivial_guard (Env.push_univ_vars env us) t k
      | None ->
        let t, _, g = tc_tot_or_gtot_term (Env.push_univ_vars env us) t in
        Rel.force_trivial_guard env g;
        t in
    let g_us, t = TcUtil.generalize_universes env t in
    //check that n = List.length g_us and that if us is set, it is same as g_us
    begin
      if List.length g_us <> n then
        let error = BU.format4
          "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
          ed.mname.str comb (string_of_int n) (g_us |> List.length |> string_of_int) in
        raise_error (Errors.Fatal_MismatchUniversePolymorphic, error) t.pos
    end;
    match us with
    | [] -> g_us, t
    | _ ->
     if List.length us = List.length g_us &&
        List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) us g_us
     then g_us, t
     else raise_error (Errors.Fatal_UnexpectedNumberOfUniverse,
            (BU.format4 "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
               ed.mname.str comb (BU.string_of_int (List.length us)) (BU.string_of_int (List.length g_us))))
            t.pos
  in

  let signature = check_and_gen' "signature" 1 None ed.signature None in

  if Env.debug env0 <| Options.Other "ED" then
    BU.print1 "Typechecked signature: %s\n" (Print.tscheme_to_string signature);

  (*
   * AR: return a fresh (in the sense of fresh universe) instance of a:Type and wp sort (closed with the returned a) 
   *)
  let fresh_a_and_wp () =
    let fail t = raise_error (Err.unexpected_signature_for_monad env ed.mname t) (snd ed.signature).pos in
    //instantiate with fresh universes
    let _, signature = Env.inst_tscheme signature in
    match (SS.compress signature).n with
    | Tm_arrow (bs, _) ->
      let bs = SS.open_binders bs in
      (match bs with
       | [(a, _); (wp, _)] -> a, wp.sort
       | _ -> fail signature)
    | _ -> fail signature
  in

  let log_combinator s ts =
    if Env.debug env <| Options.Other "ED" then
      BU.print3 "Typechecked %s:%s = %s\n" ed.mname.str s (Print.tscheme_to_string ts) in

  let ret_wp =
    let a, wp_sort = fresh_a_and_wp () in
    let k = U.arrow [ S.mk_binder a; S.null_binder (S.bv_to_name a)] (S.mk_GTotal wp_sort) in
    check_and_gen' "ret_wp" 1 None (ed |> U.get_return_vc_combinator) (Some k) in

  log_combinator "ret_wp" ret_wp;

  let bind_wp =
    let a, wp_sort_a = fresh_a_and_wp () in
    let b, wp_sort_b = fresh_a_and_wp () in
    let wp_sort_a_b = U.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_sort_b) in

    let k = U.arrow [
      S.null_binder t_range;
      S.mk_binder a;
      S.mk_binder b;
      S.null_binder wp_sort_a;
      S.null_binder wp_sort_a_b ] (S.mk_Total wp_sort_b) in

    check_and_gen' "bind_wp" 2 None (ed |> U.get_bind_vc_combinator) (Some k) in

  log_combinator "bind_wp" bind_wp;

  let stronger =
    let a, wp_sort_a = fresh_a_and_wp () in
    let t, _ = U.type_u() in
    let k = U.arrow [
      S.mk_binder a;
      S.null_binder wp_sort_a;
      S.null_binder wp_sort_a ] (S.mk_Total t) in
    check_and_gen' "stronger" 1 None (ed |> U.get_stronger_vc_combinator) (Some k) in

  log_combinator "stronger" stronger;

  let if_then_else =
    let a, wp_sort_a = fresh_a_and_wp () in
    let p = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let k = U.arrow [
      S.mk_binder a;
      S.mk_binder p;
      S.null_binder wp_sort_a;
      S.null_binder wp_sort_a ] (S.mk_Total wp_sort_a) in

    check_and_gen' "if_then_else" 1 None (ed |> U.get_wp_if_then_else_combinator |> must) (Some k) in

  log_combinator "if_then_else" if_then_else;

  let ite_wp =
    let a, wp_sort_a = fresh_a_and_wp () in
    let k = U.arrow [S.mk_binder a; S.null_binder wp_sort_a] (S.mk_Total wp_sort_a) in
    check_and_gen' "ite_wp" 1 None (ed |> U.get_wp_ite_combinator |> must) (Some k) in

  log_combinator "ite_wp" ite_wp;

  let close_wp =
    let a, wp_sort_a = fresh_a_and_wp () in
    let b = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let wp_sort_b_a = U.arrow [S.null_binder (S.bv_to_name b)] (S.mk_Total wp_sort_a) in

    let k = U.arrow [S.mk_binder a; S.mk_binder b; S.null_binder wp_sort_b_a] (S.mk_Total wp_sort_a) in
    check_and_gen' "close_wp" 2 None (ed |> U.get_wp_close_combinator |> must) (Some k) in

  log_combinator "close_wp" close_wp;

  let trivial =
    let a, wp_sort_a = fresh_a_and_wp () in
    let t, _ = U.type_u () in
    let k = U.arrow [S.mk_binder a; S.null_binder wp_sort_a] (S.mk_GTotal t) in
    let trivial = check_and_gen' "trivial" 1 None (ed |> U.get_wp_trivial_combinator |> must) (Some k) in

    log_combinator "trivial" trivial;

    trivial in

  let repr, return_repr, bind_repr, actions =
    match ed |> U.get_eff_repr with
    | None -> None, None, None, ed.actions
    | _ ->
      let repr =
        let a, wp_sort_a = fresh_a_and_wp () in
        let t, _ = U.type_u () in
        let k = U.arrow [S.mk_binder a; S.null_binder wp_sort_a] (S.mk_GTotal t) in
        check_and_gen' "repr" 1 None (ed |> U.get_eff_repr |> must) (Some k) in

      log_combinator "repr" repr;

      let mk_repr' t wp =
        let _, repr = Env.inst_tscheme repr in
        let repr = N.normalize [EraseUniverses; AllowUnboundUniverses] env repr in
        mk (Tm_app (repr, [t |> as_arg; wp |> as_arg])) None Range.dummyRange in
      let mk_repr a wp = mk_repr' (S.bv_to_name a) wp in
      let destruct_repr t =
        match (SS.compress t).n with
        | Tm_app(_, [(t, _); (wp, _)]) -> t, wp
        | _ -> failwith "Unexpected repr type" in

      let return_repr =
        let return_repr_ts = ed |> U.get_return_repr |> must in
        let a, _ = fresh_a_and_wp () in
        let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
        let res =
          let wp = mk_Tm_app
            (Env.inst_tscheme ret_wp |> snd)
            [S.bv_to_name a |> S.as_arg; S.bv_to_name x_a |> S.as_arg] None Range.dummyRange in
          mk_repr a wp in
        let k = U.arrow [S.mk_binder a; S.mk_binder x_a] (S.mk_Total res) in
        let k, _, _ = tc_tot_or_gtot_term env k in
        let env = Some (Env.set_range env (snd return_repr_ts).pos) in
        check_and_gen' "return_repr" 1 env return_repr_ts (Some k) in
    
      log_combinator "return_repr" return_repr;

      let bind_repr =
        let bind_repr_ts = ed |> U.get_bind_repr |> must in
        let r = S.lid_as_fv PC.range_0 delta_constant None |> S.fv_to_tm in
        let a, wp_sort_a = fresh_a_and_wp () in
        let b, wp_sort_b = fresh_a_and_wp () in
        let wp_sort_a_b = U.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_sort_b) in
        let wp_f = S.gen_bv "wp_f" None wp_sort_a in
        let wp_g = S.gen_bv "wp_g" None wp_sort_a_b in
        let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
        let wp_g_x = mk_Tm_app (S.bv_to_name wp_g) [S.bv_to_name x_a |> S.as_arg] None Range.dummyRange in
        let res =
          let wp = mk_Tm_app
            (Env.inst_tscheme bind_wp |> snd)
            (List.map as_arg [r; S.bv_to_name a; S.bv_to_name b; S.bv_to_name wp_f; S.bv_to_name wp_g])
            None Range.dummyRange in
          mk_repr b wp in

        let maybe_range_arg =
          if BU.for_some (U.attr_eq U.dm4f_bind_range_attr) ed.eff_attrs
          then [S.null_binder S.t_range; S.null_binder S.t_range]
          else [] in
       
        let k = U.arrow ([S.mk_binder a; S.mk_binder b] @
                         maybe_range_arg @
                         [S.mk_binder wp_f;
                          S.null_binder (mk_repr a (S.bv_to_name wp_f));
                          S.mk_binder wp_g;
                          S.null_binder (U.arrow [S.mk_binder x_a] (S.mk_Total <| mk_repr b (wp_g_x)))])
                        (S.mk_Total res) in
        let k, _, _ = tc_tot_or_gtot_term env k in
        let env = Env.set_range env (snd bind_repr_ts).pos in
        let env = {env with lax=true} |> Some in //we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
        check_and_gen' "bind_repr" 2 env bind_repr_ts (Some k) in

      log_combinator "bind_repr" bind_repr;

      let actions =
        let check_action (act:action) =
          (* We should not have action params anymore, they should have been handled by dmff below *)
          if List.length act.action_params <> 0 then failwith "tc_eff_decl: expected action_params to be empty";

          // 0) The action definition has a (possibly) useless type; the
          // action cps'd type contains the "good" wp that tells us EVERYTHING
          // about what this action does. Please note that this "good" wp is
          // of the form [binders -> repr ...], i.e. is it properly curried.

          //in case action has universes, open the action type etc. first
          let env, act =
            if act.action_univs = [] then env, act
            else
              let usubst, uvs = SS.univ_var_opening act.action_univs in
              Env.push_univ_vars env uvs,
              { act with
                action_univs = uvs;
                action_defn  = SS.subst usubst act.action_defn;
                action_typ   = SS.subst usubst act.action_typ } in

          //AR: if the act typ is already in the effect monad (e.g. in the second phase),
          //    then, convert it to repr, so that the code after it can work as it is
          //    perhaps should open/close binders properly
          let act_typ =
            match (SS.compress act.action_typ).n with
            | Tm_arrow (bs, c) ->
              let c = U.comp_to_comp_typ c in
              if lid_equals c.effect_name ed.mname
              then U.arrow bs (S.mk_Total (mk_repr' c.result_typ (fst (List.hd c.effect_args))))
              else act.action_typ
            | _ -> act.action_typ
          in

          let act_typ, _, g_t = tc_tot_or_gtot_term env act_typ in

          // 1) Check action definition, setting its expected type to
          //    [action_typ]
          let env' = { Env.set_expected_typ env act_typ with instantiate_imp = false } in
          if Env.debug env (Options.Other "ED") then
            BU.print3 "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
              (text_of_lid act.action_name) (Print.term_to_string act.action_defn)
              (Print.term_to_string act_typ);
          let act_defn, _, g_a = tc_tot_or_gtot_term env' act.action_defn in

          let act_defn = N.normalize [ Env.UnfoldUntil S.delta_constant ] env act_defn in
          let act_typ = N.normalize [ Env.UnfoldUntil S.delta_constant; Env.Eager_unfolding; Env.Beta ] env act_typ in
          // 2) This implies that [action_typ] has Type(k): good for us!

          // 3) Unify [action_typ] against [expected_k], because we also need
          // to check that the action typ is of the form [binders -> repr ...]
          let expected_k, g_k =
            let act_typ = SS.compress act_typ in
            match act_typ.n with
            | Tm_arrow(bs, c) ->
              let bs, _ = SS.open_comp bs c in
              let res = mk_repr' S.tun S.tun in
              let k = U.arrow bs (S.mk_Total res) in
              let k, _, g = tc_tot_or_gtot_term env k in
              k, g
            | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType, (BU.format2
              "Actions must have function types (not: %s, a.k.a. %s)"
                (Print.term_to_string act_typ) (Print.tag_of_term act_typ))) act_defn.pos
          in
          let g = Rel.teq env act_typ expected_k in
          Rel.force_trivial_guard env (Env.conj_guard g_a (Env.conj_guard g_k (Env.conj_guard g_t g)));

          // 4) Do a bunch of plumbing to assign a type in the new monad to
          //    the action
          let act_typ = match (SS.compress expected_k).n with
              | Tm_arrow(bs, c) ->
                let bs, c = SS.open_comp bs c in
                let a, wp = destruct_repr (U.comp_result c) in
                let c = {
                  comp_univs=[env.universe_of env a];
                  effect_name = ed.mname;
                  result_typ = a;
                  effect_args = [as_arg wp];
                  flags = []
                } in
                U.arrow bs (S.mk_Comp c)
              | _ -> failwith "Impossible (expected_k is an arrow)" in

          (* printfn "Checked action %s against type %s\n" *)
          (*         (Print.term_to_string act_defn) *)
          (*         (Print.term_to_string (N.normalize [Env.Beta] env act_typ)); *)

          //AR: if the action universes were already annotated, simply close, else generalize
          let univs, act_defn =
            if act.action_univs = []
            then TcUtil.generalize_universes env act_defn
            else act.action_univs, SS.close_univ_vars act.action_univs act_defn
          in
          let act_typ = N.normalize [Env.Beta] env act_typ in
          let act_typ = Subst.close_univ_vars univs act_typ in
          {act with
           action_univs=univs;
           action_defn=act_defn;
           action_typ =act_typ }
        in
        ed.actions |> List.map check_action in

      Some repr, Some return_repr, Some bind_repr, actions
  in

  //close the ed_univs and ed_bs
  let cl ts =
    let ts = SS.close_tscheme ed_bs ts in
    let ed_univs_closing = SS.univ_var_closing ed_univs in
    SS.subst_tscheme (SS.shift_subst (List.length ed_bs) ed_univs_closing) ts in

  let combinators = {
    ret_wp = ret_wp;
    bind_wp = bind_wp;
    stronger = stronger;
    if_then_else = if_then_else;
    ite_wp = ite_wp;
    close_wp = close_wp;
    trivial = trivial;

    repr = repr;
    return_repr = return_repr;
    bind_repr = bind_repr;
  } in

  let combinators = U.apply_wp_eff_combinators cl combinators in
  let combinators =
    match ed.combinators with
    | Primitive_eff _ -> Primitive_eff combinators
    | DM4F_eff _ -> DM4F_eff combinators
    | _ -> failwith "Impossible! tc_eff_decl on a layered effect is not expected" in

  //univs and binders have already been set
  let ed = { ed with
    signature     =cl signature;
    combinators   = combinators;
    actions       =
      List.map (fun a ->
        { a with
          action_typ  = cl (a.action_univs, a.action_typ) |> snd;
          action_defn = cl (a.action_univs, a.action_defn) |> snd }) actions } in

  if Env.debug env <| Options.Other "ED" then
    BU.print1 "Typechecked effect declaration:\n\t%s\n" (Print.eff_decl_to_string false ed);

  ed

let tc_eff_decl env ed quals =
  (if ed |> U.is_layered then tc_layered_eff_decl else tc_non_layered_eff_decl) env ed quals

let monad_signature env m s =
 let fail () = raise_error (Err.unexpected_signature_for_monad env m s) (range_of_lid m) in
 let s = SS.compress s in
 match s.n with
  | Tm_arrow(bs, c) ->
    let bs = SS.open_binders bs in
    begin match bs with
        | [(a, _);(wp, _)] -> a, wp.sort
        | _ -> fail ()
    end
  | _ -> fail ()

(*
 * Typecheck lift to/from a layered effect
 *
 *)
let tc_layered_lift env0 (sub:S.sub_eff) : S.sub_eff =
  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "Typechecking sub_effect: %s\n" (Print.sub_eff_to_string sub);

  let us, lift = sub.lift |> must in
  let r = lift.pos in

  begin
    let src_ed = Env.get_effect_decl env0 sub.source in
    let tgt_ed = Env.get_effect_decl env0 sub.target in
    if (src_ed |> U.is_layered &&  //source is a layered effect
        lid_equals (src_ed |> U.get_layered_effect_base |> must) tgt_ed.mname) ||  //and target is its underlying effect, or
       (tgt_ed |> U.is_layered &&  // target is a layered effect
        lid_equals (tgt_ed |> U.get_layered_effect_base |> must) src_ed.mname &&  //and source is its underlying effect 
        not (lid_equals src_ed.mname PC.effect_PURE_lid))  //and source is not PURE
    then
      raise_error (Errors.Fatal_EffectsCannotBeComposed,
                   BU.format2 "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     (src_ed.mname |> Ident.string_of_lid) (tgt_ed.mname |> Ident.string_of_lid)) r
  end;



  let env, us, lift =
    if List.length us = 0 then env0, us, lift
    else
      let us, lift = SS.open_univ_vars us lift in
      Env.push_univ_vars env0 us, us, lift in

  (*
   * We typecheck the lift term (without any expected type)
   *   and then unify its type with the expected lift type
   *)

  let lift, lc, g = tc_tot_or_gtot_term env lift in
  Rel.force_trivial_guard env g;

  let lift_ty = lc.res_typ |> N.normalize [Beta] env0 in

  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print2 "Typechecked lift: %s and lift_ty: %s\n"
      (Print.term_to_string lift) (Print.term_to_string lift_ty);

  let lift_t_shape_error s = BU.format4
    "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
    (Ident.string_of_lid sub.source) (Ident.string_of_lid sub.target)
    s (Print.term_to_string lift_ty) in

  (*
   * Construct the expected lift type k as:
   *   a:Type -> <some binders> -> f:source_repr a f_i_1 ... f_i_n : target_repr a i_1 ... i_m
   *)
  let k, g_k =
    let a, u_a = U.type_u () |> (fun (t, u) -> S.gen_bv "a" None t |> S.mk_binder, u) in

    //a:Type u

    //other binders
    let rest_bs =
      match (SS.compress lift_ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 2 ->
        let ((a', _)::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 1) |> fst
           |> SS.subst_binders [NT (a', bv_to_name (fst a))]
      | _ ->
        raise_error (Errors.Fatal_UnexpectedExpressionType,
          lift_t_shape_error "either not an arrow, or not enough binders") r in

    let f_b, g_f_b =
      let f_sort, g = TcUtil.fresh_effect_repr_en
        (Env.push_binders env (a::rest_bs)) r sub.source u_a (a |> fst |> S.bv_to_name) in
      S.gen_bv "f" None f_sort |> S.mk_binder, g in

    let bs = a::(rest_bs@[f_b]) in

    //repr<?u> ?u_i ... ?u_n
    let repr, g_repr = TcUtil.fresh_effect_repr_en
      (Env.push_binders env bs)
      r sub.target u_a (a |> fst |> S.bv_to_name) in
    
    U.arrow bs (mk_Total' repr (new_u_univ () |> Some)), Env.conj_guard g_f_b g_repr in

   if Env.debug env <| Options.Other "LayeredEffects" then
    BU.print1 "tc_layered_lift: before unification k: %s\n" (Print.term_to_string k);

  let g = Rel.teq env lift_ty k in
  Rel.force_trivial_guard env g_k; Rel.force_trivial_guard env g;

  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "After unification k: %s\n" (Print.term_to_string k);

  //generalize
  let us, lift, lift_wp =
    let inst_us, lift = TcUtil.generalize_universes env0 lift in
    if List.length inst_us <> 1
    then raise_error (Errors.Fatal_MismatchUniversePolymorphic, BU.format4
      "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
      (Ident.string_of_lid sub.source) (Ident.string_of_lid sub.target)
      (inst_us |> List.length |> string_of_int) (Print.term_to_string lift)) r;

    if List.length us = 0 ||
       (List.length us = List.length inst_us &&
        List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) us inst_us)
    then inst_us, lift,
         k |> N.remove_uvar_solutions env |> SS.close_univ_vars inst_us
    else 
       raise_error (Errors.Fatal_UnexpectedNumberOfUniverse, BU.format5
         "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
         (Ident.string_of_lid sub.source) (Ident.string_of_lid sub.target)
         (us |> List.length |> string_of_int) (inst_us |> List.length |> string_of_int)
         (Print.term_to_string lift)) r in
       
  let sub = { sub with
    lift = Some (us, lift);
    lift_wp = Some (us, lift_wp) } in

  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "Final sub_effect: %s\n" (Print.sub_eff_to_string sub);

  sub

let tc_lift env sub r =
  let ed_src = Env.get_effect_decl env sub.source in
  let ed_tgt = Env.get_effect_decl env sub.target in

  if ed_src |> U.is_layered || ed_tgt |> U.is_layered
  then tc_layered_lift env sub
  else
    let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
    let b, wp_b_tgt = monad_signature env sub.target (Env.lookup_effect_lid env sub.target) in
    let wp_a_tgt    = SS.subst [NT(b, S.bv_to_name a)] wp_b_tgt in
    let expected_k  = U.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
    let repr_type eff_name a wp =
      if not (is_reifiable_effect env eff_name)
      then raise_error (Errors.Fatal_EffectCannotBeReified, (BU.format1 "Effect %s cannot be reified" eff_name.str)) (Env.get_range env);
      match Env.effect_decl_opt env eff_name with
      | None -> failwith "internal error: reifiable effect has no decl?"
      | Some (ed, qualifiers) ->
        let repr = Env.inst_effect_fun_with [U_unknown] env ed (ed |> U.get_eff_repr |> must) in
        mk (Tm_app(repr, [as_arg a; as_arg wp])) None (Env.get_range env)
    in
    let lift, lift_wp =
      match sub.lift, sub.lift_wp with
      | None, None -> failwith "Impossible (parser)"
      | lift, Some (uvs, lift_wp) ->
        //AR: open the universes, if present (two phases)
        let env, lift_wp =
          if List.length uvs > 0 then
            let usubst, uvs = SS.univ_var_opening uvs in
            Env.push_univ_vars env uvs, SS.subst usubst lift_wp
          else env, lift_wp
        in
        (* Covers both the "classic" format and the reifiable case. *)
        //AR: if universes are already annotated, simply close, else generalize
        let lift_wp = if List.length uvs = 0 then check_and_gen env lift_wp expected_k
                      else let lift_wp = tc_check_trivial_guard env lift_wp expected_k in uvs, SS.close_univ_vars uvs lift_wp
        in
        lift, lift_wp
      (* Sub-effect for free case *)
      | Some (what, lift), None ->
        //AR: open the universes if present (two phases)
        let uvs, lift =
          if List.length what > 0
          then let usubst, uvs = SS.univ_var_opening what in
               uvs, SS.subst usubst lift
          else [], lift
        in
        if Env.debug env (Options.Other "ED")
        then BU.print1 "Lift for free : %s\n" (Print.term_to_string lift);
        let dmff_env = DMFF.empty env (tc_constant env Range.dummyRange) in
        let lift, comp, _ = tc_term (Env.push_univ_vars env uvs) lift in  //AR: push univs in the env
        (* TODO : Check that comp is pure ? *)
        let _, lift_wp, lift_elab = DMFF.star_expr dmff_env lift in
        let lift_wp = DMFF.recheck_debug "lift-wp" env lift_wp in
        let lift_elab = DMFF.recheck_debug "lift-elab" env lift_elab in
        if List.length uvs = 0 then Some (TcUtil.generalize_universes env lift_elab), TcUtil.generalize_universes env lift_wp
        else Some (uvs, SS.close_univ_vars uvs lift_elab), (uvs, SS.close_univ_vars uvs lift_wp)
    in
    (* we do not expect the lift to verify, *)
    (* since that requires internalizing monotonicity of WPs *)
    let env = {env with lax=true} in
    let lift = match lift with
    | None -> None
    | Some (uvs, lift) ->
      let env, lift =
        let usubst, uvs = SS.univ_var_opening uvs in
        Env.push_univ_vars env uvs, SS.subst usubst lift
      in
      let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
      let wp_a = S.new_bv None wp_a_src in
      let a_typ = S.bv_to_name a in
      let wp_a_typ = S.bv_to_name wp_a in
      let repr_f = repr_type sub.source a_typ wp_a_typ in
      let repr_result =
        let lift_wp = N.normalize [Env.EraseUniverses; Env.AllowUnboundUniverses] env (snd lift_wp) in
        let lift_wp_a = mk (Tm_app(lift_wp, [as_arg a_typ; as_arg wp_a_typ])) None (Env.get_range env) in
        repr_type sub.target a_typ lift_wp_a in
      let expected_k =
        U.arrow [S.mk_binder a; S.mk_binder wp_a; S.null_binder repr_f]
                (S.mk_Total repr_result) in
      let expected_k, _, _ =
        tc_tot_or_gtot_term env expected_k in
      let lift =
        if List.length uvs = 0 then check_and_gen env lift expected_k
        else
          let lift = tc_check_trivial_guard env lift expected_k in
          uvs, SS.close_univ_vars uvs lift in
        Some lift
    in
    //check that sub effecting is universe polymorphic in exactly one universe
    if lift_wp |> fst |> List.length <> 1 then
    raise_error (Errors.Fatal_TooManyUniverse, (BU.format3 "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                                           (Print.lid_to_string sub.source) (Print.lid_to_string sub.target)
                                                           (lift_wp |> fst |> List.length |> string_of_int))) r;
    if is_some lift && lift |> must |> fst |> List.length <> 1 then
      raise_error (Errors.Fatal_TooManyUniverse, (BU.format3 "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                                             (Print.lid_to_string sub.source) (Print.lid_to_string sub.target)
                                                             (lift |> must |> fst |> List.length |> string_of_int))) r;
    ({ sub with lift_wp=Some lift_wp; lift=lift })

let tc_effect_abbrev env (lid, uvs, tps, c) r =
  let env0 = env in
  //assert (uvs = []); AR: not necessarily, two phases

  //AR: open universes in tps and c if needed
  let env, uvs, tps, c =
    if List.length uvs = 0 then env, uvs, tps, c
    else
      let usubst, uvs = SS.univ_var_opening uvs in
      let tps = SS.subst_binders usubst tps in
      let c = SS.subst_comp (SS.shift_subst (List.length tps) usubst) c in
      Env.push_univ_vars env uvs, uvs, tps, c
  in
  let env = Env.set_range env r in
  let tps, c = SS.open_comp tps c in
  let tps, env, us = tc_tparams env tps in
  let c, u, g = tc_comp env c in
  Rel.force_trivial_guard env g;
  let _ =
    let expected_result_typ =
      match tps with
      | (x, _)::_ -> S.bv_to_name x
      | _ -> raise_error (Errors.Fatal_NotEnoughArgumentsForEffect,
                         "Effect abbreviations must bind at least the result type")
                        r
    in
    let def_result_typ = FStar.Syntax.Util.comp_result c in
    if not (Rel.teq_nosmt_force env expected_result_typ def_result_typ)
    then raise_error (Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                      BU.format2 "Result type of effect abbreviation `%s` \
                                  does not match the result type of its definition `%s`"
                                  (Print.term_to_string expected_result_typ)
                                  (Print.term_to_string def_result_typ))
                     r
  in
  let tps = SS.close_binders tps in
  let c = SS.close_comp tps c in
  let uvs, t = TcUtil.generalize_universes env0 (mk (Tm_arrow(tps, c)) None r) in
  let tps, c = match tps, (SS.compress t).n with
    | [], Tm_arrow(_, c) -> [], c
    | _,  Tm_arrow(tps, c) -> tps, c
    | _ -> failwith "Impossible (t is an arrow)" in
  if List.length uvs <> 1
  then begin
    let _, t = Subst.open_univ_vars uvs t in
    raise_error (Errors.Fatal_TooManyUniverse,
                 BU.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                  (Print.lid_to_string lid)
                                  (List.length uvs |> BU.string_of_int)
                                  (Print.term_to_string t)) r
  end;
  (lid, uvs, tps, c)
