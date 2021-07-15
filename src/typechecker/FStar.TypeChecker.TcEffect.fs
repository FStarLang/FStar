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
open FStar.Pervasives
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
module Gen = FStar.TypeChecker.Generalize

module BU = FStar.Util

let dmff_cps_and_elaborate env ed =
  (* This is only an elaboration rule not a typechecking one *)

  // Let the power of Dijkstra generate everything "for free", then defer
  // the rest of the job to [tc_decl].
  DMFF.cps_and_elaborate env ed

(*
 * Helper function used to typecheck and generalize various effect combinators
 *
 * comb is the name of the combinator (used for error messages)
 * n is the number of universes that the combinator should be polymorphic in
 * (us, t) is the tscheme to check and generalize (us will be [] in the first phase)
 *)
let check_and_gen env (eff_name:string) (comb:string) (n:int) (us, t) : (univ_names * term * typ) =
  let us, t = SS.open_univ_vars us t in
  let t, ty =
    let t, lc, g = tc_tot_or_gtot_term (Env.push_univ_vars env us) t in
    Rel.force_trivial_guard env g;
    t, lc.res_typ in
  let g_us, t = Gen.generalize_universes env t in
  let ty = SS.close_univ_vars g_us ty in
  //check that n = List.length g_us and that if us is set, it is same as g_us
  let univs_ok =
    if List.length g_us <> n then
      let error = BU.format5
        "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
        eff_name comb (string_of_int n) (g_us |> List.length |> string_of_int)
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
               eff_name comb (Print.univ_names_to_string us) (Print.univ_names_to_string g_us)))
            t.pos in
  g_us, t, ty

(*
 * A small gadget to get a uvar for pure wp with given result type
 *)
let pure_wp_uvar env (t:typ) (reason:string) (r:Range.range) : term * guard_t =
  let pure_wp_t =
    let pure_wp_ts = Env.lookup_definition [Env.NoDelta] env PC.pure_wp_lid |> must in
    let _, pure_wp_t = Env.inst_tscheme pure_wp_ts in
    S.mk_Tm_app
      pure_wp_t
      [t |> S.as_arg]
      r in

  let pure_wp_uvar, _, guard_wp = Env.new_implicit_var_aux reason r env pure_wp_t Allow_untyped None in
  pure_wp_uvar, guard_wp


(*
 * For all the layered effects combinators, we enforce that their types are
 *   typeable without using subtyping
 *
 * This is to guard against unsoundness creeping in because of using Untyped uvars
 *   when applying these combinators
 *
 * Essentially we want to ensure that uvars are not introduces at a type different than
 *   what they are used at
 *)
let check_no_subtyping_for_layered_combinator env (t:term) (k:option<typ>) =
  if Env.debug env <| Options.Other "LayeredEffectsTc"
  then BU.print2 "Checking that %s is well typed with no subtyping (k:%s)\n"
         (Print.term_to_string t)
         (match k with
          | None -> "None"
          | Some k -> Print.term_to_string k);

  let env = ({ env with use_eq_strict = true }) in
  match k with
  | None -> ignore (tc_trivial_guard env t)
  | Some k -> ignore (tc_check_trivial_guard env t k)


(*
 * Check that the layered effect binders that will be solved by unification,
 *   appear in the repr indices in the combinator type in a head position
 *
 * For example, appearing in an argument position in an index term does not count
 *
 * If the flag check_non_informative_binders is set, additionally checks that the
 *   binders have non-informative types
 *
 * Precondition: repr_terms may not be well-typed in env but bs must be well-typed (properly closed etc.)
 * To check for non_informativeness, we do some normalization, so bs well-typedness is required
 *)
let validate_layered_effect_binders env (bs:binders) (repr_terms:list<term>) (check_non_informatve_binders:bool) (r:Range.range)
: unit
= //repr can be (repr a is) or unit -> M a wp for wp effects
  let repr_args repr =
    match (SS.compress repr).n with
    | Tm_app (_, args) -> args
    | Tm_arrow ([_], c) -> c |> U.comp_effect_args
    | _ ->
      raise_error (Errors.Fatal_UnexpectedEffect,
        BU.format1 "Unexpected repr term %s when validating layered effect combinator binders"
          (Print.term_to_string repr)) r in

  let rec head_names_in_term arg =
    match (SS.compress arg).n with
    | Tm_name _ -> [arg]
    | Tm_app (head, _) ->
      (match (SS.compress head).n with
       | Tm_name _ -> [head]
       | _-> [])
    | Tm_abs (_, body, _) -> head_names_in_term body
    | _ -> [] in

  let head_names_in_args args =
    args
    |> List.map fst
    |> List.collect head_names_in_term in

  let repr_names_args = List.collect (fun repr -> repr |> repr_args |> head_names_in_args) repr_terms in

  if Env.debug env <| Options.Other "LayeredEffectsTc" then
    BU.print2 "Checking layered effect combinator binders validity, names: %s, binders: %s\n\n"
      (List.fold_left (fun s t -> s ^ "; " ^ (Print.term_to_string t)) "" repr_names_args)
      (Print.binders_to_string "; " bs);

  let valid_binder b =
    //it appears in a repr index in a head position
    List.existsb (fun t -> U.eq_tm (S.bv_to_name b.binder_bv) t = U.Equal) repr_names_args
    ||
    (match b.binder_attrs with  //or has a tactic associated
     | _::_ -> true
     | _ -> false) in

  let invalid_binders = List.filter (fun b -> not (valid_binder b)) bs in
  if List.length invalid_binders <> 0 then
    raise_error (Errors.Fatal_UnexpectedEffect,
      BU.format1 "Binders %s neither appear as repr indices nor have an associated tactic"
        (Print.binders_to_string "; " invalid_binders)) r
  else ();

  if check_non_informatve_binders
  then
    let _, informative_binders = List.fold_left (fun (env, bs) b ->
      let env = Env.push_binders env [b] in
      if N.non_info_norm env b.binder_bv.sort
      then (env, bs)
      else (env, b::bs)) (env, []) bs in
    if List.length informative_binders <> 0 then
      raise_error (Errors.Fatal_UnexpectedEffect,
        BU.format1 "Binders %s are informative while the effect is reifiable"
          (Print.binders_to_string "; " informative_binders)) r
    else ()
  else ()


(*
 * Typechecking of layered effects
 *)
let tc_layered_eff_decl env0 (ed : S.eff_decl) (quals : list<qualifier>) (attrs : list<S.attribute>) =
Errors.with_ctx (BU.format1 "While checking layered effect definition `%s`" (string_of_lid ed.mname)) (fun () ->
  if Env.debug env0 <| Options.Other "LayeredEffectsTc" then
    BU.print1 "Typechecking layered effect: \n\t%s\n" (Print.eff_decl_to_string false ed);

  //we don't support effect binders in layered effects yet
  if List.length ed.univs <> 0 || List.length ed.binders <> 0 then
    raise_error
      (Errors.Fatal_UnexpectedEffect, "Binders are not supported for layered effects (" ^ (string_of_lid ed.mname) ^")")
      (range_of_lid ed.mname);

  let log_combinator s (us, t, ty) =
    if Env.debug env0 <| Options.Other "LayeredEffectsTc" then
      BU.print4 "Typechecked %s:%s = %s:%s\n"
        (string_of_lid ed.mname) s
        (Print.tscheme_to_string (us, t)) (Print.tscheme_to_string (us, ty)) in

  //helper function to get (a:Type ?u), returns the binder and ?u
  let fresh_a_and_u_a (a:string) : binder * universe = U.type_u () |> (fun (t, u) -> S.gen_bv a None t |> S.mk_binder, u) in
  //helper function to get (x:a)
  let fresh_x_a (x:string) (a:binder) : binder = S.gen_bv x None (S.bv_to_name a.binder_bv) |> S.mk_binder in


  (*
   * We now typecheck various combinators
   * In all the cases we take the following approach:
   *   - Typecheck the combinator (with no expected type)
   *   - Construct an expected type (k) using uvars
   *   - Unify the type of the combinator (as typechecked) with k
   *   - Record k in the effect declaration (along with the combinator)
   *)

  let check_and_gen = check_and_gen env0 (string_of_lid ed.mname) in


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
    let rest_bs = TcUtil.layered_effect_indices_as_binders env r ed.mname (sig_us, sig_t) u (a.binder_bv |> S.bv_to_name) in
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
  let repr =
    let repr_ts = ed |> U.get_eff_repr |> must in
    let r = (snd repr_ts).pos in
    let repr_us, repr_t, repr_ty = check_and_gen "repr" 1 repr_ts in

    
    let us, ty = SS.open_univ_vars repr_us repr_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u = fresh_a_and_u_a "a" in
    let rest_bs =
      let signature_ts = let us, t, _ = signature in (us, t) in
      TcUtil.layered_effect_indices_as_binders env r ed.mname signature_ts u (a.binder_bv |> S.bv_to_name) in
    let bs = a::rest_bs in
    let k = U.arrow bs (U.type_u () |> (fun (t, u) -> S.mk_Total' t (Some (new_u_univ ())))) in  //note the universe of Tot need not be u
    let g = Rel.teq env ty k in
    Rel.force_trivial_guard env g;
    (repr_us, repr_t, SS.close_univ_vars us (k |> N.remove_uvar_solutions env))
  in

  log_combinator "repr" repr;

  //helper function that creates an application node (repr<u> a_tm ?u1 ... ?un)
  //returns the application term and the guard for the introduced uvars (see TcUtil.fresh_layered_effect_repr)
  let fresh_repr r env u a_tm =
    let signature_ts = let us, t, _ = signature in (us, t) in
    let repr_ts = let us, t, _ = repr in (us, t) in
    TcUtil.fresh_effect_repr env r ed.mname signature_ts (Some repr_ts) u a_tm in

  let not_an_arrow_error comb n t r =
    raise_error (Errors.Fatal_UnexpectedEffect,
      BU.format5 "Type of %s:%s is not an arrow with >= %s binders (%s::%s)" (string_of_lid ed.mname) comb
        (string_of_int n) (Print.tag_of_term t) (Print.term_to_string t)
    ) r in

  let check_non_informative_binders =
    List.contains S.Reifiable quals &&
    not (U.has_attribute attrs PC.allow_informative_binders_attr) in

  (*
   * return_repr
   *
   * return_repr must have type:
   *   a:Type -> x:a -> <some binders> -> repr a i_1 ... i_n  //polymorphic in one universe (that of a)
   *   where i_1 ... i_n are terms of effect indices types (as in the signature)
   *
   * The binders have arbitrary sorts
   *
   * The positioning of the binders is a little asymmetric with other binders,
   *   e.g. in others, the binders are stuffed in the middle
   *   but this seems ok for return where the remaining binder is always a value (x:a)
   *   and not a repr
   *)
  let return_repr =
    let return_repr_ts = ed |> U.get_return_repr |> must in
    let r = (snd return_repr_ts).pos in
    let ret_us, ret_t, ret_ty = check_and_gen "return_repr" 1 return_repr_ts in

    let us, ty = SS.open_univ_vars ret_us ret_ty in
    let env = Env.push_univ_vars env0 us in

    check_no_subtyping_for_layered_combinator env ty None;

    let a, u_a = fresh_a_and_u_a "a" in
    let x_a = fresh_x_a "x" a in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 2 ->
        let (({binder_bv=a'})::({binder_bv=x'})::bs) = SS.open_binders bs in
        bs |> SS.subst_binders [NT (a', bv_to_name a.binder_bv)]
           |> SS.subst_binders [NT (x', bv_to_name x_a.binder_bv)]
      | _ -> not_an_arrow_error "return" 2 ty r in
    let bs = a::x_a::rest_bs in
    let repr, g = fresh_repr r (Env.push_binders env bs) u_a (a.binder_bv |> S.bv_to_name) in
    let k = U.arrow bs (S.mk_Total' repr (Some u_a)) in
    let g_eq = Rel.teq env ty k in
    Rel.force_trivial_guard env (Env.conj_guard g g_eq);

    let k = k |> N.remove_uvar_solutions env in

    let _check_valid_binders =
      match (SS.compress k).n with
      | Tm_arrow (bs, c) ->
        let a::x::bs, c = SS.open_comp bs c in
        let res_t = U.comp_result c in
        let env = Env.push_binders env [a; x] in
        validate_layered_effect_binders env bs [res_t] check_non_informative_binders r in

    ret_us, ret_t, k |> SS.close_univ_vars us in

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

    check_no_subtyping_for_layered_combinator env ty None;

    let a, u_a = fresh_a_and_u_a "a" in
    let b, u_b = fresh_a_and_u_a "b" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 4 ->
        let (({binder_bv=a'})::({binder_bv=b'})::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 2) |> fst
           |> SS.subst_binders [NT (a', bv_to_name a.binder_bv); NT (b', bv_to_name b.binder_bv)] 
      | _ -> not_an_arrow_error "bind" 4 ty r in
    let bs = a::b::rest_bs in
    let f, guard_f =
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (a.binder_bv |> S.bv_to_name) in
      S.gen_bv "f" None repr |> S.mk_binder, g in
    let g, guard_g =
      let x_a = fresh_x_a "x" a in
      let repr, g = fresh_repr r (Env.push_binders env (bs@[x_a])) u_b (b.binder_bv |> S.bv_to_name) in
      S.gen_bv "g" None (U.arrow [x_a] (S.mk_Total' repr (Some (new_u_univ ())))) |> S.mk_binder, g in
    let repr, guard_repr = fresh_repr r (Env.push_binders env bs) u_b (b.binder_bv |> S.bv_to_name) in

    //the computation type of the bind combinator can be a PURE type
    let pure_wp_uvar, g_pure_wp_uvar = pure_wp_uvar (Env.push_binders env bs) repr
      (BU.format1 "implicit for pure_wp in checking bind for %s" (string_of_lid ed.mname))
      r in

    let k = U.arrow (bs@[f; g]) (S.mk_Comp ({
      comp_univs = [ Env.new_u_univ () ];
      effect_name = PC.effect_PURE_lid;
      result_typ = repr;
      effect_args = [ pure_wp_uvar |> S.as_arg ];
      flags = [] })) in

    let guard_eq = Rel.teq env ty k in
    List.iter (Rel.force_trivial_guard env) [guard_f; guard_g; guard_repr; g_pure_wp_uvar; guard_eq];

    let k = k |> N.remove_uvar_solutions env in

    let _check_valid_binders =
      match (SS.compress k).n with
      | Tm_arrow (bs, c) ->
        let a::b::bs, c = SS.open_comp bs c in
        let res_t = U.comp_result c in
        let bs, f_b, g_b =
          List.splitAt (List.length bs - 2) bs
          |> (fun (l1, l2) -> l1,
                          l2 |> List.hd, l2 |> List.tl |> List.hd) in
        (*
         * AR: CAUTION: a little lax about opening g_b with the x:a binder
         *              g_sort is only used for repr terms, validate_layered_effect_binders does not expect
         *                it to be closed in env
         *)
        let g_sort =
          match (SS.compress g_b.binder_bv.sort).n with
          | Tm_arrow (_, c) -> U.comp_result c in
        let env = Env.push_binders env [a; b] in
        validate_layered_effect_binders env bs [f_b.binder_bv.sort; g_sort; res_t]
          check_non_informative_binders r in

    bind_us, bind_t, k |> SS.close_univ_vars bind_us in

  log_combinator "bind_repr" bind_repr;

  (*
   * stronger_repr
   *
   * stronger_repr must have type:
   *   a:Type -> <some binders> -> f:repr a i_1 ... i_n -> PURE (repr a j_1 ... j_n) wp //polymorphic in one universe (that of a)
   *   where i, j are terms of effect indices types (as in the signature)
   *
   * The binders have arbitrary sorts
   *
   * The combinator is optional, indicated by a Tm_unknown
   * If so, we add a default combinator as: fun (a:Type) (signature_bs) (f:repr a signature_bs) -> f
   * 
   *)
  let stronger_repr =
    let stronger_repr =
      let ts = ed |> U.get_stronger_repr |> must in
      match (ts |> snd |> SS.compress).n with
      | Tm_unknown ->
        let signature_ts = let (us, t, _) = signature in (us, t) in
        let _, signature_t = Env.inst_tscheme_with signature_ts [U_unknown] in
        (match (SS.compress signature_t).n with
         | Tm_arrow (bs, _) ->
           let bs = SS.open_binders bs in
           let repr_t =
             let repr_ts = let (us, t, _) = repr in (us, t) in
             Env.inst_tscheme_with repr_ts [U_unknown] |> snd in
           let repr_t_applied = mk
             (Tm_app (repr_t, bs |> List.map (fun b -> b.binder_bv) |> List.map S.bv_to_name |> List.map S.as_arg))
             Range.dummyRange in
           let f_b = S.null_binder repr_t_applied in
           [], U.abs (bs@[f_b]) (f_b.binder_bv |> S.bv_to_name) None
         | _ -> failwith "Impossible!")
      | _ -> ts in
        
    let r = (snd stronger_repr).pos in

    let stronger_us, stronger_t, stronger_ty = check_and_gen "stronger_repr" 1 stronger_repr in

    if Env.debug env0 <| Options.Other "LayeredEffectsTc" then
      BU.print2 "stronger combinator typechecked with term: %s and type: %s\n"
        (Print.tscheme_to_string (stronger_us, stronger_t))
        (Print.tscheme_to_string (stronger_us, stronger_ty));

    let us, ty = SS.open_univ_vars stronger_us stronger_ty in
    let env = Env.push_univ_vars env0 us in

    check_no_subtyping_for_layered_combinator env ty None;

    let a, u = fresh_a_and_u_a "a" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 2 ->
        let (({binder_bv=a'})::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 1) |> fst
           |> SS.subst_binders [NT (a', bv_to_name a.binder_bv)]
      | _ -> not_an_arrow_error "stronger" 2 ty r in
    let bs = a::rest_bs in
    let f, guard_f =
      let repr, g = fresh_repr r (Env.push_binders env bs) u (a.binder_bv |> S.bv_to_name) in
      S.gen_bv "f" None repr |> S.mk_binder, g in
    let ret_t, guard_ret_t = fresh_repr r (Env.push_binders env bs) u (a.binder_bv |> S.bv_to_name) in

    let pure_wp_uvar, guard_wp = pure_wp_uvar (Env.push_binders env bs) ret_t 
      (BU.format1 "implicit for pure_wp in checking stronger for %s" (string_of_lid ed.mname))
      r in
    let c = S.mk_Comp ({
      comp_univs = [ Env.new_u_univ () ];
      effect_name = PC.effect_PURE_lid;
      result_typ = ret_t;
      effect_args = [ pure_wp_uvar |> S.as_arg ];
      flags = [] }) in

    let k = U.arrow (bs@[f]) c in

    if Env.debug env <| Options.Other "LayeredEffectsTc" then
      BU.print1 "Expected type of subcomp before unification: %s\n"
        (Print.term_to_string k);

    let guard_eq = Rel.teq env ty k in
    List.iter (Rel.force_trivial_guard env) [guard_f; guard_ret_t; guard_wp; guard_eq];

    let k = k |> N.remove_uvar_solutions env in

    let _check_valid_binders =
      match (SS.compress k).n with
      | Tm_arrow (bs, c) ->
        let a::bs,c = SS.open_comp bs c in
        let res_t = U.comp_result c in
        let bs, f_b =
          List.splitAt (List.length bs - 1) bs
          |> (fun (l1, l2) -> l1, List.hd l2) in
        let env = Env.push_binders env [a] in
        validate_layered_effect_binders env bs [f_b.binder_bv.sort; res_t]
          check_non_informative_binders r in

    stronger_us, stronger_t, k |> SS.close_univ_vars stronger_us in

  log_combinator "stronger_repr" stronger_repr;

  (*
   * This combinator is also optional
   * If so, we add a default:
   * fun (a:Type) (signature_bs) (f:repr a signature_bs) (g:repr a signature_bs) (b:bool) -> repr a signature_bs
   *)
  let if_then_else =
    let if_then_else_ts =
      let ts = ed |> U.get_layered_if_then_else_combinator |> must in
      match (ts |> snd |> SS.compress).n with
      | Tm_unknown ->
        let signature_ts = let (us, t, _) = signature in (us, t) in
        let _, signature_t = Env.inst_tscheme_with signature_ts [U_unknown] in
        (match (SS.compress signature_t).n with
         | Tm_arrow (bs, _) ->
           let bs = SS.open_binders bs in
           let repr_t =
             let repr_ts = let (us, t, _) = repr in (us, t) in
             Env.inst_tscheme_with repr_ts [U_unknown] |> snd in
           let repr_t_applied = mk
             (Tm_app (repr_t, bs |> List.map (fun b -> b.binder_bv) |> List.map S.bv_to_name |> List.map S.as_arg))
             Range.dummyRange in
           let f_b = S.null_binder repr_t_applied in
           let g_b = S.null_binder repr_t_applied in
           let b_b = S.null_binder U.t_bool in
           [], U.abs (bs@[f_b; g_b; b_b]) repr_t_applied None
         | _ -> failwith "Impossible!")
      | _ -> ts in

    let r = (snd if_then_else_ts).pos in
    let if_then_else_us, if_then_else_t, if_then_else_ty = check_and_gen "if_then_else" 1 if_then_else_ts in

    let us, t = SS.open_univ_vars if_then_else_us if_then_else_t in
    let _, ty = SS.open_univ_vars if_then_else_us if_then_else_ty in
    let env = Env.push_univ_vars env0 us in

    check_no_subtyping_for_layered_combinator env t (Some ty);

    let a, u_a = fresh_a_and_u_a "a" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 4 ->
        let (({binder_bv=a'})::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 3) |> fst
           |> SS.subst_binders [NT (a', a.binder_bv |> S.bv_to_name)]
      | _ -> not_an_arrow_error "if_then_else" 4 ty r in
    let bs = a::rest_bs in
    let f_bs, guard_f =
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (a.binder_bv |> S.bv_to_name) in
      S.gen_bv "f" None repr |> S.mk_binder, g in
    let g_bs, guard_g =
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (a.binder_bv |> S.bv_to_name) in
      S.gen_bv "g" None repr |> S.mk_binder, g in
    let p_b = S.gen_bv "p" None U.t_bool |> S.mk_binder in
    let t_body, guard_body = fresh_repr r (Env.push_binders env (bs@[p_b])) u_a (a.binder_bv |> S.bv_to_name) in
    let k = U.abs (bs@[f_bs; g_bs; p_b]) t_body None in
    let guard_eq = Rel.teq env t k in
    [guard_f; guard_g; guard_body; guard_eq] |> List.iter (Rel.force_trivial_guard env);

    let k = k |> N.remove_uvar_solutions env in

    let _check_valid_binders =
      match (SS.compress k).n with
      | Tm_abs (bs, body, _) ->
        let a::bs, body = SS.open_term bs body in
        let bs, f_b, g_b =
          List.splitAt (List.length bs - 3) bs
          |> (fun (l1, l2) -> l1,
                          l2 |> List.hd, l2 |> List.tl |> List.hd) in
        let env = Env.push_binders env [a] in
        validate_layered_effect_binders env bs [f_b.binder_bv.sort; g_b.binder_bv.sort; body]
          check_non_informative_binders r in

    if_then_else_us,
    k |> SS.close_univ_vars if_then_else_us,
    if_then_else_ty in

  log_combinator "if_then_else" if_then_else;


  (*
   * Checking the soundness of the if_then_else combinator
   *
   * In all combinators, other than if_then_else, the soundness is ensured
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
   * The way we program it is as follows:
   *
   * First for ite : a:Type -> bs -> f:repr a is -> g:repr a js -> p:bool -> Type,
   *   we create a fully applied (ite a bs f g p) term,
   *   where a, bs, f, g, and p are fresh names
   *
   * Note that beta-reducing this term gives us a (repr a ks) term
   *
   * Next, when subcomp : a:Type -> bs -> f:repr a s_is -> Pure (repr a s_js) pre post,
   *   we create fresh uvars for bs, where a is substituted by the a:Type
   *   name from the ite combinator
   *
   * To check the then branch, we unify (repr a s_is) with the sort of f binder
   *   from the ite combinator, and (repr a s_js) with (repr a ks), i.e. the
   *   beta-normal form of the fully applied ite combinator
   *
   * In addition, we produce an smt guard from pre
   *
   * To get flow-sensitivity (i.e. p ==>), the env that we do all this in,
   *   has a (squash p) binder
   *
   * Finally, we discharge all the guards
   *
   * Similarly we check the else branch by unifying (repr a s_is) with g binder,
   *   in an environment with squash (not p)
   *
   * When the effect is annotated with ite_soundness_by attribute, the uvars that
   *   we create for subcomp are tagged with the argument of ite_soundness_by,
   *   and the smt guard is also put in a implicit tagged with this implicit
   *
   * Through the usual tactics dispatching, Rel dispatches these to the tactic
   *   if one is in scope
   *)
  let _if_then_else_is_sound = Errors.with_ctx "While checking if-then-else soundness" (fun () ->
    let r = (ed |> U.get_layered_if_then_else_combinator |> must |> snd).pos in

    (*
     * In constructing the application nodes for subcomp and if_then_else,
     *   we need to adjust the qualifiers
     *
     * Implicits remain implicits, but meta_attr or meta_arg just become implicits
     *
     * Don't think the boolean false below matters, but is perhaps safer (see Syntax.fsi)
     *)
    let binder_aq_to_arg_aq (aq, attrs) =
      match aq, attrs with
      | Some (Implicit _), _ -> aq
      | Some (Meta _), _ -> Some (Implicit false)
      | _ -> None in

    let ite_us, ite_t, _ = if_then_else in

    let us, ite_t = SS.open_univ_vars ite_us ite_t in
    let env, ite_t_applied, a_b, f_b, g_b, p_t =
      match (SS.compress ite_t).n with
      | Tm_abs (bs, _, _) ->
        let bs = SS.open_binders bs in
        let f_b, g_b, p_b =
          bs
          |> List.splitAt (List.length bs - 3)
          |> snd
          |> (fun l -> let [f; g; p] = l in f, g, p) in
        let env =  Env.push_binders (Env.push_univ_vars env0 us) bs in
        env,
        S.mk_Tm_app ite_t
          (bs |> List.map (fun b -> S.bv_to_name b.binder_bv, binder_aq_to_arg_aq (b.binder_qual, b.binder_attrs)))
          r |> N.normalize [Env.Beta] env,  //beta-reduce
        bs |> List.hd, f_b, g_b, (S.bv_to_name p_b.binder_bv)
      | _ -> failwith "Impossible! ite_t must have been an abstraction with at least 3 binders" in

    let subcomp_a_b, subcomp_bs, subcomp_f_b, subcomp_c =
      let _, _, subcomp_ty = stronger_repr in
      let _, subcomp_ty = SS.open_univ_vars us subcomp_ty in
      match (SS.compress subcomp_ty).n with
      | Tm_arrow (bs, c) ->
        let bs, c = SS.open_comp bs c in
        let a_b, rest_bs = List.hd bs, List.tl bs in
        let rest_bs, f_b =
          rest_bs |> List.splitAt (List.length rest_bs - 1)
                  |> (fun (l1, l2) -> l1, List.hd l2) in
        a_b, rest_bs, f_b, c
      | _ -> failwith "Impossible! subcomp_ty must have been an arrow with at lease 1 binder" in

    (*
     * An auxiliary function that we will call for then and else branches
     *
     * attr_opt is (Some arg) when there is an (ite_soundness_by arg) attribute on the effect
     *
     * The input env has the squash p (resp. squash (not p)) binder for the then (resp. else) branch
     *)
    let check_branch env ite_f_or_g_sort attr_opt : unit =
      let subst, uvars, g_uvars = subcomp_bs |> List.fold_left
        (fun (subst, uvars, g) b ->
         let sort = SS.subst subst b.binder_bv.sort in
         let t, _, g_t =
         (*
          * AR: TODO: now that we use fastpath for implicits checking,
          *           can this always be Strict?
          *)
         let uv_qual =
           if List.length b.binder_attrs > 0 ||
              attr_opt |> is_some
           then Strict
           else Allow_untyped in
         let ctx_uvar_meta = BU.map_option Ctx_uvar_meta_attr attr_opt in
         new_implicit_var_aux
           (BU.format1 "uvar for subcomp %s binder when checking ite soundness"
             (Print.binder_to_string b))
           r
           env
           sort
           uv_qual
           ctx_uvar_meta in
        subst@[NT (b.binder_bv, t)], uvars@[t], conj_guard g g_t)
        ([NT (subcomp_a_b.binder_bv, S.bv_to_name a_b.binder_bv)],
         [],
         Env.trivial_guard) in

      let subcomp_f_sort = SS.subst subst subcomp_f_b.binder_bv.sort in
      let c = SS.subst_comp subst subcomp_c |> Env.unfold_effect_abbrev env in

      let g_f_or_g = Rel.layered_effect_teq env subcomp_f_sort ite_f_or_g_sort None in
      let g_c = Rel.layered_effect_teq env c.result_typ ite_t_applied None in

      let fml = Env.pure_precondition_for_trivial_post
        env
        (List.hd c.comp_univs)
        c.result_typ
        (c.effect_args |> List.hd |> fst)
        r in
      let g_precondition =
        match attr_opt with
        | None -> fml  |> NonTrivial |> Env.guard_of_guard_formula
        | Some attr ->
          let _, _, g = new_implicit_var_aux "" r env
            (U.mk_squash S.U_zero fml)
            Strict
            (Ctx_uvar_meta_attr attr |> Some) in
          g in

      Rel.force_trivial_guard env (Env.conj_guards [g_uvars; g_f_or_g; g_c; g_precondition]) in

    let ite_soundness_tac_attr =
      match U.get_attribute PC.ite_soundness_by_attr attrs with
      | Some ((t, _)::_) -> Some t
      | _ -> None in

    let _check_then =
      let env = Env.push_bv env (S.new_bv None (U.mk_squash S.U_zero (p_t |> U.b2t))) in
      ignore (check_branch env f_b.binder_bv.sort ite_soundness_tac_attr) in

    let _check_else =
      let not_p = S.mk_Tm_app
        (S.lid_as_fv PC.not_lid S.delta_constant None |> S.fv_to_tm)
        [p_t |> U.b2t |> S.as_arg]
        r in
      let env = Env.push_bv env (S.new_bv None not_p) in
      ignore (check_branch env g_b.binder_bv.sort ite_soundness_tac_attr) in

    ()
  )  //Errors.with_ctx
  in


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
        (string_of_lid ed.mname) (string_of_lid act.action_name) (Print.binders_to_string "; " act.action_params)) r;

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
            r in
          let c = S.mk_Total' repr (Some (new_u_univ ())) in
          U.arrow bs c
        else act.action_typ
      | _ -> act.action_typ in
    
    let act_typ, _, g_t = tc_tot_or_gtot_term env act_typ in
    let act_defn, _, g_d = tc_tot_or_gtot_term
      ({ Env.set_expected_typ env act_typ with instantiate_imp = false })
      act.action_defn in
    
    if Env.debug env <| Options.Other "LayeredEffectsTc" then
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
          (string_of_lid ed.mname) (string_of_lid act.action_name) in
        let a_tm, _, g_tm = TcUtil.new_implicit_var reason r env t in
        let repr, g = fresh_repr r env u a_tm in
        U.arrow bs (S.mk_Total' repr (Env.new_u_univ () |> Some)), Env.conj_guard g g_tm
      | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType,
        BU.format3 "Unexpected non-function type for action %s:%s (%s)"
          (string_of_lid ed.mname) (string_of_lid act.action_name) (Print.term_to_string act_typ)) r in

    if Env.debug env <| Options.Other "LayeredEffectsTc" then
      BU.print1 "Expected action type: %s\n" (Print.term_to_string k);

    let g = Rel.teq env act_typ k in
    List.iter (Rel.force_trivial_guard env) [g_t; g_d; g_k; g];

    if Env.debug env <| Options.Other "LayeredEffectsTc" then
      BU.print1 "Expected action type after unification: %s\n" (Print.term_to_string k);
    
    let act_typ =
      let err_msg t = BU.format3
        "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
        (string_of_lid ed.mname) (string_of_lid act.action_name) (Print.term_to_string t) in
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

    if Env.debug env <| Options.Other "LayeredEffectsTc" then
      BU.print1 "Action type after injecting it into the monad: %s\n" (Print.term_to_string act_typ);
    
    let act =
      let us, act_defn = Gen.generalize_universes env act_defn in
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
                 (string_of_lid ed.mname) (string_of_lid act.action_name) (Print.univ_names_to_string us) (Print.univ_names_to_string act.action_univs)))
             r in

    act in

  let tschemes_of (us, t, ty) : tscheme * tscheme = (us, t), (us, ty) in

  let combinators = Layered_eff ({
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
)

let tc_non_layered_eff_decl env0 (ed:S.eff_decl) (_quals : list<qualifier>) (_attrs : list<S.attribute>) : S.eff_decl =
Errors.with_ctx (BU.format1 "While checking effect definition `%s`" (string_of_lid ed.mname)) (fun () ->
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
      let us, tmp_t = Gen.generalize_universes env0 tmp_t in
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
               (string_of_lid ed.mname) (BU.string_of_int (List.length ed_univs)) (BU.string_of_int (List.length us))))
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
    let g_us, t = Gen.generalize_universes env t in
    //check that n = List.length g_us and that if us is set, it is same as g_us
    begin
      if List.length g_us <> n then
        let error = BU.format4
          "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
          (string_of_lid ed.mname) comb (string_of_int n) (g_us |> List.length |> string_of_int) in
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
               (string_of_lid ed.mname) comb (BU.string_of_int (List.length us)) (BU.string_of_int (List.length g_us))))
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
       | [({binder_bv=a}); ({binder_bv=wp})] -> a, wp.sort
       | _ -> fail signature)
    | _ -> fail signature
  in

  let log_combinator s ts =
    if Env.debug env <| Options.Other "ED" then
      BU.print3 "Typechecked %s:%s = %s\n" (string_of_lid ed.mname) s (Print.tscheme_to_string ts) in

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
        mk (Tm_app (repr, [t |> as_arg; wp |> as_arg])) Range.dummyRange in
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
            [S.bv_to_name a |> S.as_arg; S.bv_to_name x_a |> S.as_arg] Range.dummyRange in
          mk_repr a wp in
        let k = U.arrow [S.mk_binder a; S.mk_binder x_a] (S.mk_Total res) in
        let k, _, _ = tc_tot_or_gtot_term env k in
        let env = Some (Env.set_range env (snd return_repr_ts).pos) in
        check_and_gen' "return_repr" 1 env return_repr_ts (Some k) in
    
      log_combinator "return_repr" return_repr;

      let bind_repr =
        let bind_repr_ts = ed |> U.get_bind_repr |> must in
        let a, wp_sort_a = fresh_a_and_wp () in
        let b, wp_sort_b = fresh_a_and_wp () in
        let wp_sort_a_b = U.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_sort_b) in
        let wp_f = S.gen_bv "wp_f" None wp_sort_a in
        let wp_g = S.gen_bv "wp_g" None wp_sort_a_b in
        let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
        let wp_g_x = mk_Tm_app (S.bv_to_name wp_g) [S.bv_to_name x_a |> S.as_arg] Range.dummyRange in
        let res =
          let wp = mk_Tm_app
            (Env.inst_tscheme bind_wp |> snd)
            (List.map as_arg [S.bv_to_name a; S.bv_to_name b; S.bv_to_name wp_f; S.bv_to_name wp_g])
            Range.dummyRange in
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
              (string_of_lid act.action_name) (Print.term_to_string act.action_defn)
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
            then Gen.generalize_universes env act_defn
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
)

let tc_eff_decl env ed quals attrs =
  (if ed |> U.is_layered then tc_layered_eff_decl else tc_non_layered_eff_decl) env ed quals attrs

let monad_signature env m s =
 let fail () = raise_error (Err.unexpected_signature_for_monad env m s) (range_of_lid m) in
 let s = SS.compress s in
 match s.n with
  | Tm_arrow(bs, c) ->
    let bs = SS.open_binders bs in
    begin match bs with
        | [({binder_bv=a});({binder_bv=wp})] -> a, wp.sort
        | _ -> fail ()
    end
  | _ -> fail ()

(*
 * Typecheck lift to/from a layered effect
 *
 *)
let tc_layered_lift env0 (sub:S.sub_eff) : S.sub_eff =
  if Env.debug env0 <| Options.Other "LayeredEffectsTc" then
    BU.print1 "Typechecking sub_effect: %s\n" (Print.sub_eff_to_string sub);

  let lift_ts = sub.lift |> must in
  let r = (lift_ts |> snd).pos in

  let us, lift, lift_ty = check_and_gen env0 "" "lift" 1 lift_ts in

  if Env.debug env0 <| Options.Other "LayeredEffectsTc" then
    BU.print2 "Typechecked lift: %s and lift_ty: %s\n"
      (Print.tscheme_to_string (us, lift)) (Print.tscheme_to_string ((us, lift_ty)));

  let us, lift_ty = SS.open_univ_vars us lift_ty in
  let env = Env.push_univ_vars env0 us in

  check_no_subtyping_for_layered_combinator env lift_ty None;

  let lift_t_shape_error s = BU.format4
    "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
    (Ident.string_of_lid sub.source) (Ident.string_of_lid sub.target)
    s (Print.term_to_string lift_ty) in

  (*
   * Construct the expected lift type k as:
   *   a:Type -> <some binders> -> f:source_repr a f_i_1 ... f_i_n : PURE (target_repr a i_1 ... i_m) wp
   *
   * Note the PURE effect and the wp
   *   It is a bit unusual, most of the times this is just Tot (target_repr a ...)
   *
   * Layered effects may have a logical payload, so when we define a lift from say PURE ~> M,
   *   we need to stash some preconditions (e.g. satisfiability of the PURE wp) in the lift combinator's definition somewhere
   *
   * When layered effects have logical payload, then these preconditiond can be stashed in there
   *
   * But when they don't, this PURE wp comes handy
   *)
  let k, g_k =
    let a, u_a = U.type_u () |> (fun (t, u) -> S.gen_bv "a" None t |> S.mk_binder, u) in

    //a:Type u

    //other binders
    let rest_bs, lift_eff =
      match (SS.compress lift_ty).n with
      | Tm_arrow (bs, c) when List.length bs >= 2 ->
        let (({binder_bv=a'})::bs) = SS.open_binders bs in
        bs |> List.splitAt (List.length bs - 1) |> fst
           |> SS.subst_binders [NT (a', bv_to_name a.binder_bv)],
        U.comp_effect_name c |> Env.norm_eff_name env
      | _ ->
        raise_error (Errors.Fatal_UnexpectedExpressionType,
          lift_t_shape_error "either not an arrow, or not enough binders") r in

    if (not ((lid_equals lift_eff PC.effect_PURE_lid) ||
             (lid_equals lift_eff PC.effect_GHOST_lid && Env.is_erasable_effect env sub.source)))
    then raise_error (Errors.Fatal_UnexpectedExpressionType,
                      lift_t_shape_error "the lift combinator has an unexpected effect: \
                        it must either be PURE or if the source effect is erasable then may be GHOST") r;

    let f_b, g_f_b =
      let f_sort, g = TcUtil.fresh_effect_repr_en
        (Env.push_binders env (a::rest_bs)) r sub.source u_a (a.binder_bv |> S.bv_to_name) in
      S.gen_bv "f" None f_sort |> S.mk_binder, g in

    let bs = a::rest_bs in

    //repr<?u> ?u_i ... ?u_n
    let repr, g_repr = TcUtil.fresh_effect_repr_en
      (Env.push_binders env bs)
      r sub.target u_a (a.binder_bv |> S.bv_to_name) in

    let pure_wp_uvar, guard_wp = pure_wp_uvar (Env.push_binders env bs) repr
      (BU.format2 "implicit for pure_wp in typechecking lift %s~>%s"
         (Ident.string_of_lid sub.source) (Ident.string_of_lid sub.target)) r in

    let c = S.mk_Comp ({
      comp_univs = [ Env.new_u_univ () ];
      effect_name = lift_eff;
      result_typ = repr;
      effect_args = [ pure_wp_uvar |> S.as_arg ];
      flags = [] }) in

    U.arrow (bs@[f_b]) c, Env.conj_guard (Env.conj_guard g_f_b g_repr) guard_wp in

  if Env.debug env <| Options.Other "LayeredEffectsTc"
  then BU.print1 "tc_layered_lift: before unification k: %s\n" (Print.term_to_string k);

  let g = Rel.teq env lift_ty k in
  Rel.force_trivial_guard env g_k; Rel.force_trivial_guard env g;

  if Env.debug env0 <| Options.Other "LayeredEffectsTc" then
    BU.print1 "After unification k: %s\n" (Print.term_to_string k);

  let k = k |> N.remove_uvar_solutions env in

  let check_non_informative_binders =
    Env.is_reifiable_effect env sub.target &&
    not (Env.fv_with_lid_has_attr env sub.target PC.allow_informative_binders_attr) in
  let _check_valid_binders =
    match (SS.compress k).n with
    | Tm_arrow (bs, c) ->
      let a::bs, c = SS.open_comp bs c in
      let res_t = U.comp_result c in
      let bs, f_b =
        List.splitAt (List.length bs - 1) bs
        |> (fun (l1, l2) -> l1, List.hd l2) in
      let env = Env.push_binders env [a] in
      validate_layered_effect_binders env bs [f_b.binder_bv.sort; res_t] check_non_informative_binders r in

  let sub = { sub with
    lift = Some (us, lift);
    lift_wp = Some (us, k |> SS.close_univ_vars us) } in

  if Env.debug env0 <| Options.Other "LayeredEffectsTc" then
    BU.print1 "Final sub_effect: %s\n" (Print.sub_eff_to_string sub);

  sub

let check_lift_for_erasable_effects env (m1:lident) (m2:lident) r : unit =
  let err reason = raise_error (Errors.Fatal_UnexpectedEffect,
                                BU.format3 "Error defining a lift/subcomp %s ~> %s: %s"
                                  (string_of_lid m1) (string_of_lid m2) reason) r in

  let m1 = Env.norm_eff_name env m1 in
  if lid_equals m1 PC.effect_GHOST_lid
  then err "user-defined lifts from GHOST effect are not allowed"
  else
    let m1_erasable = Env.is_erasable_effect env m1 in
    let m2_erasable = Env.is_erasable_effect env m2 in
    if m2_erasable     &&
       not m1_erasable &&
       not (lid_equals m1 PC.effect_PURE_lid)
    then err "cannot lift a non-erasable effect to an erasable effect unless the non-erasable effect is PURE"

let tc_lift env sub r =
  let check_and_gen env t k =
    // BU.print1 "\x1b[01;36mcheck and gen \x1b[00m%s\n" (Print.term_to_string t);
    Gen.generalize_universes env (tc_check_trivial_guard env t k) in

  check_lift_for_erasable_effects env sub.source sub.target r;

  let ed_src = Env.get_effect_decl env sub.source in
  let ed_tgt = Env.get_effect_decl env sub.target in

  if ed_src |> U.is_layered || ed_tgt |> U.is_layered
  then tc_layered_lift (Env.set_range env r) sub
  else
    let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
    let b, wp_b_tgt = monad_signature env sub.target (Env.lookup_effect_lid env sub.target) in
    let wp_a_tgt    = SS.subst [NT(b, S.bv_to_name a)] wp_b_tgt in
    let expected_k  = U.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
    let repr_type eff_name a wp =
      if not (is_reifiable_effect env eff_name)
      then raise_error (Errors.Fatal_EffectCannotBeReified, (BU.format1 "Effect %s cannot be reified" (string_of_lid eff_name))) (Env.get_range env);
      match Env.effect_decl_opt env eff_name with
      | None -> failwith "internal error: reifiable effect has no decl?"
      | Some (ed, qualifiers) ->
        let repr = Env.inst_effect_fun_with [U_unknown] env ed (ed |> U.get_eff_repr |> must) in
        mk (Tm_app(repr, [as_arg a; as_arg wp])) (Env.get_range env)
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
        if List.length uvs = 0 then Some (Gen.generalize_universes env lift_elab), Gen.generalize_universes env lift_wp
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
        let lift_wp_a = mk (Tm_app(lift_wp, [as_arg a_typ; as_arg wp_a_typ])) (Env.get_range env) in
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
      | ({binder_bv=x})::_ -> S.bv_to_name x
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
  let uvs, t = Gen.generalize_universes env0 (mk (Tm_arrow(tps, c)) r) in
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


let check_polymonadic_bind_for_erasable_effects env (m:lident) (n:lident) (p:lident) r =
  let err reason = raise_error (Errors.Fatal_UnexpectedEffect,
                                BU.format4 "Error definition polymonadic bind (%s, %s) |> %s: %s"
                                  (string_of_lid m) (string_of_lid n) (string_of_lid p) reason) r in

  let m = Env.norm_eff_name env m in
  let n = Env.norm_eff_name env n in

  if lid_equals m PC.effect_GHOST_lid ||
     lid_equals n PC.effect_GHOST_lid
  then err "GHOST computations are not allowed to be composed using user-defined polymonadic binds"
  else
    let m_erasable = Env.is_erasable_effect env m in
    let n_erasable = Env.is_erasable_effect env n in
    let p_erasable = Env.is_erasable_effect env p in


    if p_erasable
    then if not m_erasable && not (lid_equals m PC.effect_PURE_lid)
         then err (BU.format1 "target effect is erasable but %s is neither erasable nor PURE" (string_of_lid m))
         else if not n_erasable && not (lid_equals n PC.effect_PURE_lid)
         then err (BU.format1 "target effect is erasable but %s is neither erasable nor PURE" (string_of_lid n))

let tc_polymonadic_bind env (m:lident) (n:lident) (p:lident) (ts:S.tscheme) : (S.tscheme * S.tscheme) =
  let eff_name = BU.format3 "(%s, %s) |> %s)"
    (m |> ident_of_lid |> string_of_id)
    (n |> ident_of_lid |> string_of_id)
    (p |> ident_of_lid |> string_of_id) in
  let r = (snd ts).pos in

  check_polymonadic_bind_for_erasable_effects env m n p r;

  //p should be non-reifiable, reification of polymonadic binds is not yet implemented
  (*
   * AR: TODO: FIXME: we are allowing reification of effects that use polymoandic binds,
   *                  but this should only be used for proofs, extracting such code would
   *                  not work
   *)
  // if Env.is_user_reifiable_effect env p
  // then raise_error (Errors.Fatal_EffectCannotBeReified,
  //        BU.format2 "Error typechecking the polymonadic bind %s, the final effect %s is reifiable \
  //          and reification of polymondic binds is not yet implemented"
  //          eff_name (Ident.string_of_lid p)) r;

  //typecheck the term making sure that it is universe polymorphic in 2 universes
  let (us, t, ty) = check_and_gen env eff_name "polymonadic_bind" 2 ts in

  //make sure that the bind is of the right shape

  let us, ty = SS.open_univ_vars us ty in
  let env = Env.push_univ_vars env us in

  check_no_subtyping_for_layered_combinator env ty None;

  //construct the expected type k to be:
  //a:Type -> b:Type -> <some binders> -> m_repr a is -> (x:a -> n_repr b js) -> p_repr b ks

  let a, u_a = U.type_u () |> (fun (t, u) -> S.gen_bv "a" None t |> S.mk_binder, u) in
  let b, u_b = U.type_u () |> (fun (t, u) -> S.gen_bv "b" None t |> S.mk_binder, u) in

  let rest_bs =
    match (SS.compress ty).n with
    | Tm_arrow (bs, _) when List.length bs >= 4 ->
      let (({binder_bv=a'})::({binder_bv=b'})::bs) = SS.open_binders bs in
      bs |> List.splitAt (List.length bs - 2) |> fst
         |> SS.subst_binders [NT (a', a.binder_bv |> S.bv_to_name); NT (b', b.binder_bv |> S.bv_to_name)]
    | _ ->
      raise_error (Errors.Fatal_UnexpectedEffect,
        BU.format3 "Type of %s is not an arrow with >= 4 binders (%s::%s)" eff_name
          (Print.tag_of_term ty) (Print.term_to_string ty)) r in

  let bs = a::b::rest_bs in

  let f, guard_f =
    let repr, g = TcUtil.fresh_effect_repr_en (Env.push_binders env bs) r m u_a (a.binder_bv |> S.bv_to_name) in
    S.gen_bv "f" None repr |> S.mk_binder, g in

  let g, guard_g =
    let x_a = S.gen_bv "x" None (a.binder_bv |> S.bv_to_name) |> S.mk_binder in
    let repr, g = TcUtil.fresh_effect_repr_en (Env.push_binders env (bs@[x_a])) r n u_b (b.binder_bv |> S.bv_to_name) in
    S.gen_bv "g" None (U.arrow [x_a] (S.mk_Total' repr (Some (new_u_univ ())))) |> S.mk_binder, g in

  let repr, guard_repr = TcUtil.fresh_effect_repr_en (Env.push_binders env bs) r p u_b (b.binder_bv |> S.bv_to_name) in

  let pure_wp_uvar, g_pure_wp_uvar = pure_wp_uvar (Env.push_binders env bs) repr
    (BU.format1 "implicit for pure_wp in checking %s" eff_name)
    r in

  let k = U.arrow (bs@[f; g]) (S.mk_Comp ({
    comp_univs = [ Env.new_u_univ () ];
    effect_name = PC.effect_PURE_lid;
    result_typ = repr;
    effect_args = [ pure_wp_uvar |> S.as_arg ];
    flags = [] })) in
  
  let guard_eq = Rel.teq env ty k in
  List.iter (Rel.force_trivial_guard env) [guard_f; guard_g; guard_repr; g_pure_wp_uvar; guard_eq];

  if Env.debug env <| Options.Extreme
  then BU.print3 "Polymonadic bind %s after typechecking (%s::%s)\n"
         eff_name (Print.tscheme_to_string (us, t))
                  (Print.tscheme_to_string (us, k));

  let k = k |> N.remove_uvar_solutions env in

  let check_non_informative_binders =
    Env.is_reifiable_effect env p &&
    not (Env.fv_with_lid_has_attr env p PC.allow_informative_binders_attr) in
  let _check_valid_binders =
    match (SS.compress k).n with
    | Tm_arrow (bs, c) ->
      let a::b::bs, c = SS.open_comp bs c in
      let res_t = U.comp_result c in
      let bs, f_b, g_b =
        List.splitAt (List.length bs - 2) bs
        |> (fun (l1, l2) -> l1,
                        l2 |> List.hd, l2 |> List.tl |> List.hd) in
      //AR: CAUTION: a little lax about opening g_b with x:a binder, see comment in tc_layered_eff bind checking
      let g_sort =
        match (SS.compress g_b.binder_bv.sort).n with
        | Tm_arrow (_, c) -> U.comp_result c in
      let env = Env.push_binders env [a; b] in
      validate_layered_effect_binders env bs [f_b.binder_bv.sort; g_sort; res_t] check_non_informative_binders r in


  log_issue r (Errors.Warning_BleedingEdge_Feature,
    BU.format1 "Polymonadic binds (%s in this case) is an experimental feature;\
      it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
      eff_name);

  (us, t), (us, k |> SS.close_univ_vars us)


let tc_polymonadic_subcomp env0 (m:lident) (n:lident) (ts:S.tscheme) : (S.tscheme * S.tscheme) =
  let r = (snd ts).pos in

  check_lift_for_erasable_effects env0 m n r;

  let combinator_name =
    (m |> ident_of_lid |> string_of_id) ^ " <: " ^
    (n |> ident_of_lid |> string_of_id) in

  let us, t, ty = check_and_gen env0 combinator_name "polymonadic_subcomp" 1 ts in

  //make sure that the combinator has the right shape

  let us, ty = SS.open_univ_vars us ty in
  let env = Env.push_univ_vars env0 us in

  check_no_subtyping_for_layered_combinator env ty None;

  //construct the expected type k to be:
  //a:Type -> <some binders> -> m_repr a is -> PURE (n_repr a js) wp

  let a, u = U.type_u () |> (fun (t, u) -> S.gen_bv "a" None t |> S.mk_binder, u) in
  let rest_bs =
    match (SS.compress ty).n with
    | Tm_arrow (bs, _) when List.length bs >= 2 ->
      let (({binder_bv=a'})::bs) = SS.open_binders bs in
      bs |> List.splitAt (List.length bs - 1) |> fst
         |> SS.subst_binders [NT (a', bv_to_name a.binder_bv)]
    | _ -> 
      raise_error (Errors.Fatal_UnexpectedEffect,
        BU.format3 "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
          combinator_name
          (Print.tag_of_term t) (Print.term_to_string t)) r in
    
  let bs = a::rest_bs in
  let f, guard_f =
    let repr, g = TcUtil.fresh_effect_repr_en (Env.push_binders env bs) r m u
      (a.binder_bv |> S.bv_to_name) in
    S.gen_bv "f" None repr |> S.mk_binder, g in
    
  let ret_t, guard_ret_t = TcUtil.fresh_effect_repr_en (Env.push_binders env bs)
    r n u (a.binder_bv |> S.bv_to_name) in

  let pure_wp_uvar, guard_wp = pure_wp_uvar (Env.push_binders env bs) ret_t 
    (BU.format1 "implicit for pure_wp in checking polymonadic subcomp %s" combinator_name)
    r in
  let c = S.mk_Comp ({
    comp_univs = [ Env.new_u_univ () ];
    effect_name = PC.effect_PURE_lid;
    result_typ = ret_t;
    effect_args = [ pure_wp_uvar |> S.as_arg ];
    flags = [] }) in

  let k = U.arrow (bs@[f]) c in

  if Env.debug env <| Options.Other "LayeredEffectsTc" then
    BU.print2 "Expected type of polymonadic subcomp %s before unification: %s\n"
      combinator_name
      (Print.term_to_string k);

  let guard_eq = Rel.teq env ty k in
  List.iter (Rel.force_trivial_guard env) [guard_f; guard_ret_t; guard_wp; guard_eq];

  let k = k
    |> N.remove_uvar_solutions env
    |> N.normalize [Env.Beta; Env.Eager_unfolding] env in

  if Env.debug env <| Options.Other "LayeredEffectsTc" then
    BU.print2 "Polymonadic subcomp %s type after unification : %s\n"
      combinator_name (Print.tscheme_to_string (us, k));

  let check_non_informative_binders =
    Env.is_reifiable_effect env n &&
    not (Env.fv_with_lid_has_attr env n PC.allow_informative_binders_attr) in
  let _check_valid_binders =
    match (SS.compress k).n with
    | Tm_arrow (bs, c) ->
      let a::bs,c = SS.open_comp bs c in
      let res_t = U.comp_result c in
      let bs, f_b =
        List.splitAt (List.length bs - 1) bs
        |> (fun (l1, l2) -> l1, List.hd l2) in
      let env = Env.push_binders env [a] in
      validate_layered_effect_binders env bs [f_b.binder_bv.sort; res_t] check_non_informative_binders r in


  log_issue r (Errors.Warning_BleedingEdge_Feature,
    BU.format1 "Polymonadic subcomp (%s in this case) is an experimental feature;\
      it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
      combinator_name);

  (us, t), (us, k |> SS.close_univ_vars us)
