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
module FStarC.TypeChecker.TcEffect
open FStar.Pervasives
open FStarC.Compiler.Effect
open FStarC.Compiler.List
open FStar open FStarC
open FStarC.Compiler
open FStarC.Syntax
open FStarC.TypeChecker

open FStarC.Compiler.Util
open FStarC.Ident
open FStarC.Errors
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.TcTerm

module PC = FStarC.Parser.Const
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module Env = FStarC.TypeChecker.Env
module N = FStarC.TypeChecker.Normalize
module TcUtil = FStarC.TypeChecker.Util
module Gen = FStarC.TypeChecker.Generalize
module TEQ = FStarC.TypeChecker.TermEqAndSimplify

module BU = FStarC.Compiler.Util
open FStarC.Class.Show
open FStarC.Class.Tagged

let dbg                  = Debug.get_toggle "ED"
let dbg_LayeredEffectsTc = Debug.get_toggle "LayeredEffectsTc"

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
let check_and_gen env (eff_name:string) (comb:string) (n:int) (us, t) : (univ_names & term & typ) =
  Errors.with_ctx ("While checking combinator " ^ comb ^ " = " ^ show (us, t)) (fun () ->
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
      raise_error t Errors.Fatal_MismatchUniversePolymorphic error;
    match us with
    | [] -> ()
    | _ ->
     if List.length us = List.length g_us &&
      List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) us g_us
     then ()
     else raise_error t Errors.Fatal_UnexpectedNumberOfUniverse
            (BU.format4 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
               eff_name comb (show us) (show g_us))
  in
  g_us, t, ty
  )

(*
 * A small gadget to get a uvar for pure wp with given result type
 *)
let pure_wp_uvar env (t:typ) (reason:string) (r:Range.range) : term & guard_t =
  let pure_wp_t =
    let pure_wp_ts = Env.lookup_definition [Env.NoDelta] env PC.pure_wp_lid |> must in
    let _, pure_wp_t = Env.inst_tscheme pure_wp_ts in
    S.mk_Tm_app
      pure_wp_t
      [t |> S.as_arg]
      r in

  let pure_wp_uvar, _, guard_wp = Env.new_implicit_var_aux reason r env pure_wp_t Strict None false in
  pure_wp_uvar, guard_wp

let (let?) (#a #b:Type) (f:option a) (g:a -> option b) : option b =
  match f with
  | None -> None
  | Some x -> g x

let mteq (env:env) (t1 t2:typ) : bool =
  try
    Rel.teq_nosmt_force env t1 t2
   with
   | _ -> false

//
// A gadget used to check for effect combinator kind (substitutive or ad-hoc)
//
// bs1 and bs2 are opened binders from the signature and the effect combinator
//
let eq_binders env (bs1 bs2:binders) : option (list S.indexed_effect_binder_kind) =
  if List.fold_left2 (fun (b, ss) b1 b2 ->
       b &&
       mteq env (SS.subst ss b1.binder_bv.sort) b2.binder_bv.sort,
       ss@[NT (b1.binder_bv, b2.binder_bv |> S.bv_to_name)]) (true, []) bs1 bs2

     |> fst
  then bs1 |> List.map (fun _ -> Substitutive_binder) |> Some
  else None

let log_ad_hoc_combinator_warning (comb_name:string) (r:Range.range) =
  log_issue r Errors.Warning_Adhoc_IndexedEffect_Combinator [
    Errors.text (BU.format1 "Combinator %s is not a substitutive indexed effect combinator, \
                   it is better to make it one if possible for better performance and ease of use" comb_name)
  ]

//
// Check bind combinator kind for an indexed effect or polymonadic bind
//
// k is the bind type (in the general indexed effects bind shape)
//
// num_effect_params must be 0 for polymonadic binds
//
// returns None if bind is not Substitutive
//   else Some l, where l is the list of binder kinds
//
let bind_combinator_kind (env:env)
  (m_eff_name n_eff_name p_eff_name:lident)
  (m_sig_ts n_sig_ts p_sig_ts:tscheme)
  (m_repr_ts n_repr_ts p_repr_ts:option tscheme)
  (bind_us:univ_names)
  (k:typ)
  (num_effect_params:int)
  (has_range_binders:bool)
  : option (list indexed_effect_binder_kind) =

  let debug s =
    if Debug.medium () || !dbg_LayeredEffectsTc
    then BU.print1 "%s\n" s in

  debug (BU.format1
           "Checking bind combinator kind with %s effect parameters"
           (string_of_int num_effect_params));

  // we know k = a:Type u_a -> b:Type u_b -> rest_bs -> optional_range_bs -> f -> g -> Pure repr wp

  let [u_a; u_b] = bind_us in

  let (a_b::b_b::rest_bs) = k |> U.arrow_formals |> fst in

  // we will check that every binder in k has the expected type,
  //   where the expected types will come from the signatures of the effects

  // check that rest_bs has expected effect parameters
  // to check expected, we use the signature from m,
  //   for polymonadic binds num effect parameters is 0,
  //   so this code will return from the then branch
  let? eff_params_bs, eff_params_bs_kinds, rest_bs =
    if num_effect_params = 0
    then ([], [], rest_bs) |> Some
    else // take the num effect parameters from m's signature and
         //   check that those binders are equal to those in k
         let _, sig = Env.inst_tscheme_with m_sig_ts [U_name u_a] in
         let sig_bs = sig |> U.arrow_formals
           |> fst
           |> List.tl in
         let? sig_eff_params_bs =
           if List.length sig_bs < num_effect_params
           then None
           else List.splitAt num_effect_params sig_bs |> fst |> Some in
         let? eff_params_bs, rest_bs =
           if List.length rest_bs < num_effect_params
           then None
           else List.splitAt num_effect_params rest_bs |> Some in
         let? eff_params_bs_kinds = eq_binders env sig_eff_params_bs eff_params_bs in
         (eff_params_bs, eff_params_bs_kinds, rest_bs) |> Some in

  // check that prefix of rest_bs matches the binders in f's repr
  let? f_bs, f_bs_kinds, rest_bs =
    // binders in f's signature,
    //   after substituting eff_params_bs (we need to check for binder equality)
    let f_sig_bs =
      let _, sig = Env.inst_tscheme_with m_sig_ts [U_name u_a] in
      sig |> U.arrow_formals
          |> fst
          |> (fun (a::bs) ->
             let sig_bs, bs = List.splitAt num_effect_params bs in
             let ss = List.fold_left2 (fun ss sig_b b ->
               ss@[NT (sig_b.binder_bv, b.binder_bv |> S.bv_to_name)]
             ) [NT (a.binder_bv, a_b.binder_bv |> S.bv_to_name)] sig_bs eff_params_bs in
             bs |> SS.subst_binders ss) in

    let? f_bs, rest_bs =
      if List.length rest_bs < List.length f_sig_bs
      then None
      else List.splitAt (List.length f_sig_bs) rest_bs |> Some in

    let? f_bs_kinds = eq_binders env f_sig_bs f_bs in

    (f_bs, f_bs_kinds, rest_bs) |> Some in

  // same thing for g

  let? g_bs, g_bs_kinds, rest_bs =
    let g_sig_bs =
      let _, sig = Env.inst_tscheme_with n_sig_ts [U_name u_b] in
      sig |> U.arrow_formals
          |> fst
          |> (fun (b::bs) ->
             let sig_bs, bs = List.splitAt num_effect_params bs in
             let ss = List.fold_left2 (fun ss sig_b b ->
               ss@[NT (sig_b.binder_bv, b.binder_bv |> S.bv_to_name)]
             ) [NT (b.binder_bv, b_b.binder_bv |> S.bv_to_name)] sig_bs eff_params_bs in
             bs |> SS.subst_binders ss) in

    let? g_bs, rest_bs =
      if List.length rest_bs < List.length g_sig_bs
      then None
      else List.splitAt (List.length g_sig_bs) rest_bs |> Some in

    //
    // g's binders may be either abstracted over x:a or un-abstracted,
    //   so we can't simply do eq_binders, we need to check one binder at a time
    //
    let? g_bs_kinds =
      let g_bs_kinds, _ = List.fold_left2 (fun (l, ss) g_sig_b g_b ->  // l is the (bv, kind) list for the binders seen so far
        let g_sig_b_sort = SS.subst ss g_sig_b.binder_bv.sort in
        let g_sig_b_arrow_t =  // expected sort of g_b if the binder were abstracted
          let x_bv = S.gen_bv "x" None (a_b.binder_bv |> S.bv_to_name) in
          let ss = List.map (fun (bv, k) ->
            if k = Substitutive_binder
            then [NT (bv, mk_Tm_app (S.bv_to_name bv) [x_bv |> S.bv_to_name |> S.as_arg] Range.dummyRange)]
            else []) l |> List.flatten in
          let g_sig_b_sort = SS.subst ss g_sig_b_sort in
          U.arrow [S.mk_binder x_bv]
                  (mk_Total g_sig_b_sort) in
        let g_b_kind =
          if TEQ.eq_tm env g_sig_b_arrow_t g_b.binder_bv.sort = TEQ.Equal
          then Substitutive_binder
          else if TEQ.eq_tm env g_sig_b_sort g_b.binder_bv.sort = TEQ.Equal
          then BindCont_no_abstraction_binder
          else Ad_hoc_binder in
        let ss = ss@[NT (g_sig_b.binder_bv, g_b.binder_bv |> S.bv_to_name)] in
        l@[g_b.binder_bv, g_b_kind], ss) ([], []) g_sig_bs g_bs in

      let g_bs_kinds = List.map snd g_bs_kinds in
      if List.contains Ad_hoc_binder g_bs_kinds
      then None
      else g_bs_kinds |> Some in

    (g_bs, g_bs_kinds, rest_bs) |> Some in

  // peel off range binders if any

  let (range_bs, rest_bs) : (list binder & list binder) =
    if has_range_binders
    then List.splitAt 2 rest_bs
    else [], rest_bs in

  let? rest_bs, f_b, g_b =
    if List.length rest_bs >= 2
    then let rest_bs, [f_b; g_b] = List.splitAt (List.length rest_bs - 2) rest_bs in
         (rest_bs, f_b, g_b) |> Some
    else None in

  // check that the type of the f repr is ok
  let? _f_b_ok_ =
    let repr_app_bs = eff_params_bs@f_bs in
    let expected_f_b_sort =
      match m_repr_ts with
      | Some repr_ts ->  // an indexed effect, so repr applied to a and bs
        let _, t = Env.inst_tscheme_with repr_ts [U_name u_a] in
        S.mk_Tm_app t
          ((a_b.binder_bv |> S.bv_to_name |> S.as_arg)::
           (List.map (fun {binder_bv=b} -> b |> S.bv_to_name |> S.as_arg) repr_app_bs))
          Range.dummyRange
      | None ->  // a primitive effect, so unit -> M a bs
        U.arrow [S.null_binder S.t_unit]
                (mk_Comp ({
                   comp_univs = [U_name u_a];
                   effect_name = m_eff_name;
                   result_typ = a_b.binder_bv |> S.bv_to_name;
                   effect_args = repr_app_bs |> List.map (fun b -> b.binder_bv |> S.bv_to_name |> S.as_arg);
                   flags = []})) in
    if TEQ.eq_tm env f_b.binder_bv.sort expected_f_b_sort = TEQ.Equal
    then Some ()
    else None in

  // check that the type of g repr is ok
  let? _g_b_ok =
    let expected_g_b_sort =
      let x_bv = S.gen_bv "x" None (a_b.binder_bv |> S.bv_to_name) in
      let eff_params_args = List.map (fun {binder_bv=b} -> b |> S.bv_to_name |> S.as_arg) eff_params_bs in
      let g_bs_args =
        List.map2 (fun {binder_bv=b} kind ->
          // we know here that kind is either Substitutive or BindCont_no_abs
          if kind = Substitutive_binder
          then S.mk_Tm_app (b |> S.bv_to_name) [x_bv |> S.bv_to_name |> S.as_arg] Range.dummyRange
          else b |> S.bv_to_name) g_bs g_bs_kinds
        |> List.map S.as_arg in
      let repr_args = eff_params_args@g_bs_args in

      match n_repr_ts with
      | Some repr_ts ->
        let _, repr_hd = Env.inst_tscheme_with repr_ts [U_name u_b] in
        let repr_app = mk_Tm_app repr_hd
          ((b_b.binder_bv |> S.bv_to_name |> S.as_arg)::repr_args)
          Range.dummyRange in
        U.arrow [x_bv |> S.mk_binder] (mk_Total repr_app)
      | None ->
        let thunk_t = U.arrow [S.null_binder S.t_unit]
          (mk_Comp ({
             comp_univs = [U_name u_b];
             effect_name = n_eff_name;
             result_typ = b_b.binder_bv |> S.bv_to_name;
             effect_args = repr_args;
             flags = []})) in
        U.arrow [x_bv |> S.mk_binder] (mk_Total thunk_t) in
    if TEQ.eq_tm env g_b.binder_bv.sort expected_g_b_sort = TEQ.Equal
    then Some ()
    else None in

  let range_kinds = List.map (fun _ -> Range_binder) range_bs in

  // remaining binders in rest_bs are all ad-hoc
  let rest_kinds = List.map (fun _ -> Ad_hoc_binder) rest_bs in

  Some ([Type_binder; Type_binder] @
        eff_params_bs_kinds        @
        f_bs_kinds                 @
        g_bs_kinds                 @
        range_kinds                @
        rest_kinds                 @
        [Repr_binder; Repr_binder])

//
// Validate that the indexed effect bind has the expected shape,
//   and return its canonical type and combinator kind
//
let validate_indexed_effect_bind_shape (env:env)
  (m_eff_name n_eff_name p_eff_name:lident)
  (m_sig_ts n_sig_ts p_sig_ts:tscheme)
  (m_repr_ts n_repr_ts p_repr_ts:option tscheme)
  (bind_us:univ_names)
  (bind_t:typ)
  (r:Range.range)
  (num_effect_params:int)
  (has_range_binders:bool)
  : typ & indexed_effect_combinator_kind =

  let bind_name = BU.format3 "(%s , %s) |> %s"
    (string_of_lid m_eff_name)
    (string_of_lid n_eff_name)
    (string_of_lid p_eff_name) in

  let [u_a; u_b] = bind_us in

  //
  // First check that bind has the general shape:
  //   a:Type u_a -> b:Type u_b -> some_bs -> optional_range_bs -> f -> g -> PURE repr wp
  //
  // We do so by creating expected type k = the arrow type above,
  //   and unifying it with bind_t
  //

  // a:Type and b:Type binders
  let a_b = (U_name u_a) |> U.type_with_u |> S.gen_bv "a" None |> S.mk_binder in
  let b_b = (U_name u_b) |> U.type_with_u |> S.gen_bv "b" None |> S.mk_binder in

  // rest_bs are opened and have their a and b substituted with a_b and b_b
  let rest_bs =
    match (SS.compress bind_t).n with
    | Tm_arrow {bs} when List.length bs >= 4 ->
      // peel off a and b from bs
      let ({binder_bv=a})::({binder_bv=b})::bs = SS.open_binders bs in
      // peel off f and g from the end of bs
      bs |> List.splitAt (List.length bs - 2) |> fst
         |> SS.subst_binders [NT (a, a_b.binder_bv |> S.bv_to_name);
                             NT (b, b_b.binder_bv |> S.bv_to_name)]
    | _ ->
     raise_error r Errors.Fatal_UnexpectedEffect
                  (BU.format2 "Type of %s is not an arrow with >= 4 binders (%s)"
                    bind_name
                    (show bind_t)) in
      

  // peel off range binders from the end, if any
  let rest_bs, range_bs =
    if has_range_binders
    then if List.length rest_bs >= 2
         then List.splitAt (List.length rest_bs - 2) rest_bs
         else raise_error r Errors.Fatal_UnexpectedEffect
                           (BU.format2 "Type of %s is not an arrow with >= 6 binders (%s)"
                             bind_name
                             (show bind_t))
    else rest_bs, [] in

  // f binder with sort m_repr ?us
  let f, guard_f =
    let repr, g = TcUtil.fresh_effect_repr
      (Env.push_binders env (a_b::b_b::rest_bs))
      r
      m_eff_name
      m_sig_ts
      m_repr_ts
      (U_name u_a)
      (a_b.binder_bv |> S.bv_to_name) in
    repr |> S.gen_bv "f" None |> S.mk_binder, g in

  // g binder with sort (x:a -> n_repr ?us)
  let g, guard_g =
    let x_a = a_b.binder_bv |> S.bv_to_name |> S.gen_bv "x" None |> S.mk_binder in
    let repr, g = TcUtil.fresh_effect_repr
      (Env.push_binders env (a_b::b_b::rest_bs@[x_a]))
      r
      n_eff_name
      n_sig_ts
      n_repr_ts
      (U_name u_b)
      (b_b.binder_bv |> S.bv_to_name) in
    S.gen_bv "g" None (U.arrow [x_a] (S.mk_Total repr)) |> S.mk_binder,
    g in

  // return repr type p_repr ?us
  let return_repr, guard_return_repr = TcUtil.fresh_effect_repr
    (Env.push_binders env (a_b::b_b::rest_bs))
    r
    p_eff_name
    p_sig_ts
    p_repr_ts
    (U_name u_b)
    (b_b.binder_bv |> S.bv_to_name) in

  let pure_wp_uvar, g_pure_wp_uvar = pure_wp_uvar
    (Env.push_binders env (a_b::b_b::rest_bs))
    return_repr
    (BU.format1 "implicit for pure_wp in checking bind %s" bind_name)
    r in

  let k = U.arrow (a_b::b_b::(rest_bs@range_bs@[f; g])) (S.mk_Comp ({
    comp_univs = [Env.new_u_univ ()];
    effect_name = PC.effect_PURE_lid;
    result_typ = return_repr;
    effect_args = [pure_wp_uvar |> S.as_arg];
    flags = [] })) in

  let guard_eq =
    match Rel.teq_nosmt env k bind_t with
    | None ->
      raise_error r Errors.Fatal_UnexpectedEffect
                   (BU.format2 "Unexpected type of %s (%s)\n"
                     bind_name
                     (show bind_t))
    | Some g -> g in

  Rel.force_trivial_guard env (Env.conj_guards [
    guard_f;
    guard_g;
    guard_return_repr;
    g_pure_wp_uvar;
    guard_eq]);

  let k = k |> N.remove_uvar_solutions env |> SS.compress in

  let lopt = bind_combinator_kind env m_eff_name n_eff_name p_eff_name
    m_sig_ts n_sig_ts p_sig_ts
    m_repr_ts n_repr_ts p_repr_ts
    bind_us
    k
    num_effect_params
    has_range_binders in

  let kind = 
    match lopt with
    | None ->
      log_ad_hoc_combinator_warning bind_name r;
      Ad_hoc_combinator
    | Some l -> Substitutive_combinator l in

  if Debug.medium () || !dbg_LayeredEffectsTc
  then BU.print2 "Bind %s has %s kind\n" bind_name (show kind);

  k, kind

//
// Check subcomp combinator kind
//
// Used for both indexed effects subcomp and polymonadic subcomp
//
let subcomp_combinator_kind (env:env)
  (m_eff_name n_eff_name:lident)
  (m_sig_ts n_sig_ts:tscheme)
  (m_repr_ts n_repr_ts:option tscheme)
  (u:univ_name)
  (k:typ)
  (num_effect_params:int)

  : option S.indexed_effect_combinator_kind =

  // the idea is same as that of bind
  //   we will check that each binder in k has expected type,
  //   where the expected types will come from signatures and reprs of m and n

  let a_b::rest_bs, k_c = k |> U.arrow_formals_comp in

  let? eff_params_bs, eff_params_bs_kinds, rest_bs =
    if num_effect_params = 0
    then ([], [], rest_bs) |> Some
    else let _, sig = Env.inst_tscheme_with m_sig_ts [U_name u] in
         let _::sig_bs, _ = sig |> U.arrow_formals in
         let sig_effect_params_bs = List.splitAt num_effect_params sig_bs |> fst in
         let eff_params_bs, rest_bs = List.splitAt num_effect_params rest_bs in
         let? eff_params_bs_kinds = eq_binders env sig_effect_params_bs eff_params_bs in
         (eff_params_bs, eff_params_bs_kinds, rest_bs) |> Some in

  let? f_bs, f_bs_kinds, rest_bs =
    let f_sig_bs =
      let _, sig = Env.inst_tscheme_with m_sig_ts [U_name u] in
      sig |> U.arrow_formals
          |> fst
          |> (fun (a::bs) ->
             let sig_bs, bs = List.splitAt num_effect_params bs in
             let ss = List.fold_left2 (fun ss sig_b b ->
               ss@[NT (sig_b.binder_bv, b.binder_bv |> S.bv_to_name)]
             ) [NT (a.binder_bv, a_b.binder_bv |> S.bv_to_name)] sig_bs eff_params_bs in
             bs |> SS.subst_binders ss) in

    let? f_bs, rest_bs =
      if List.length rest_bs < List.length f_sig_bs
      then None
      else List.splitAt (List.length f_sig_bs) rest_bs |> Some in

    let? f_bs_kinds = eq_binders env f_sig_bs f_bs in

    (f_bs, f_bs_kinds, rest_bs) |> Some in

  // peel off the f:repr a is binder
  let? rest_bs, f_b =
    if List.length rest_bs >= 1
    then let rest_bs, [f_b] = List.splitAt (List.length rest_bs - 1) rest_bs in
         (rest_bs, f_b) |> Some
    else None in

  // check that f repr binder has the expected type
  let? _f_b_ok_ =
    let expected_f_b_sort =
      match m_repr_ts with
      | Some repr_ts ->
        let _, t = Env.inst_tscheme_with repr_ts [U_name u] in
        S.mk_Tm_app t
          ((a_b.binder_bv |> S.bv_to_name |> S.as_arg)::
           (List.map (fun {binder_bv=b} -> b |> S.bv_to_name |> S.as_arg) (eff_params_bs@f_bs)))
          Range.dummyRange
      | None ->
        U.arrow [S.null_binder S.t_unit]
          (mk_Comp ({
             comp_univs = [U_name u];
             effect_name = m_eff_name;
             result_typ = a_b.binder_bv |> S.bv_to_name;
             effect_args = (eff_params_bs@f_bs) |> List.map (fun b -> b.binder_bv |> S.bv_to_name |> S.as_arg);
             flags = []})) in
    if TEQ.eq_tm env f_b.binder_bv.sort expected_f_b_sort = TEQ.Equal
    then Some ()
    else None in

  let check_ret_t (f_or_g_bs:binders) : option unit =
    let expected_t =
      match n_repr_ts with
      | Some repr_ts ->
        let _, t = Env.inst_tscheme_with repr_ts [U_name u] in
        S.mk_Tm_app t
          ((a_b.binder_bv |> S.bv_to_name |> S.as_arg)::
           (List.map (fun {binder_bv=b} -> b |> S.bv_to_name |> S.as_arg) (eff_params_bs@f_or_g_bs)))
          Range.dummyRange
      | None ->
        U.arrow [S.null_binder S.t_unit]
          (mk_Comp ({
             comp_univs = [U_name u];
             effect_name = n_eff_name;
             result_typ = a_b.binder_bv |> S.bv_to_name;
             effect_args = (eff_params_bs@f_or_g_bs) |> List.map (fun b -> b.binder_bv |> S.bv_to_name |> S.as_arg);
             flags = []})) in
    if TEQ.eq_tm env (U.comp_result k_c) expected_t = TEQ.Equal
    then Some ()
    else None in

  if Some? (check_ret_t f_bs)
  then Some Substitutive_invariant_combinator
  else begin
    let? g_bs, g_bs_kinds, rest_bs =
      let g_sig_bs =
        let _, sig = Env.inst_tscheme_with n_sig_ts [U_name u] in
        sig |> U.arrow_formals
            |> fst
            |> (fun (a::bs) ->
               let sig_bs, bs = List.splitAt num_effect_params bs in
               let ss = List.fold_left2 (fun ss sig_b b ->
                 ss@[NT (sig_b.binder_bv, b.binder_bv |> S.bv_to_name)]
               ) [NT (a.binder_bv, a_b.binder_bv |> S.bv_to_name)] sig_bs eff_params_bs in
               bs |> SS.subst_binders ss) in

      let? g_bs, rest_bs =
        if List.length rest_bs < List.length g_sig_bs
        then None
        else List.splitAt (List.length g_sig_bs) rest_bs |> Some in

      let? g_bs_kinds = eq_binders env g_sig_bs g_bs in

      (g_bs, g_bs_kinds, rest_bs) |> Some in

    // check subcomp return type is expected
    let? _ret_t_ok_ = check_ret_t g_bs in

    // rest of the binders are ad-hoc
    let rest_kinds = List.map (fun _ -> Ad_hoc_binder) rest_bs in

    Some (([Type_binder]        @
           eff_params_bs_kinds  @
           f_bs_kinds           @
           g_bs_kinds@rest_kinds@
           [Repr_binder]) |> Substitutive_combinator)
  end

//
// Validate indexed effect subcomp (including polymonadic subcomp) shape
//   and compute its kind
//
let validate_indexed_effect_subcomp_shape (env:env)
  (m_eff_name n_eff_name:lident)
  (m_sig_ts n_sig_ts:tscheme)
  (m_repr_ts n_repr_ts:option tscheme)
  (u:univ_name)
  (subcomp_t:typ)
  (num_effect_params:int)
  (r:Range.range)
  : typ & indexed_effect_combinator_kind =

  let subcomp_name = BU.format2 "%s <: %s"
    (string_of_lid m_eff_name)
    (string_of_lid n_eff_name) in

  let a_b = (U_name u) |> U.type_with_u |> S.gen_bv "a" None |> S.mk_binder in

  let rest_bs =
    match (SS.compress subcomp_t).n with
    | Tm_arrow {bs} when List.length bs >= 2 ->
      // peel off a:Type
      let ({binder_bv=a})::bs = SS.open_binders bs in
      // peel off f:repr from the end
      bs |> List.splitAt (List.length bs - 1) |> fst
         |> SS.subst_binders [NT (a, bv_to_name a_b.binder_bv)]
    | _ ->
      raise_error r Errors.Fatal_UnexpectedEffect
        (BU.format2 "Type of %s is not an arrow with >= 2 binders (%s)"
          subcomp_name
          (show subcomp_t)) in

  let f, guard_f =
    let repr, g = TcUtil.fresh_effect_repr
      (Env.push_binders env (a_b::rest_bs))
      r
      m_eff_name
      m_sig_ts
      m_repr_ts
      (U_name u)
      (a_b.binder_bv |> S.bv_to_name) in
    repr |> S.gen_bv "f" None |> S.mk_binder, g in
    
  let ret_t, guard_ret_t = TcUtil.fresh_effect_repr
    (Env.push_binders env (a_b::rest_bs))
    r
    n_eff_name
    n_sig_ts
    n_repr_ts
    (U_name u)
    (a_b.binder_bv |> S.bv_to_name) in
  
  let pure_wp_uvar, guard_wp = pure_wp_uvar
    (Env.push_binders env (a_b::rest_bs))
    ret_t
    (BU.format1 "implicit for pure_wp in checking %s" subcomp_name)
    r in

  let c = S.mk_Comp ({
    comp_univs = [ Env.new_u_univ () ];
    effect_name = PC.effect_PURE_lid;
    result_typ = ret_t;
    effect_args = [ pure_wp_uvar |> S.as_arg ];
    flags = [] }) in

  let k = U.arrow (a_b::rest_bs@[f]) c in

  if Debug.medium () || !dbg_LayeredEffectsTc then
    BU.print1 "Expected type of subcomp before unification: %s\n"
      (show k);

  let guard_eq =
    match Rel.teq_nosmt env subcomp_t k with
    | None ->
      raise_error r Errors.Fatal_UnexpectedEffect
                   (BU.format2 "Unexpected type of %s (%s)\n"
                     subcomp_name
                     (show subcomp_t))
    | Some g -> g in


  Rel.force_trivial_guard env (Env.conj_guards [
    guard_f;
    guard_ret_t;
    guard_wp;
    guard_eq ]);

  let k = k |> N.remove_uvar_solutions env |> SS.compress in

  let kopt = subcomp_combinator_kind env m_eff_name n_eff_name
    m_sig_ts n_sig_ts
    m_repr_ts n_repr_ts
    u
    k
    num_effect_params in

  let kind =
    match kopt with
    | None ->
      log_ad_hoc_combinator_warning subcomp_name r;
      Ad_hoc_combinator
    | Some k -> k in

  if Debug.medium () || !dbg_LayeredEffectsTc
  then BU.print2 "Subcomp %s has %s kind\n" subcomp_name (show kind);


  k, kind

//
// Check the kind of an indexed effect ite combinator
//
let ite_combinator_kind (env:env)
  (eff_name:lident)
  (sig_ts repr_ts:tscheme)
  (u:univ_name)
  (tm:term)
  (num_effect_params:int)

  : option S.indexed_effect_combinator_kind =

  let a_b::rest_bs, _, _ = U.abs_formals tm in

  let? eff_params_bs, eff_params_bs_kinds, rest_bs =
    if num_effect_params = 0
    then ([], [], rest_bs) |> Some
    else let _, sig = Env.inst_tscheme_with sig_ts [U_name u] in
         let _::sig_bs, _ = sig |> U.arrow_formals in
         let sig_effect_params_bs = List.splitAt num_effect_params sig_bs |> fst in
         let eff_params_bs, rest_bs = List.splitAt num_effect_params rest_bs in
         let? eff_params_bs_kinds = eq_binders env sig_effect_params_bs eff_params_bs in
         (eff_params_bs, eff_params_bs_kinds, rest_bs) |> Some in

  let? f_bs, f_bs_kinds, rest_bs =
    let f_sig_bs =
      let _, sig = Env.inst_tscheme_with sig_ts [U_name u] in
      sig |> U.arrow_formals
          |> fst
          |> (fun (a::bs) ->
             let sig_bs, bs = List.splitAt num_effect_params bs in
             let ss = List.fold_left2 (fun ss sig_b b ->
               ss@[NT (sig_b.binder_bv, b.binder_bv |> S.bv_to_name)]
             ) [NT (a.binder_bv, a_b.binder_bv |> S.bv_to_name)] sig_bs eff_params_bs in
             bs |> SS.subst_binders ss) in

    let? f_bs, rest_bs =
      if List.length rest_bs < List.length f_sig_bs
      then None
      else List.splitAt (List.length f_sig_bs) rest_bs |> Some in

    let? f_bs_kinds = eq_binders env f_sig_bs f_bs in

    (f_bs, f_bs_kinds, rest_bs) |> Some in

  let? rest_bs, [f_b; g_b; p_b] =
    if List.length rest_bs >= 3
    then List.splitAt (List.length rest_bs - 3) rest_bs |> Some
    else None in

  let? _f_b_ok_ =
    let expected_f_b_sort =
      let _, t = Env.inst_tscheme_with repr_ts [U_name u] in
      S.mk_Tm_app t
        ((a_b.binder_bv |> S.bv_to_name |> S.as_arg)::
         (List.map (fun {binder_bv=b} -> b |> S.bv_to_name |> S.as_arg) (eff_params_bs@f_bs)))
        Range.dummyRange in
    if TEQ.eq_tm env f_b.binder_bv.sort expected_f_b_sort = TEQ.Equal
    then Some ()
    else None in

  let check_g_b (f_or_g_bs:binders) : option unit =
    let expected_g_b_sort =
      let _, t = Env.inst_tscheme_with repr_ts [U_name u] in
      S.mk_Tm_app t
        ((a_b.binder_bv |> S.bv_to_name |> S.as_arg)::
         (List.map (fun {binder_bv=b} -> b |> S.bv_to_name |> S.as_arg) (eff_params_bs@f_or_g_bs)))
        Range.dummyRange in
    if TEQ.eq_tm env g_b.binder_bv.sort expected_g_b_sort = TEQ.Equal
    then Some ()
    else None in

  if Some? (check_g_b f_bs)
  then Some Substitutive_invariant_combinator
  else begin
    let? g_bs, g_bs_kinds, rest_bs =
      let g_sig_bs =
        let _, sig = Env.inst_tscheme_with sig_ts [U_name u] in
        sig |> U.arrow_formals
            |> fst
            |> (fun (a::bs) ->
               let sig_bs, bs = List.splitAt num_effect_params bs in
               let ss = List.fold_left2 (fun ss sig_b b ->
                 ss@[NT (sig_b.binder_bv, b.binder_bv |> S.bv_to_name)]
               ) [NT (a.binder_bv, a_b.binder_bv |> S.bv_to_name)] sig_bs eff_params_bs in
               bs |> SS.subst_binders ss) in

      let? g_bs, rest_bs =
        if List.length rest_bs < List.length g_sig_bs
        then None
        else List.splitAt (List.length g_sig_bs) rest_bs |> Some in

      let? g_bs_kinds = eq_binders env g_sig_bs g_bs in

      (g_bs, g_bs_kinds, rest_bs) |> Some in

    let? _g_b_ok_ = check_g_b g_bs in

    let rest_kinds = List.map (fun _ -> Ad_hoc_binder) rest_bs in

    Some ([Type_binder]      @
          eff_params_bs_kinds@
          f_bs_kinds         @
          g_bs_kinds         @
          rest_kinds         @
          [Repr_binder; Repr_binder; Substitutive_binder] |> Substitutive_combinator)

  end

//
// Validate the shape of an indexed effect ite combinator,
//   and compute its kind
//
let validate_indexed_effect_ite_shape (env:env)
  (eff_name:lident)
  (sig_ts:tscheme)
  (repr_ts:tscheme)
  (u:univ_name)
  (ite_ty:typ)
  (ite_tm:term)
  (num_effect_params:int)
  (r:Range.range)

  : term & indexed_effect_combinator_kind =

  let ite_name = BU.format1 "ite_%s" (string_of_lid eff_name) in

  let a_b = u |> U_name |> U.type_with_u |> S.gen_bv "a" None |> S.mk_binder in

  let rest_bs =
    match (SS.compress ite_ty).n with
    | Tm_arrow {bs} when List.length bs >= 4 ->
      // peel off a:Type
      let (({binder_bv=a})::bs) = SS.open_binders bs in
      // peel off f:repr, g:repr, p:bool from the end
      bs |> List.splitAt (List.length bs - 3) |> fst
         |> SS.subst_binders [NT (a, a_b.binder_bv |> S.bv_to_name)]
    | _ ->
      raise_error r Errors.Fatal_UnexpectedEffect
        (BU.format2 "Type of %s is not an arrow with >= 4 binders (%s)"
          ite_name
          (show ite_ty)) in

  let f, guard_f =
    let repr, g = TcUtil.fresh_effect_repr
      (Env.push_binders env (a_b::rest_bs))
      r
      eff_name
      sig_ts
      (Some repr_ts)
      (U_name u)
      (a_b.binder_bv |> S.bv_to_name) in
    repr |> S.gen_bv "f" None |> S.mk_binder, g in

  let g, guard_g =
    let repr, g = TcUtil.fresh_effect_repr
      (Env.push_binders env (a_b::rest_bs))
      r
      eff_name
      sig_ts
      (Some repr_ts)
      (U_name u)
      (a_b.binder_bv |> S.bv_to_name) in
    repr |> S.gen_bv "g" None |> S.mk_binder, g in

  let p = S.gen_bv "p" None U.t_bool |> S.mk_binder in

  let body_tm, guard_body = TcUtil.fresh_effect_repr
    (Env.push_binders env (a_b::rest_bs@[p]))
    r
    eff_name
    sig_ts
    (Some repr_ts)
    (U_name u)
    (a_b.binder_bv |> S.bv_to_name) in
  
  let k = U.abs (a_b::rest_bs@[f; g; p]) body_tm None in
  
  let guard_eq =
    match Rel.teq_nosmt env ite_tm k with
    | None ->
      raise_error r Errors.Fatal_UnexpectedEffect
                   (BU.format2 "Unexpected term for %s (%s)\n"
                     ite_name
                     (show ite_tm))
    | Some g -> g in

  Rel.force_trivial_guard env (Env.conj_guards [
    guard_f;
    guard_g;
    guard_body;
    guard_eq ]);
    
  let k = k |> N.remove_uvar_solutions env |> SS.compress in

  let kopt = ite_combinator_kind env eff_name sig_ts repr_ts u k num_effect_params in

  let kind =
    match kopt with
    | None ->
      log_ad_hoc_combinator_warning ite_name r;
      Ad_hoc_combinator
    | Some k -> k in

  if Debug.medium () || !dbg_LayeredEffectsTc
  then BU.print2 "Ite %s has %s kind\n" ite_name
         (show kind);

  k, kind


//
// Validate the shape of an indexed effect close combinator
//
// Only substitutive close combinator is supported
//  fun (a:Type) (b:Type) (is:b -> is_t) (f:(x:a -> repr a (is x))) -> repr a js
//
let validate_indexed_effect_close_shape (env:env)
  (eff_name:lident)
  (sig_ts:tscheme)
  (repr_ts:tscheme)
  (u_a:univ_name)
  (u_b:univ_name)
  (close_tm:term)
  (num_effect_params:int)
  (r:Range.range) : term =

  let close_name = BU.format1 "close_%s" (string_of_lid eff_name) in

  let b_b = u_b |> U_name |> U.type_with_u |> S.gen_bv "b" None |> S.mk_binder in

  let a_b::sig_bs = Env.inst_tscheme_with sig_ts [U_name u_a] |> snd |> U.arrow_formals |> fst in
  let eff_params_bs, sig_bs = List.splitAt num_effect_params sig_bs in
  let bs = List.map (fun b ->
    let x_b = S.gen_bv "x" None (S.bv_to_name b_b.binder_bv) |> S.mk_binder in
    {b with binder_bv={b.binder_bv with sort=U.arrow [x_b] (S.mk_Total b.binder_bv.sort)}}
  ) sig_bs in
  let f_b =
    let _, repr_t = Env.inst_tscheme_with repr_ts [U_name u_a] in
    let x_b = S.gen_bv "x" None (S.bv_to_name b_b.binder_bv) |> S.mk_binder in
    let is_args =
      List.map (fun {binder_bv} ->
                S.mk_Tm_app (S.bv_to_name binder_bv) [x_b.binder_bv |> S.bv_to_name |> S.as_arg] Range.dummyRange
                |> S.as_arg) bs in
    let repr_app = S.mk_Tm_app repr_t ((a_b.binder_bv |> S.bv_to_name |> S.as_arg)::is_args) Range.dummyRange in
    let f_sort = U.arrow [x_b] (S.mk_Total repr_app) in
    S.gen_bv "f" None f_sort |> S.mk_binder in
  let env = Env.push_binders env (a_b::b_b::(eff_params_bs@bs)) in 
  let body_tm, g_body = TcUtil.fresh_effect_repr
    env
    r
    eff_name
    sig_ts
    (Some repr_ts)
    (U_name u_a)
    (a_b.binder_bv |> S.bv_to_name) in
  
  let k = U.abs (a_b::b_b::(eff_params_bs@bs@[f_b])) body_tm None in

  let g_eq =
    match Rel.teq_nosmt env close_tm k with
    | None ->
      raise_error r Errors.Fatal_UnexpectedEffect
                   (BU.format2 "Unexpected term for %s (%s)\n"
                     close_name
                     (show close_tm))
    | Some g -> g in
  
  Rel.force_trivial_guard env (Env.conj_guard g_body g_eq);

  k |> N.remove_uvar_solutions env |> SS.compress

//
// Check the kind of an indexed effect lift
//
let lift_combinator_kind (env:env)
  (m_eff_name:lident)
  (m_sig_ts:tscheme)
  (m_repr_ts:option tscheme)
  (u:univ_name)
  (k:typ)
  : option (list indexed_effect_binder_kind) =

  let a_b::rest_bs, _ = U.arrow_formals k in

  let? f_bs, f_bs_kinds, rest_bs =
    let f_sig_bs =
      let _, sig = Env.inst_tscheme_with m_sig_ts [U_name u] in
      sig |> U.arrow_formals
          |> fst
          |> (fun (a::bs) ->
             SS.subst_binders [NT (a.binder_bv, a_b.binder_bv |> S.bv_to_name)] bs) in

    let? f_bs, rest_bs =
      if List.length rest_bs < List.length f_sig_bs
      then None
      else List.splitAt (List.length f_sig_bs) rest_bs |> Some in

    let? f_bs_kinds = eq_binders env f_sig_bs f_bs in

    (f_bs, f_bs_kinds, rest_bs) |> Some in

  let? rest_bs, f_b =
    if List.length rest_bs >= 1
    then let rest_bs, [f_b] = List.splitAt (List.length rest_bs - 1) rest_bs in
         (rest_bs, f_b) |> Some
    else None in

  let? _f_b_ok_ =
    let expected_f_b_sort =
      match m_repr_ts with
      | Some repr_ts ->
        let _, t = Env.inst_tscheme_with repr_ts [U_name u] in
        S.mk_Tm_app t
          ((a_b.binder_bv |> S.bv_to_name |> S.as_arg)::
           (List.map (fun {binder_bv=b} -> b |> S.bv_to_name |> S.as_arg) f_bs))
          Range.dummyRange
      | None ->
        U.arrow [S.null_binder S.t_unit]
          (mk_Comp ({
             comp_univs = [U_name u];
             effect_name = m_eff_name;
             result_typ = a_b.binder_bv |> S.bv_to_name;
             effect_args = f_bs |> List.map (fun b -> b.binder_bv |> S.bv_to_name |> S.as_arg);
             flags = []})) in
    if TEQ.eq_tm env f_b.binder_bv.sort expected_f_b_sort = TEQ.Equal
    then Some ()
    else None in

  let rest_kinds = List.map (fun _ -> Ad_hoc_binder) rest_bs in

  Some ([Type_binder]@
        f_bs_kinds   @
        rest_kinds   @
        [Repr_binder])

//
// Validate the shape of an indexed effect lift,
//   and compute its kind
//
let validate_indexed_effect_lift_shape (env:env)
  (m_eff_name n_eff_name:lident)
  (u:univ_name)
  (lift_t:typ)
  (r:Range.range)
  : typ & indexed_effect_combinator_kind =

  let lift_name = BU.format2 "%s ~> %s"
    (string_of_lid m_eff_name)
    (string_of_lid n_eff_name) in

  let lift_t_shape_error s = BU.format2 "Unexpected shape of lift %s, reason:%s"
    lift_name
    s in

  let m_ed, n_ed = Env.get_effect_decl env m_eff_name, Env.get_effect_decl env n_eff_name in

  let a_b = (U_name u) |> U.type_with_u |> S.gen_bv "a" None |> S.mk_binder in

  let rest_bs, lift_eff =
    match (SS.compress lift_t).n with
    | Tm_arrow {bs; comp=c} when List.length bs >= 2 ->
      // peel off a:Type
      let (({binder_bv=a})::bs) = SS.open_binders bs in
      // peel off f:repr from the end
      bs |> List.splitAt (List.length bs - 1) |> fst
         |> SS.subst_binders [NT (a, bv_to_name a_b.binder_bv)],
      U.comp_effect_name c |> Env.norm_eff_name env
    | _ ->
      raise_error r Errors.Fatal_UnexpectedExpressionType
                   (lift_t_shape_error "either not an arrow, or not enough binders") in

  if (not ((lid_equals lift_eff PC.effect_PURE_lid) ||
           (lid_equals lift_eff PC.effect_GHOST_lid && Env.is_erasable_effect env m_eff_name)))
  then raise_error r Errors.Fatal_UnexpectedExpressionType
                    (lift_t_shape_error "the lift combinator has an unexpected effect: \
                      it must either be PURE or if the source effect is erasable then may be GHOST");

  let f, guard_f =
    let repr, g = TcUtil.fresh_effect_repr
      (Env.push_binders env (a_b::rest_bs))
      r
      m_eff_name
      (U.effect_sig_ts m_ed.signature)
      (U.get_eff_repr m_ed)
      (U_name u)
      (a_b.binder_bv |> S.bv_to_name) in

    repr |> S.gen_bv "f" None |> S.mk_binder, g in

  let ret_t, guard_ret_t = TcUtil.fresh_effect_repr
      (Env.push_binders env (a_b::rest_bs))
      r
      n_eff_name
      (U.effect_sig_ts n_ed.signature)
      (U.get_eff_repr n_ed)
      (U_name u)
      (a_b.binder_bv |> S.bv_to_name) in
      
  let pure_wp_uvar, guard_wp = pure_wp_uvar (Env.push_binders env (a_b::rest_bs)) ret_t
    (BU.format1 "implicit for pure_wp in typechecking lift %s" lift_name) r in

  let c = S.mk_Comp ({
    comp_univs = [ Env.new_u_univ () ];
    effect_name = lift_eff;
    result_typ = ret_t;
    effect_args = [ pure_wp_uvar |> S.as_arg ];
    flags = [] }) in

  let k = U.arrow (a_b::rest_bs@[f]) c in

  let guard_eq =
    match Rel.teq_nosmt env lift_t k with
    | None ->
      raise_error r Errors.Fatal_UnexpectedEffect
                   (BU.format2 "Unexpected type of %s (%s)\n"
                     lift_name
                     (show lift_t))
    | Some g -> g in

  Rel.force_trivial_guard env (Env.conj_guards [
    guard_f;
    guard_ret_t;
    guard_wp;
    guard_eq ]);

  let k = k |> N.remove_uvar_solutions env |> SS.compress in

  let lopt = lift_combinator_kind env m_eff_name (U.effect_sig_ts m_ed.signature)
    (U.get_eff_repr m_ed)
    u k in

  let kind =
    match lopt with
    | None ->
      log_ad_hoc_combinator_warning lift_name r;
      Ad_hoc_combinator
    | Some l -> Substitutive_combinator l in

  if Debug.medium () || !dbg_LayeredEffectsTc
  then BU.print2 "Lift %s has %s kind\n" lift_name
         (show kind);


  k, kind

(*
 * Typechecking of layered effects
 *
 * If the effect is reifiable, returns reify__M sigelt also
 *)
let tc_layered_eff_decl env0 (ed : S.eff_decl) (quals : list qualifier) (attrs : list S.attribute) =
Errors.with_ctx (BU.format1 "While checking layered effect definition `%s`" (string_of_lid ed.mname)) (fun () ->
  if !dbg_LayeredEffectsTc then
    BU.print1 "Typechecking layered effect: \n\t%s\n" (show ed);

  //we don't support effect binders in layered effects yet
  if List.length ed.univs <> 0 || List.length ed.binders <> 0 then
    raise_error ed.mname Errors.Fatal_UnexpectedEffect 
      ("Binders are not supported for layered effects (" ^ (string_of_lid ed.mname) ^")");

  let log_combinator s (us, t, ty) =
    if !dbg_LayeredEffectsTc then
      BU.print4 "Typechecked %s:%s = %s:%s\n"
        (string_of_lid ed.mname) s
        (Print.tscheme_to_string (us, t)) (Print.tscheme_to_string (us, ty)) in

  //helper function to get (a:Type ?u), returns the binder and ?u
  let fresh_a_and_u_a (a:string) : binder & universe = U.type_u () |> (fun (t, u) -> S.gen_bv a None t |> S.mk_binder, u) in
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
  let num_effect_params, signature =
    let n, sig_ts =
      match ed.signature with
      | Layered_eff_sig (n, ts) -> n, ts
      | _ -> failwith "Impossible (tc_layered_eff_decl with a wp effect sig" in

    Errors.with_ctx ("While checking the effect signature") (fun () ->
      let r = (snd sig_ts).pos in
      let sig_us, sig_t, sig_ty = check_and_gen "signature" 1 sig_ts in

      let us, t = SS.open_univ_vars sig_us sig_t in
      let env = Env.push_univ_vars env0 us in

      let a, u = fresh_a_and_u_a "a" in
      let rest_bs =
        TcUtil.layered_effect_indices_as_binders env r ed.mname (sig_us, sig_t) u (a.binder_bv |> S.bv_to_name) in
      let bs = a::rest_bs in
      let k = U.arrow bs (S.mk_Total S.teff) in  //U.arrow does closing over bs
      let g_eq = Rel.teq env t k in
      Rel.force_trivial_guard env g_eq;
      n, (sig_us, SS.close_univ_vars us (k |> N.remove_uvar_solutions env), sig_ty)) in

  log_combinator "signature" signature;

  (*
   * Effect repr
   *
   * The repr must have the type:
   *   a:Type -> <binders for effect indices> -> Type  //polymorphic in one universe (that of a)
   *)
  let repr =
    Errors.with_ctx ("While checking the effect repr") (fun () ->
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
      let k = U.arrow bs (U.type_u () |> (fun (t, u) -> S.mk_Total t)) in  //note the universe of Tot need not be u
      let g = Rel.teq env ty k in
      Rel.force_trivial_guard env g;
      (repr_us, repr_t, SS.close_univ_vars us (k |> N.remove_uvar_solutions env)))
  in

  log_combinator "repr" repr;

  //helper function that creates an application node (repr<u> a_tm ?u1 ... ?un)
  //returns the application term and the guard for the introduced uvars (see TcUtil.fresh_layered_effect_repr)
  let fresh_repr r env u a_tm =
    let signature_ts = let us, t, _ = signature in (us, t) in
    let repr_ts = let us, t, _ = repr in (us, t) in
    TcUtil.fresh_effect_repr env r ed.mname signature_ts (Some repr_ts) u a_tm in

  let not_an_arrow_error comb n t r =
    raise_error r Errors.Fatal_UnexpectedEffect
      (BU.format5 "Type of %s:%s is not an arrow with >= %s binders (%s::%s)" (string_of_lid ed.mname) comb
        (show n) (tag_of t) (show t))
  in

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
    Errors.with_ctx ("While checking the return combinator") (fun () ->
      let return_repr_ts = ed |> U.get_return_repr |> must in
      let r = (snd return_repr_ts).pos in
      let ret_us, ret_t, ret_ty = check_and_gen "return_repr" 1 return_repr_ts in

      let us, ty = SS.open_univ_vars ret_us ret_ty in
      let env = Env.push_univ_vars env0 us in

      let a, u_a = fresh_a_and_u_a "a" in
      let x_a = fresh_x_a "x" a in
      let rest_bs =
        match (SS.compress ty).n with
        | Tm_arrow {bs} when List.length bs >= 2 ->
          let (({binder_bv=a'})::({binder_bv=x'})::bs) = SS.open_binders bs in
          bs |> SS.subst_binders [NT (a', bv_to_name a.binder_bv)]
             |> SS.subst_binders [NT (x', bv_to_name x_a.binder_bv)]
        | _ -> not_an_arrow_error "return" 2 ty r in
      let bs = a::x_a::rest_bs in
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (a.binder_bv |> S.bv_to_name) in
      let k = U.arrow bs (S.mk_Total repr) in
      let g_eq = Rel.teq env ty k in
      Rel.force_trivial_guard env (Env.conj_guard g g_eq);

      let k = k |> N.remove_uvar_solutions env in

      ret_us, ret_t, k |> SS.close_univ_vars us) in

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
  let bind_repr, bind_kind =
    Errors.with_ctx ("While checking the bind combinator") (fun () ->
      let bind_repr_ts = ed |> U.get_bind_repr |> must in
      let r = (snd bind_repr_ts).pos in
      let bind_us, bind_t, bind_ty = check_and_gen "bind_repr" 2 bind_repr_ts in

      let us, ty = SS.open_univ_vars bind_us bind_ty in
      let env = Env.push_univ_vars env0 us in

      let k, kind =
        let sig_ts = let us, t, _ = signature in (us, t) in
        let repr_ts = let us, t, _ = repr in (us, t) in
        validate_indexed_effect_bind_shape env
          ed.mname ed.mname ed.mname
          sig_ts sig_ts sig_ts
          (Some repr_ts) (Some repr_ts) (Some repr_ts)
          us
          ty
          r
          num_effect_params
          (U.has_attribute ed.eff_attrs PC.bind_has_range_args_attr) in

      (bind_us, bind_t, k |> SS.close_univ_vars bind_us), kind) in

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
  let stronger_repr, subcomp_kind =
    Errors.with_ctx ("While checking the subcomp combinator") (fun () ->
      let stronger_repr =
        let ts = ed |> U.get_stronger_repr |> must in
        match (ts |> snd |> SS.compress).n with
        | Tm_unknown ->
          let signature_ts = let (us, t, _) = signature in (us, t) in
          let _, signature_t = Env.inst_tscheme_with signature_ts [U_unknown] in
          (match (SS.compress signature_t).n with
           | Tm_arrow {bs} ->
             let bs = SS.open_binders bs in
             let repr_t =
               let repr_ts = let (us, t, _) = repr in (us, t) in
               Env.inst_tscheme_with repr_ts [U_unknown] |> snd in
             let repr_t_applied = mk
               (Tm_app {hd=repr_t;
                        args=bs |> List.map (fun b -> b.binder_bv) |> List.map S.bv_to_name |> List.map S.as_arg})
               (Ident.range_of_lid ed.mname) in
             let f_b = S.null_binder repr_t_applied in
             [], {U.abs (bs@[f_b]) (f_b.binder_bv |> S.bv_to_name) None
                  with pos=Ident.range_of_lid ed.mname}
           | _ -> failwith "Impossible!")
        | _ -> ts in
        
      let r = (snd stronger_repr).pos in

      let stronger_us, stronger_t, stronger_ty = check_and_gen "stronger_repr" 1 stronger_repr in

      if !dbg_LayeredEffectsTc then
        BU.print2 "stronger combinator typechecked with term: %s and type: %s\n"
          (Print.tscheme_to_string (stronger_us, stronger_t))
          (Print.tscheme_to_string (stronger_us, stronger_ty));

      let us, ty = SS.open_univ_vars stronger_us stronger_ty in
      let env = Env.push_univ_vars env0 us in

      let k, kind =
        let sig_ts = let us, t, _ = signature in (us, t) in
        let repr_ts = let us, t, _ = repr in (us, t) in
        validate_indexed_effect_subcomp_shape env
          ed.mname ed.mname
          sig_ts sig_ts
          (Some repr_ts) (Some repr_ts)
          (List.hd us)
          ty
          num_effect_params
          r in

      (stronger_us, stronger_t, k |> SS.close_univ_vars stronger_us), kind) in

  log_combinator "stronger_repr" stronger_repr;

  (*
   * This combinator is also optional
   * If so, we add a default:
   * fun (a:Type) (signature_bs) (f:repr a signature_bs) (g:repr a signature_bs) (b:bool) -> repr a signature_bs
   *)
  let if_then_else, ite_kind =
    Errors.with_ctx ("While checking the if_then_else combinator") (fun () ->
      let if_then_else_ts =
        let ts = ed |> U.get_layered_if_then_else_combinator |> must |> fst in
        match (ts |> snd |> SS.compress).n with
        | Tm_unknown ->
          let signature_ts = let (us, t, _) = signature in (us, t) in
          let _, signature_t = Env.inst_tscheme_with signature_ts [U_unknown] in
          (match (SS.compress signature_t).n with
           | Tm_arrow {bs} ->
             let bs = SS.open_binders bs in
             let repr_t =
               let repr_ts = let (us, t, _) = repr in (us, t) in
               Env.inst_tscheme_with repr_ts [U_unknown] |> snd in
             let repr_t_applied = mk
               (Tm_app {hd=repr_t;
                        args=bs |> List.map (fun b -> b.binder_bv) |> List.map S.bv_to_name |> List.map S.as_arg})
               (Ident.range_of_lid ed.mname) in
             let f_b = S.null_binder repr_t_applied in
             let g_b = S.null_binder repr_t_applied in
             let b_b = S.null_binder U.t_bool in
             [], {U.abs (bs@[f_b; g_b; b_b]) repr_t_applied None
                  with pos=Ident.range_of_lid ed.mname}
           | _ -> failwith "Impossible!")
        | _ -> ts in

      let r = (snd if_then_else_ts).pos in
      let if_then_else_us, if_then_else_t, if_then_else_ty = check_and_gen "if_then_else" 1 if_then_else_ts in

      let us, t = SS.open_univ_vars if_then_else_us if_then_else_t in
      let _, ty = SS.open_univ_vars if_then_else_us if_then_else_ty in
      let env = Env.push_univ_vars env0 us in

      let k, kind = 
        let sig_ts = let us, t, _ = signature in (us, t) in
        let repr_ts = let us, t, _ = repr in (us, t) in
        validate_indexed_effect_ite_shape env
          ed.mname
          sig_ts
          repr_ts
          (List.hd us)
          ty
          t
          num_effect_params
          r in
   
      (if_then_else_us,
       k |> SS.close_univ_vars if_then_else_us,
       if_then_else_ty), kind) in

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
    let r = (ed |> U.get_layered_if_then_else_combinator |> must |> fst |> snd).pos in

    let ite_us, ite_t, _ = if_then_else in

    let us, ite_t = SS.open_univ_vars ite_us ite_t in
    let env, ite_t_applied, a_b, f_b, g_b, p_t =
      match (SS.compress ite_t).n with
      | Tm_abs {bs} ->
        let bs = SS.open_binders bs in
        let f_b, g_b, p_b =
          bs
          |> List.splitAt (List.length bs - 3)
          |> snd
          |> (fun l -> let [f; g; p] = l in f, g, p) in
        let env =  Env.push_binders (Env.push_univ_vars env0 us) bs in
        env,
        S.mk_Tm_app ite_t
          (bs |> List.map (fun b -> S.bv_to_name b.binder_bv, U.aqual_of_binder b))
          r |> N.normalize [Env.Beta] env,  //beta-reduce
        bs |> List.hd, f_b, g_b, (S.bv_to_name p_b.binder_bv)
      | _ -> failwith "Impossible! ite_t must have been an abstraction with at least 3 binders" in

    let subcomp_a_b, subcomp_bs, subcomp_f_b, subcomp_c =
      let _, _, subcomp_ty = stronger_repr in
      let _, subcomp_ty = SS.open_univ_vars us subcomp_ty in
      match (SS.compress subcomp_ty).n with
      | Tm_arrow {bs; comp=c} ->
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
            let ctx_uvar_meta = BU.map_option Ctx_uvar_meta_attr attr_opt in
            Env.new_implicit_var_aux
              (BU.format1 "uvar for subcomp %s binder when checking ite soundness"
                (show b))
              r
              env
              sort
              Strict
              ctx_uvar_meta
              false
          in
          subst@[NT (b.binder_bv, t)], uvars@[t], conj_guard g g_t)
          ([NT (subcomp_a_b.binder_bv, S.bv_to_name a_b.binder_bv)],
           [],
           Env.trivial_guard)
      in

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
          let _, _, g = Env.new_implicit_var_aux "tc_layered_effect_decl.g_precondition" r env
            (U.mk_squash S.U_zero fml)
            Strict
            (Ctx_uvar_meta_attr attr |> Some)
            false
          in
          g
      in

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
        (S.lid_as_fv PC.not_lid None |> S.fv_to_tm)
        [p_t |> U.b2t |> S.as_arg]
        r in
      let env = Env.push_bv env (S.new_bv None not_p) in
      ignore (check_branch env g_b.binder_bv.sort ite_soundness_tac_attr) in

    ()
  )  //Errors.with_ctx
  in

  //
  // Close combinator is optional,
  //   typecheck it only if it is set, else leave it as None
  //
  let close_ =
    Errors.with_ctx ("While checking the close combinator") (fun () ->
      let ts_opt = ed |> U.get_layered_close_combinator in
      match ts_opt with
      | None -> None
      | Some close_ts ->
        let r = (snd close_ts).pos in
        let close_us, close_t, close_ty = check_and_gen "close" 2 close_ts in
        let us, t = SS.open_univ_vars close_us close_t in
        let env = Env.push_univ_vars env0 us in
        let k =
          let sig_ts = let us, t, _ = signature in (us, t) in
          let repr_ts = let us, t, _ = repr in (us, t) in
          let [u_a; u_b] = us in
          validate_indexed_effect_close_shape env ed.mname sig_ts repr_ts u_a u_b t num_effect_params r
        in
        Some (close_us, k |> SS.close_univ_vars close_us, close_ty)) in
  
  //
  // Checking the soundness of the close combinator
  //
  // Close combinator has the shape:
  //   fun (a:Type) (b:type) (is:a -> is_t) (f:(x:a -> repr a (is x))) -> repr a js
  //
  // We check:
  //
  // a, b, is, x:a |- subcomp (repr a (is x)) (repr a js)
  //
  // Operationally, we create names for a, b, is, and x
  //   substitute them in the subcomp combinator,
  //   and prove its (Pure) precondition
  //
  let _close_is_sound = Errors.with_ctx ("While checking the soundness of the close combinator") (fun () ->
    match close_ with
    | None -> ()
    | Some close_ ->
      let us, close_tm, _ = close_ in
      let r = close_tm.pos in
      let _ =
        let supported_subcomp =
          match subcomp_kind with
          | Substitutive_combinator l ->
            not (List.contains Ad_hoc_binder l)
          | _ -> false in
        
        if not supported_subcomp
        then raise_error r Errors.Fatal_UnexpectedEffect "close combinator is only allowed for effects with substitutive subcomp"
      in
      let us, close_tm = SS.open_univ_vars us close_tm in
      let close_bs, close_body, _ = U.abs_formals close_tm in
      let a_b::b_b::close_bs = close_bs in
      let is_bs, _ = List.splitAt (List.length close_bs - 1) close_bs in
      let x_bv = S.gen_bv "x" None (S.bv_to_name b_b.binder_bv) in
      let args1 = List.map (fun i_b ->
        S.mk_Tm_app (S.bv_to_name i_b.binder_bv) [S.as_arg (S.bv_to_name x_bv)] r
      ) is_bs in
      let args2 =
        match (SS.compress close_body).n with
        | Tm_app {args=a::args} -> args |> List.map fst
        | _ -> raise_error r Errors.Fatal_UnexpectedEffect "close combinator body not a repr" in

      let env = Env.push_binders env0 ((a_b::b_b::is_bs)@[x_bv |> S.mk_binder]) in
      let subcomp_ts =
        let (us, _, t) = stronger_repr in
        (us, t) in
      let _, subcomp_t = Env.inst_tscheme_with subcomp_ts [List.hd us |> S.U_name] in
      let a_b_subcomp::subcomp_bs, subcomp_c = U.arrow_formals_comp subcomp_t in
      let subcomp_substs = [ NT (a_b_subcomp.binder_bv, a_b.binder_bv |> S.bv_to_name) ] in
      let subcomp_f_bs, subcomp_bs = List.splitAt (List.length args1) subcomp_bs in
      let subcomp_substs = subcomp_substs @ (List.map2 (fun b arg1 ->
        NT (b.binder_bv, arg1)
      ) subcomp_f_bs args1) in
      let subcomp_g_bs, _ = List.splitAt (List.length args2) subcomp_bs in
      let subcomp_substs = subcomp_substs @ (List.map2 (fun b arg2 ->
        NT (b.binder_bv, arg2)
      ) subcomp_g_bs args2) in
      let subcomp_c = SS.subst_comp subcomp_substs subcomp_c |> Env.unfold_effect_abbrev env in
      let fml = Env.pure_precondition_for_trivial_post
        env
        (List.hd subcomp_c.comp_univs)
        subcomp_c.result_typ
        (subcomp_c.effect_args |> List.hd |> fst)
        r in
      Rel.force_trivial_guard env (fml |> NonTrivial |> Env.guard_of_guard_formula))
  in

  (*
   * Actions
   *
   * Actions must have type:
   *    <some binders> -> repr a i_1 ... i_n
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
    then raise_error r Errors.Fatal_MalformedActionDeclaration
      (BU.format3 "Action %s:%s has non-empty action params (%s)"
        (string_of_lid ed.mname) (string_of_lid act.action_name) (show act.action_params));

    let env, act =
      let usubst, us = SS.univ_var_opening act.action_univs in
      Env.push_univ_vars env us,
      { act with 
        action_univs = us;
        action_defn  = SS.subst usubst act.action_defn;
        action_typ   = SS.subst usubst act.action_typ } in
    
    let act_typ =
      match (SS.compress act.action_typ).n with
      | Tm_arrow {bs; comp=c} ->
        let ct = Env.comp_to_comp_typ env c in
        if lid_equals ct.effect_name ed.mname
        then
          let repr_ts = let us, t, _ = repr in (us, t) in
          let repr = Env.inst_tscheme_with repr_ts ct.comp_univs |> snd in
          let repr = S.mk_Tm_app
            repr
            (S.as_arg ct.result_typ::ct.effect_args)
            r in
          let c = S.mk_Total repr in
          U.arrow bs c
        else act.action_typ
      | _ -> act.action_typ in
    
    let act_typ, _, g_t = tc_tot_or_gtot_term env act_typ in
    let act_defn, _, g_d = tc_tot_or_gtot_term
      ({ Env.set_expected_typ env act_typ with instantiate_imp = false })
      act.action_defn in
    
    if Debug.medium () || !dbg_LayeredEffectsTc then
      BU.print2 "Typechecked action definition: %s and action type: %s\n"
        (show act_defn) (show act_typ);

    let k, g_k =
      let act_typ = N.normalize [Beta] env act_typ in
      match (SS.compress act_typ).n with
      | Tm_arrow {bs} ->
        let bs = SS.open_binders bs in
        let env = Env.push_binders env bs in
        let t, u = U.type_u () in
        let reason = BU.format2 "implicit for return type of action %s:%s"
          (string_of_lid ed.mname) (string_of_lid act.action_name) in
        let a_tm, _, g_tm = TcUtil.new_implicit_var reason r env t false in
        let repr, g = fresh_repr r env u a_tm in
        U.arrow bs (S.mk_Total repr), Env.conj_guard g g_tm
      | _ -> raise_error r Errors.Fatal_ActionMustHaveFunctionType
               (BU.format3 "Unexpected non-function type for action %s:%s (%s)"
                 (show ed.mname) (show act.action_name) (show act_typ)) in

    if Debug.medium () || !dbg_LayeredEffectsTc then
      BU.print1 "Expected action type: %s\n" (show k);

    let g = Rel.teq env act_typ k in
    List.iter (Rel.force_trivial_guard env) [g_t; g_d; g_k; g];

    if Debug.medium () || !dbg_LayeredEffectsTc then
      BU.print1 "Expected action type after unification: %s\n" (show k);
    
    let act_typ =
      let err_msg t = BU.format3
        "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
        (string_of_lid ed.mname) (string_of_lid act.action_name) (show t) in
      let repr_args t : universes & term & args =
        match (SS.compress t).n with
        | Tm_app {hd=head;args=a::is} ->
          (match (SS.compress head).n with
           | Tm_uinst (_, us) -> us, fst a, is
           | _ -> raise_error r Errors.Fatal_ActionMustHaveFunctionType (err_msg t))
        | _ -> raise_error r Errors.Fatal_ActionMustHaveFunctionType (err_msg t) in

      let k = N.normalize [Beta] env k in
      match (SS.compress k).n with
      | Tm_arrow {bs; comp=c} ->
        let bs, c = SS.open_comp bs c in
        let us, a, is = repr_args (U.comp_result c) in
        let ct = {
          comp_univs = us;
          effect_name = ed.mname;
          result_typ = a;
          effect_args = is;
          flags = [] } in
        U.arrow bs (S.mk_Comp ct)
      | _ -> raise_error r Errors.Fatal_ActionMustHaveFunctionType (err_msg k) in

    if Debug.medium () || !dbg_LayeredEffectsTc then
      BU.print1 "Action type after injecting it into the monad: %s\n" (show act_typ);
    
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
        else raise_error r Errors.Fatal_UnexpectedNumberOfUniverse
               (BU.format4 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                 (string_of_lid ed.mname) (string_of_lid act.action_name) (show us) (show act.action_univs))
    in

    act in

  let tc_action_with_ctx env (act:action) =
    Errors.with_ctx (BU.format1 "While checking the action %s" (string_of_lid act.action_name))
                    (fun () -> tc_action env act) in

  // set extraction mode
  let extraction_mode =
    let has_primitive_extraction =
      U.has_attribute ed.eff_attrs PC.primitive_extraction_attr in
    let is_reifiable = List.contains Reifiable quals in

    if has_primitive_extraction && is_reifiable
    then raise_error ed.mname Errors.Fatal_UnexpectedEffect
                      (BU.format1 "Effect %s is declared to be both primitive extraction and reifiable"
                        (show ed.mname)) 
    else begin
      if has_primitive_extraction
      then S.Extract_primitive
      else
        let us, a_b, rest_bs =
          let us, t = let us, t, _ = signature in us, t in
          match (SS.compress t).n with
          | Tm_arrow {bs} ->
            let a_b::rest_bs = SS.open_binders bs in
            us, a_b, rest_bs
          | _ -> failwith "Impossible!"  // there are multiple places above where we have relied on sig being an arrow
        in
        let env = Env.push_univ_vars env0 us in
        let env = Env.push_binders env [a_b] in
        let _, r = List.fold_left (fun (env, r) b ->
          let r = r && Some? (N.non_info_norm env b.binder_bv.sort) in
          Env.push_binders env [b], r) (env, true) rest_bs in
        if r &&
           Substitutive_combinator? bind_kind &&
           (is_reifiable || lid_equals ed.mname PC.effect_TAC_lid)
        then S.Extract_reify
        else let m =
               if not r
               then "one or more effect indices are informative"
               else if not (Substitutive_combinator? bind_kind)
               then "bind is not substitutive"
               else "the effect is not reifiable" in      
             S.Extract_none m
    end
  in

  if !dbg_LayeredEffectsTc
  then BU.print2 "Effect %s has extraction mode %s\n" (show ed.mname) (show extraction_mode);

  let tschemes_of (us, t, ty) k = (us, t), (us, ty), k in
  let tschemes_of2 (us, t, ty) = (us, t), (us, ty) in

  let combinators = Layered_eff ({
    l_repr = tschemes_of2 repr;
    l_return = tschemes_of2 return_repr;
    l_bind = tschemes_of bind_repr (Some bind_kind);
    l_subcomp = tschemes_of stronger_repr (Some subcomp_kind);
    l_if_then_else = tschemes_of if_then_else (Some ite_kind);
    l_close = (match close_ with
               | None -> None
               | Some (us, t, ty) -> Some ((us, t), (us, ty)));
  }) in

  { ed with
    signature     = Layered_eff_sig (num_effect_params, (let us, t, _ = signature in (us, t)));
    combinators   = combinators;
    actions       = List.map (tc_action_with_ctx env0) ed.actions;
    extraction_mode }
  )

let tc_non_layered_eff_decl env0 (ed:S.eff_decl) (_quals : list qualifier) (_attrs : list S.attribute) : S.eff_decl =
Errors.with_ctx (BU.format1 "While checking effect definition `%s`" (string_of_lid ed.mname)) (fun () ->
  if !dbg then
    BU.print1 "Typechecking eff_decl: \n\t%s\n" (show ed);

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
      let tmp_t = U.arrow bs (S.mk_Total S.t_unit) in  //create a temporary bs -> Tot unit
      let us, tmp_t = Gen.generalize_universes env0 tmp_t in
      us, tmp_t |> U.arrow_formals |> fst |> SS.close_binders in

    match ed_univs with
    | [] -> us, bs  //if no annotated universes, return us, bs
    | _ ->
      let open FStarC.Pprint in
      let open FStarC.Class.PP in
      let open FStarC.Errors.Msg in
      //if ed.univs is already set, it must be the case that us = ed.univs, else error out
      if (List.length ed_univs = List.length us &&
         List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) ed_univs us)
      then us, bs
      else raise_error ed.mname Errors.Fatal_UnexpectedNumberOfUniverse [
             text "Expected and generalized universes in effect declaration for"
                ^/^ doc_of_string (string_of_lid ed.mname) ^/^ text "are different";
             text "Expected" ^/^ pp #int (List.length ed_univs) ^/^
             text "but found" ^/^ pp #int (List.length us)
           ]
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
      signature     = U.apply_eff_sig op ed.signature;
      combinators   = U.apply_eff_combinators op ed.combinators;
      actions       = List.map (fun a ->
        { a with action_defn = snd (op (a.action_univs, a.action_defn));
                 action_typ  = snd (op (a.action_univs, a.action_typ)) }) ed.actions;
    } in

  if !dbg then
    BU.print1 "After typechecking binders eff_decl: \n\t%s\n" (show ed);

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
        raise_error t Errors.Fatal_MismatchUniversePolymorphic error
    end;
    match us with
    | [] -> g_us, t
    | _ ->
     if List.length us = List.length g_us &&
        List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) us g_us
     then g_us, t
     else raise_error t Errors.Fatal_UnexpectedNumberOfUniverse
            (BU.format4 "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
               (string_of_lid ed.mname) comb (BU.string_of_int (List.length us)) (BU.string_of_int (List.length g_us)))
  in

  let signature = check_and_gen' "signature" 1 None (U.effect_sig_ts ed.signature) None in

  if !dbg then
    BU.print1 "Typechecked signature: %s\n" (Print.tscheme_to_string signature);

  (*
   * AR: return a fresh (in the sense of fresh universe) instance of a:Type and wp sort (closed with the returned a) 
   *)
  let fresh_a_and_wp () =
    let fail t = Err.unexpected_signature_for_monad env (ed.signature |> U.effect_sig_ts |> snd).pos ed.mname t in
    //instantiate with fresh universes
    let _, signature = Env.inst_tscheme signature in
    match (SS.compress signature).n with
    | Tm_arrow {bs} ->
      let bs = SS.open_binders bs in
      (match bs with
       | [({binder_bv=a}); ({binder_bv=wp})] -> a, wp.sort
       | _ -> fail signature)
    | _ -> fail signature
  in

  let log_combinator s ts =
    if !dbg then
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

    check_and_gen' "bind_wp" 2 None (ed |> U.get_bind_vc_combinator |> fst) (Some k) in

  log_combinator "bind_wp" bind_wp;

  let stronger =
    let a, wp_sort_a = fresh_a_and_wp () in
    let t, _ = U.type_u() in
    let k = U.arrow [
      S.mk_binder a;
      S.null_binder wp_sort_a;
      S.null_binder wp_sort_a ] (S.mk_Total t) in
    check_and_gen' "stronger" 1 None (ed |> U.get_stronger_vc_combinator |> fst) (Some k) in

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
        mk (Tm_app {hd=repr;args=[t |> as_arg; wp |> as_arg]}) Range.dummyRange in
      let mk_repr a wp = mk_repr' (S.bv_to_name a) wp in
      let destruct_repr t =
        match (SS.compress t).n with
        | Tm_app {args=[(t, _); (wp, _)]} -> t, wp
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
          if BU.for_some (TEQ.eq_tm_bool env U.dm4f_bind_range_attr) ed.eff_attrs
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
        let env = {env with admit = true} |> Some in //we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
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
            | Tm_arrow {bs; comp=c} ->
              let c = Env.comp_to_comp_typ env c in
              if lid_equals c.effect_name ed.mname
              then U.arrow bs (S.mk_Total (mk_repr' c.result_typ (fst (List.hd c.effect_args))))
              else act.action_typ
            | _ -> act.action_typ
          in

          let act_typ, _, g_t = tc_tot_or_gtot_term env act_typ in

          // 1) Check action definition, setting its expected type to
          //    [action_typ]
          let env' = { Env.set_expected_typ env act_typ with instantiate_imp = false } in
          if !dbg then
            BU.print3 "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
              (string_of_lid act.action_name) (show act.action_defn)
              (show act_typ);
          let act_defn, _, g_a = tc_tot_or_gtot_term env' act.action_defn in

          Rel.force_trivial_guard env (Env.conj_guards [g_a; g_t]);

          let act_defn = N.normalize [ Env.UnfoldUntil S.delta_constant ] env act_defn in
          let act_typ = N.normalize [ Env.UnfoldUntil S.delta_constant; Env.Eager_unfolding; Env.Beta ] env act_typ in
          // 2) This implies that [action_typ] has Type(k): good for us!

          // 3) Unify [action_typ] against [expected_k], because we also need
          // to check that the action typ is of the form [binders -> repr ...]
          let expected_k, g_k =
            let act_typ = SS.compress act_typ in
            match act_typ.n with
            | Tm_arrow {bs; comp=c} ->
              let bs, _ = SS.open_comp bs c in
              let res = mk_repr' S.tun S.tun in
              let k = U.arrow bs (S.mk_Total res) in
              let k, _, g = tc_tot_or_gtot_term env k in
              k, g
            | _ -> raise_error act_defn Errors.Fatal_ActionMustHaveFunctionType
                     (BU.format2 "Actions must have function types (not: %s, a.k.a. %s)" (show act_typ) (tag_of act_typ))
          in

          // The following Rel query is only to check that act_typ has
          //   the right shape, no actual typechecking going on here
          (let g = Rel.teq env act_typ expected_k in
           let g = Env.conj_guard g g_k in
           match g.guard_f with
           | NonTrivial _ ->
             raise_error act_defn Errors.Fatal_ActionMustHaveFunctionType
                          (BU.format1 "Unexpected non trivial guard formula when checking action type shape (%s)"
                            (show act_typ))
           | Trivial ->
             Rel.force_trivial_guard {env with admit=true} (Env.conj_guards [g_k; g]));

          // 4) Do a bunch of plumbing to assign a type in the new monad to
          //    the action
          let act_typ = match (SS.compress expected_k).n with
              | Tm_arrow {bs; comp=c} ->
                let bs, c = SS.open_comp bs c in
                let a, wp = destruct_repr (U.comp_result c) in
                let c = {
                  comp_univs=[env.universe_of (Env.push_binders env bs) a];
                  effect_name = ed.mname;
                  result_typ = a;
                  effect_args = [as_arg wp];
                  flags = []
                } in
                U.arrow bs (S.mk_Comp c)
              | _ -> failwith "Impossible (expected_k is an arrow)" in

          (* printfn "Checked action %s against type %s\n" *)
          (*         (show act_defn) *)
          (*         (show (N.normalize [Env.Beta] env act_typ)); *)

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
    signature     = WP_eff_sig (cl signature);
    combinators   = combinators;
    actions       =
      List.map (fun a ->
        { a with
          action_typ  = cl (a.action_univs, a.action_typ) |> snd;
          action_defn = cl (a.action_univs, a.action_defn) |> snd }) actions } in

  if !dbg then
    BU.print1 "Typechecked effect declaration:\n\t%s\n" (show ed);

  ed
)

let tc_eff_decl env ed quals attrs =
  if ed |> U.is_layered
  then tc_layered_eff_decl env ed quals attrs
  else tc_non_layered_eff_decl env ed quals attrs

let monad_signature env m s =
 let fail () = Err.unexpected_signature_for_monad env (range_of_lid m) m s in
 let s = SS.compress s in
 match s.n with
  | Tm_arrow {bs; comp=c} ->
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
  if !dbg_LayeredEffectsTc then
    BU.print1 "Typechecking sub_effect: %s\n" (show sub);

  let lift_ts = sub.lift |> must in
  let r = (lift_ts |> snd).pos in

  let us, lift, lift_ty = check_and_gen env0 "" "lift" 1 lift_ts in

  if !dbg_LayeredEffectsTc then
    BU.print2 "Typechecked lift: %s and lift_ty: %s\n"
      (Print.tscheme_to_string (us, lift)) (Print.tscheme_to_string ((us, lift_ty)));

  let us, lift_ty = SS.open_univ_vars us lift_ty in
  let env = Env.push_univ_vars env0 us in

  let k, kind = validate_indexed_effect_lift_shape env sub.source sub.target (List.hd us) lift_ty r in

  let sub = { sub with
    lift = Some (us, lift);
    lift_wp = Some (us, k |> SS.close_univ_vars us);
    kind = Some kind } in

  if !dbg_LayeredEffectsTc then
    BU.print1 "Final sub_effect: %s\n" (show sub);

  sub

let check_lift_for_erasable_effects env (m1:lident) (m2:lident) (r:Range.range) : unit =
  let err reason = raise_error r Errors.Fatal_UnexpectedEffect
                                (BU.format3 "Error defining a lift/subcomp %s ~> %s: %s"
                                  (string_of_lid m1) (string_of_lid m2) reason) in

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
  if lid_equals sub.source sub.target
  then raise_error r Fatal_UnexpectedEffect
                    (BU.format1
                      "Cannot define a lift with same source and target (%s)"
                      (show sub.source));

  let check_and_gen env t k =
    // BU.print1 "\x1b[01;36mcheck and gen \x1b[00m%s\n" (show t);
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
      then raise_error env Errors.Fatal_EffectCannotBeReified (BU.format1 "Effect %s cannot be reified" (string_of_lid eff_name));
      match Env.effect_decl_opt env eff_name with
      | None -> failwith "internal error: reifiable effect has no decl?"
      | Some (ed, qualifiers) ->
        let repr = Env.inst_effect_fun_with [U_unknown] env ed (ed |> U.get_eff_repr |> must) in
        mk (Tm_app {hd=repr; args=[as_arg a; as_arg wp]}) (Env.get_range env)
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
        if !dbg
        then BU.print1 "Lift for free : %s\n" (show lift);
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
    let env = {env with admit=true} in
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
        let lift_wp_a = mk (Tm_app {hd=lift_wp;args=[as_arg a_typ; as_arg wp_a_typ]}) (Env.get_range env) in
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
      raise_error r Errors.Fatal_TooManyUniverse
        (BU.format3 "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                    (show sub.source) (show sub.target)
                    (lift_wp |> fst |> List.length |> string_of_int));
    if is_some lift && lift |> must |> fst |> List.length <> 1 then
      raise_error r Errors.Fatal_TooManyUniverse
        (BU.format3 "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                    (show sub.source) (show sub.target)
                    (lift |> must |> fst |> List.length |> string_of_int));
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
  //
  //Check if this effect is marked as a default effect in the effect decl.
  //  of its unfolded effect
  //If so, we need to check that it has only a type argument
  //
  let is_default_effect =
    match c |> U.comp_effect_name |> Env.get_default_effect env with
    | None -> false
    | Some l -> lid_equals l lid in
  Rel.force_trivial_guard env g;
  let _ =
    let expected_result_typ =
      match tps with
      | ({binder_bv=x})::tl ->
        if is_default_effect && not (tl = [])
        then raise_error r Errors.Fatal_UnexpectedEffect
                          (BU.format2 "Effect %s is marked as a default effect for %s, but it has more than one arguments"
                            (string_of_lid lid)
                            (c |> U.comp_effect_name |> string_of_lid));
        S.bv_to_name x
      | _ -> raise_error r Errors.Fatal_NotEnoughArgumentsForEffect
                         "Effect abbreviations must bind at least the result type"
    in
    let def_result_typ = FStarC.Syntax.Util.comp_result c in
    if not (Rel.teq_nosmt_force env expected_result_typ def_result_typ)
    then raise_error r Errors.Fatal_EffectAbbreviationResultTypeMismatch
                      (BU.format2 "Result type of effect abbreviation `%s` \
                                  does not match the result type of its definition `%s`"
                                  (show expected_result_typ)
                                  (show def_result_typ))
  in
  let tps = SS.close_binders tps in
  let c = SS.close_comp tps c in
  let uvs, t = Gen.generalize_universes env0 (mk (Tm_arrow {bs=tps; comp=c}) r) in
  let tps, c = match tps, (SS.compress t).n with
    | [], Tm_arrow {comp=c} -> [], c
    | _,  Tm_arrow {bs=tps; comp=c} -> tps, c
    | _ -> failwith "Impossible (t is an arrow)" in
  if List.length uvs <> 1
  then begin
    let _, t = Subst.open_univ_vars uvs t in
    raise_error r Errors.Fatal_TooManyUniverse
                 (BU.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                  (show lid)
                                  (show (List.length uvs))
                                  (show t))
  end;
  (lid, uvs, tps, c)


let check_polymonadic_bind_for_erasable_effects env (m:lident) (n:lident) (p:lident) (r:Range.range) =
  let err reason = raise_error r Errors.Fatal_UnexpectedEffect
                                (BU.format4 "Error definition polymonadic bind (%s, %s) |> %s: %s"
                                  (show m) (show n) (show p) reason) in

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

let tc_polymonadic_bind env (m:lident) (n:lident) (p:lident) (ts:S.tscheme)
  : (S.tscheme & S.tscheme & S.indexed_effect_combinator_kind) =

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

  let m_ed, n_ed, p_ed = Env.get_effect_decl env m, Env.get_effect_decl env n, Env.get_effect_decl env p in

  let k, kind = validate_indexed_effect_bind_shape env m n p
    (U.effect_sig_ts m_ed.signature)
    (U.effect_sig_ts n_ed.signature)
    (U.effect_sig_ts p_ed.signature)
    (U.get_eff_repr m_ed) (U.get_eff_repr n_ed) (U.get_eff_repr p_ed)
    us
    ty
    (Env.get_range env)
    0
    false in

  if Debug.extreme ()
  then BU.print3 "Polymonadic bind %s after typechecking (%s::%s)\n"
         eff_name (Print.tscheme_to_string (us, t))
                  (Print.tscheme_to_string (us, k));

  log_issue r Errors.Warning_BleedingEdge_Feature [Errors.text <|
      BU.format1 "Polymonadic binds (%s in this case) is an experimental feature;\
        it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
        eff_name
  ];

  (us, t), (us, k |> SS.close_univ_vars us), kind


let tc_polymonadic_subcomp env0 (m:lident) (n:lident) (ts:S.tscheme) =
  let r = (snd ts).pos in

  check_lift_for_erasable_effects env0 m n r;

  let combinator_name =
    (m |> ident_of_lid |> string_of_id) ^ " <: " ^
    (n |> ident_of_lid |> string_of_id) in

  let us, t, ty = check_and_gen env0 combinator_name "polymonadic_subcomp" 1 ts in

  //make sure that the combinator has the right shape

  let us, ty = SS.open_univ_vars us ty in
  let env = Env.push_univ_vars env0 us in

  let m_ed, n_ed = Env.get_effect_decl env m, Env.get_effect_decl env n in

  let k, kind = validate_indexed_effect_subcomp_shape env m n
    (U.effect_sig_ts m_ed.signature)
    (U.effect_sig_ts n_ed.signature)
    (U.get_eff_repr m_ed) (U.get_eff_repr n_ed)
    (List.hd us)
    ty
    0
    (Env.get_range env) in

  if Debug.extreme ()
  then BU.print3 "Polymonadic subcomp %s after typechecking (%s::%s)\n"
         combinator_name
         (Print.tscheme_to_string (us, t))
         (Print.tscheme_to_string (us, k));

  log_issue r Errors.Warning_BleedingEdge_Feature [
    Errors.text <|
      BU.format1 "Polymonadic subcomp (%s in this case) is an experimental feature;\
        it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
        combinator_name
  ];

  (us, t), (us, k |> SS.close_univ_vars us), kind
