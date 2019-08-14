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
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Errors
open FStar.TypeChecker
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.TcTerm

module S  = FStar.Syntax.Syntax
module SP  = FStar.Syntax.Print
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcComm = FStar.TypeChecker.Common
module TcUtil = FStar.TypeChecker.Util
module BU = FStar.Util //basic util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print
module TcInductive = FStar.TypeChecker.TcInductive
module PC = FStar.Parser.Const
module EMB = FStar.Syntax.Embeddings
module ToSyntax = FStar.ToSyntax.ToSyntax

//set the name of the query so that we can correlate hints to source program fragments
let set_hint_correlator env se =
    //if the tbl has a counter for lid, we use that, else we start from 0
    //this is useful when we verify the extracted interface alongside
    let tbl = env.qtbl_name_and_index |> fst in
    let get_n lid =
      let n_opt = BU.smap_try_find tbl lid.str in
      if is_some n_opt then n_opt |> must else 0
    in

    match Options.reuse_hint_for () with
    | Some l ->
      let lid = Ident.lid_add_suffix (Env.current_module env) l in
      {env with qtbl_name_and_index=tbl, Some (lid, get_n lid)}

    | None ->
      let lids = U.lids_of_sigelt se in
      let lid = match lids with
            | [] -> Ident.lid_add_suffix (Env.current_module env)
                                         (Ident.next_id () |> BU.string_of_int)
            | l::_ -> l in
      {env with qtbl_name_and_index=tbl, Some (lid, get_n lid)}

let log env = (Options.log_types()) &&  not(lid_equals PC.prims_lid (Env.current_module env))


(*****************Type-checking the signature of a module*****************************)

let tc_check_trivial_guard env t k =
  let t, c, g = tc_check_tot_or_gtot_term env t k in
  Rel.force_trivial_guard env g;
  t

let check_and_gen env t k =
    // BU.print1 "\x1b[01;36mcheck and gen \x1b[00m%s\n" (Print.term_to_string t);
    TcUtil.generalize_universes env (tc_check_trivial_guard env t k)

let check_nogen env t k =
    let t = tc_check_trivial_guard env t k in
    [], N.normalize [Env.Beta] env t

let monad_signature env m s =
 let fail () = raise_error (Err.unexpected_signature_for_monad env m s) (range_of_lid m) in
 let s = SS.compress s in
 match s.n with
  | Tm_arrow(bs, c) ->
    let bs = SS.open_binders bs in
    begin match bs with
        | [(a, _);(wp, _)] -> a, wp.sort
        | _ -> fail()
    end
  | _ -> fail()

let tc_layered_eff_decl env0 (ed:eff_decl) : eff_decl =
  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "Typechecking layered effect: \n\t%s\n" (Print.eff_decl_to_string false ed);

  if List.length ed.univs <> 0 || List.length ed.binders <> 0 then
    raise_error
      (Errors.Fatal_UnexpectedEffect, "Binders are not supported for layered effects (" ^ ed.mname.str ^")")
      (range_of_lid ed.mname);

  let check_and_gen' (comb:string) (n:int) env_opt (us, t) : (univ_names * term * typ) =
    let env = if is_some env_opt then env_opt |> must else env0 in
    let us, t = SS.open_univ_vars us t in
    let t, ty =
      let t, lc, g = tc_tot_or_gtot_term (Env.push_univ_vars env us) t in
      Rel.force_trivial_guard env g;
      t, lc.res_typ in
    let g_us, t = TcUtil.generalize_universes env t in
    let ty = SS.close_univ_vars g_us ty in
    //check that n = List.length g_us and that if us is set, it is same as g_us
    begin
      if List.length g_us <> n then
        let error = BU.format4
          "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
          ed.mname.str comb (string_of_int n) (g_us |> List.length |> string_of_int) in
        raise_error (Errors.Fatal_MismatchUniversePolymorphic, error) t.pos
    end;
    match us with
    | [] -> g_us, t, ty
    | _ ->
     if List.length us = List.length g_us &&
        List.forall2 (fun u1 u2 -> S.order_univ_name u1 u2 = 0) us g_us
     then g_us, t, ty
     else raise_error (Errors.Fatal_UnexpectedNumberOfUniverse,
            (BU.format4 "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
               ed.mname.str comb (BU.string_of_int (List.length us)) (BU.string_of_int (List.length g_us))))
            t.pos
  in

  let log_combinator s (us, t, ty) =
    if Env.debug env0 <| Options.Other "LayeredEffects" then
      BU.print4 "Typechecked %s:%s = %s:%s\n"
        ed.mname.str s
        (Print.tscheme_to_string (us, t)) (Print.tscheme_to_string (us, ty)) in
  
  let fresh_a_and_u_a (a:string) = U.type_u () |> (fun (t, u) -> S.gen_bv a None t |> S.mk_binder, u) in
  let fresh_x_a (x:string) (a:binder) = S.gen_bv x None (a |> fst |> S.bv_to_name) |> S.mk_binder in

  let signature =
    let r = (snd ed.signature).pos in
    let sig_us, sig_t, sig_ty = check_and_gen' "signature" 1 None ed.signature in

    let us, t = SS.open_univ_vars sig_us sig_t in
    let env = Env.push_univ_vars env0 us in

    let a, u = fresh_a_and_u_a "a" in
    let rest_bs = TcUtil.layered_effect_indices_as_binders (sig_us, sig_t) u (a |> fst |> S.bv_to_name) in
    let bs = a::rest_bs in
    let k = U.arrow bs (S.mk_Total S.teff) in
    let g_eq = Rel.teq env t k in
    Rel.force_trivial_guard env g_eq;
    sig_us, SS.close_univ_vars us (N.normalize [Beta] env k), sig_ty in

  log_combinator "signature" signature;

  //AR: TODO: FIXME: check that repr has the type a:Type -> ...is... -> Type
  let repr =
    let r = (snd ed.repr).pos in
    let repr_us, repr_t, repr_ty = check_and_gen' "repr" 1 None ed.repr in
    
    let us, ty = SS.open_univ_vars repr_us repr_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u = fresh_a_and_u_a "a" in
    let rest_bs =
      let signature_ts = let us, t, _ = signature in (us, t) in
      TcUtil.layered_effect_indices_as_binders signature_ts u (a |> fst |> S.bv_to_name) in
    let bs = a::rest_bs in
    let k = U.arrow bs (U.type_u () |> (fun (t, u) -> S.mk_Total' t (Some u))) in
    let g = Rel.teq env ty k in
    Rel.force_trivial_guard env g;
    repr_us, repr_t, SS.close_univ_vars us (N.normalize [Beta] env k) in

  log_combinator "repr" repr;

  let fresh_repr r env u a_tm =
    let signature_ts = let us, t, _ = signature in (us, t) in
    let repr_ts = let us, t, _ = repr in (us, t) in
    TcUtil.fresh_layered_effect_repr env r ed.mname signature_ts repr_ts u a_tm in

  let return_repr =
    let r = (snd ed.return_repr).pos in
    let ret_us, ret_t, ret_ty = check_and_gen' "return_repr" 1 None ed.return_repr in

    let us, ty = SS.open_univ_vars ret_us ret_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u_a = fresh_a_and_u_a "a" in
    let x_a = fresh_x_a "x" a in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 2 ->
        (match SS.open_binders bs with
         | (a', _)::(x_a', _)::bs ->
           let substs = [NT (a', bv_to_name (fst a)); NT (x_a', bv_to_name (fst x_a))] in
           SS.subst_binders substs bs
         | _ -> failwith "Impossible!")
      | _ -> raise_error (Errors.Fatal_UnexpectedEffect, "") r in  //AR: TODO: FIXME
    let bs = a::x_a::rest_bs in
    let repr, g = fresh_repr r (Env.push_binders env bs) u_a (fst a |> S.bv_to_name) in
    let k = U.arrow bs (S.mk_Total' repr (Some u_a)) in
    let g_eq = Rel.teq env ty k in
    Rel.force_trivial_guard env (Env.conj_guard g g_eq);
    ret_us, ret_t, SS.close_univ_vars us (N.normalize [Beta] env k) in

  log_combinator "return_repr" return_repr;

  let bind_repr =
    let r = (snd ed.bind_repr).pos in
    let bind_us, bind_t, bind_ty = check_and_gen' "bind_repr" 2 None ed.bind_repr in

    let us, ty = SS.open_univ_vars bind_us bind_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u_a = fresh_a_and_u_a "a" in
    let b, u_b = fresh_a_and_u_a "b" in
    let rest_bs =
      match (SS.compress ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 4 ->
        (match SS.open_binders bs with
         | (a', _)::(b', _)::bs ->
           let bs, _ = List.splitAt (List.length bs - 2) bs in
           let substs = [NT (a', bv_to_name (fst a)); NT (b', bv_to_name (fst b))] in
           SS.subst_binders substs bs
         | _ -> failwith "Impossible!")
      | _ -> raise_error (Errors.Fatal_UnexpectedEffect, "") r in  //AR: TODO: FIXME
    let bs = a::b::rest_bs in
    let f, g_f =
      let repr, g = fresh_repr r (Env.push_binders env bs) u_a (fst a |> S.bv_to_name) in
      S.gen_bv "f" None repr |> S.mk_binder, g in
    let g, g_g =
      let x_a = fresh_x_a "x" a in
      let repr, g = fresh_repr r (Env.push_binders env (bs@[x_a])) u_b (fst b |> S.bv_to_name) in
      S.gen_bv "g" None (U.arrow [x_a] (S.mk_Total' repr (Some u_b))) |> S.mk_binder, g in
    let repr, g_repr = fresh_repr r (Env.push_binders env bs) u_b (fst b |> S.bv_to_name) in
    let k = U.arrow (bs@[f; g]) (S.mk_Total' repr (Some u_b)) in
    let g_eq = Rel.teq env ty k in
    List.iter (Rel.force_trivial_guard env) [g_f; g_g; g_repr; g_eq];
    bind_us, bind_t, SS.close_univ_vars bind_us (N.normalize [Beta] env k) in

  log_combinator "bind_repr" bind_repr;

  let stronger_repr =
    let stronger_repr = ed.stronger_repr |> must in
    let r = (snd stronger_repr).pos in

    let stronger_us, stronger_t, stronger_ty = check_and_gen' "stronger_repr" 1 None stronger_repr in

    if Env.debug env0 <| Options.Other "LayeredEffects" then
      BU.print2 "stronger combinator typechecked with term: %s and type: %s\n"
        (Print.tscheme_to_string (stronger_us, stronger_t))
        (Print.tscheme_to_string (stronger_us, stronger_ty));

    let us, ty = SS.open_univ_vars stronger_us stronger_ty in
    let env = Env.push_univ_vars env0 us in

    let a, u = fresh_a_and_u_a "a" in
    let f_is_bs =
      let signature_ts = let us, t, _ = signature in (us, t) in
      TcUtil.layered_effect_indices_as_binders signature_ts u (a |> fst |> S.bv_to_name) in
    let g_is_bs =
      let signature_ts = let us, t, _ = signature in (us, t) in
      TcUtil.layered_effect_indices_as_binders signature_ts u (a |> fst |> S.bv_to_name) in
    let f_b =
      let repr_ts = let (us, t, _) = repr in (us, t) in
      let _, repr = Env.inst_tscheme_with repr_ts [u] in
      let repr = S.mk_Tm_app
        repr
        ((a::f_is_bs) |> List.map fst |> List.map S.bv_to_name |> List.map S.as_arg)
        None r in
      S.gen_bv "f" None repr |> S.mk_binder in
    let ret_t =
      let repr_ts = let (us, t, _) = repr in (us, t) in
      let _, repr = Env.inst_tscheme_with repr_ts [u] in
      S.mk_Tm_app
        repr
        ((a::g_is_bs) |> List.map fst |> List.map S.bv_to_name |> List.map S.as_arg)
        None r in
    let pure_wp_t =
      let pure_wp_ts = Env.lookup_definition [NoDelta] env PC.pure_wp_lid |> must in
      let _, pure_wp_t = Env.inst_tscheme pure_wp_ts in
      S.mk_Tm_app
        pure_wp_t
        [ret_t |> S.as_arg]
        None r in

    let pure_wp_uvar, _, g_pure_wp_uvar =
      TcUtil.new_implicit_var "" r (Env.push_binders env (a::(f_is_bs@g_is_bs))) pure_wp_t in
    let c = S.mk_Comp ({
      comp_univs = [ Env.new_u_univ () ];  //AR: TODO: FIXME: not sure if this is getting resolved properly
      effect_name = PC.effect_PURE_lid;
      result_typ = ret_t;
      effect_args = [ pure_wp_uvar |> S.as_arg ];
      flags = [] }) in

    let k = U.arrow (a::(f_is_bs@g_is_bs@[f_b])) c in

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Expected type before unification: %s\n"
        (Print.term_to_string k);

    let g = Rel.teq env ty k in
    Rel.force_trivial_guard env (Env.conj_guard g_pure_wp_uvar g);
    let k = N.remove_uvar_solutions env k in  //AR: TODO: FIXME: do this for other combinators too
    stronger_us, stronger_t, SS.close_univ_vars stronger_us k in

  log_combinator "stronger_repr" stronger_repr;

  //AR: TODO: FIXME: rest of the combinators

  let tc_action env (act:action) : action =
    let r = act.action_defn.pos in
    if List.length act.action_params <> 0
    then failwith "tc_layered_eff_decl: expected action_params to be empty";

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
          let c =
            (S.mk_Tm_app
              repr
              (S.as_arg ct.result_typ::ct.effect_args)
              None r)
            |> S.mk_Total in
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
      | Tm_arrow (bs, c) ->
        let bs = SS.open_binders bs in
        let env = Env.push_binders env bs in
        let t, u = U.type_u () in
        let a_tm, _, g_tm = TcUtil.new_implicit_var "" r env t in
        let repr, g = fresh_repr r env u a_tm in
        U.arrow bs (S.mk_Total' repr (Env.new_u_univ () |> Some)), Env.conj_guard g g_tm
      | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType, "") r in  //AR: TODO: FIXME: ""

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Expected action type: %s\n" (Print.term_to_string k);

    let g = Rel.teq env act_typ k in
    List.iter (Rel.force_trivial_guard env) [g_t; g_d; g_k; g];

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Expected action type after unification: %s\n" (Print.term_to_string k);
    
    let act_typ =
      let repr_args t : universes * term * args =
        match (SS.compress t).n with
        | Tm_app (head, a::is) ->
          (match (SS.compress head).n with
           | Tm_uinst (_, us) -> us, fst a, is
           | _ -> failwith "Impossible!")
        | _ -> failwith "Impossible!" in

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
      | _ -> failwith "Impossible!" in

    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Action type after injecting it into the monad: %s\n" (Print.term_to_string act_typ);
    
    let act =
      if act.action_univs = []
      then
        let us, act_defn = TcUtil.generalize_universes env act_defn in
        { act with
          action_univs = us;
          action_defn = act_defn;
          action_typ = SS.close_univ_vars us act_typ }
      else
        { act with
          action_defn = SS.close_univ_vars act.action_univs act_defn;
          action_typ = SS.close_univ_vars act.action_univs act_typ } in

    act in

  let fst (a, _, _) = a in
  let snd (_, b, _) = b in
  let thd (_, _, c) = c in

  { ed with
    signature     = (fst signature, snd signature);
    ret_wp        = (fst return_repr, thd return_repr);
    bind_wp       = (fst bind_repr, thd bind_repr);
    stronger      = (fst stronger_repr, thd stronger_repr);
    repr          = (fst repr, snd repr);
    return_repr   = (fst return_repr, snd return_repr);
    bind_repr     = (fst bind_repr, snd bind_repr);
    stronger_repr = (fst stronger_repr, snd stronger_repr) |> Some;
    actions       = List.map (tc_action env0) ed.actions }

let tc_layered_lift env0 (sub:sub_eff) : sub_eff =
  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "Typechecking sub_effect: %s\n" (Print.sub_eff_to_string sub);

  let us, lift = sub.lift |> must in
  let r = lift.pos in

  if List.length us <> 0  //TODO: FIXME: this breaks use_extracted_flags, see ulib/Makefile.verify
  then failwith ("Unexpected number of universes in typechecking %s" ^ (Print.sub_eff_to_string sub));

  let lift, lc, g = tc_tot_or_gtot_term env0 lift in
  Rel.force_trivial_guard env0 g;

  let lift_ty = lc.res_typ |> N.normalize [Beta] env0 in

  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print2 "Typechecked lift: %s and lift_ty: %s\n"
      (Print.term_to_string lift) (Print.term_to_string lift_ty);

  let k, g_k =
    let a, u_a = U.type_u () |> (fun (t, u) -> S.gen_bv "a" None t |> S.mk_binder, u) in
    
    let a', wp_sort_a' = monad_signature env0 sub.source (Env.lookup_effect_lid env0 sub.source) in
    let src_wp_sort_a = SS.subst [NT (a', a |> fst |> S.bv_to_name)] wp_sort_a' in

    let wp = S.gen_bv "wp" None src_wp_sort_a |> S.mk_binder in

    let rest_bs =
      match (SS.compress lift_ty).n with
      | Tm_arrow (bs, _) when List.length bs >= 3 ->
        (match SS.open_binders bs with
         | (a', _)::(wp', _)::bs ->
           let bs, _ = List.splitAt (List.length bs - 1) bs in
           let substs = [NT (a', bv_to_name (fst a)); NT (wp', bv_to_name (fst wp))] in
           SS.subst_binders substs bs
         | _ -> failwith "Impossible!")
      | _ -> raise_error (Errors.Fatal_UnexpectedEffect, "") r in  //AR: TODO: FIXME
        
    let f =
      let f_sort = U.arrow
        [S.null_binder S.t_unit]
        (S.mk_Comp ({
          comp_univs = [u_a];  //AR: TODO: FIXME: this is wrong, this should be the universe of sub.source not that of a
          effect_name = sub.source;
          result_typ = a |> fst |> S.bv_to_name;
          effect_args = [wp |> fst |> S.bv_to_name |> S.as_arg];
          flags = []
        })) in
      S.gen_bv "f" None f_sort |> S.mk_binder in
     
    let bs = a::wp::(rest_bs@[f]) in

    let repr, g_repr = TcUtil.fresh_layered_effect_repr_en
      (Env.push_binders env0 bs)
      r sub.target u_a (a |> fst |> S.bv_to_name) in
    
    U.arrow bs (mk_Total' repr (new_u_univ () |> Some)), g_repr in

   if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "Before unification k: %s\n" (Print.term_to_string k);

  let g = Rel.teq env0 lift_ty k in
  Rel.force_trivial_guard env0 g_k; Rel.force_trivial_guard env0 g;

  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "After unification k: %s\n" (Print.term_to_string k);
  
  let us, lift = TcUtil.generalize_universes env0 lift in
  let lift_wp = k |> N.remove_uvar_solutions (Env.push_univ_vars env0 us) |> SS.close_univ_vars us in
  //AR: TODO: FIXME: do this remove uvar solutions other places too?
  //AR: TODO: FIXME: check that List.length us = 1

  let sub = { sub with
    lift = Some (us, lift);
    lift_wp = Some (us, lift_wp) } in

  if Env.debug env0 <| Options.Other "LayeredEffects" then
    BU.print1 "Final sub_effect: %s\n" (Print.sub_eff_to_string sub);

  sub
  

let tc_eff_decl env0 (ed:S.eff_decl) : eff_decl =
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
      ret_wp        =op ed.ret_wp;
      bind_wp       =op ed.bind_wp;
      stronger      =op ed.stronger;
      match_wps     = U.map_match_wps op ed.match_wps;
      trivial       = map_opt ed.trivial op;
      repr          =op ed.repr;
      return_repr   =op ed.return_repr;
      bind_repr     =op ed.bind_repr;
      stronger_repr = None;
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
    check_and_gen' "ret_wp" 1 None ed.ret_wp (Some k) in

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

    check_and_gen' "bind_wp" 2 None ed.bind_wp (Some k) in

  log_combinator "bind_wp" bind_wp;

  let stronger =
    let a, wp_sort_a = fresh_a_and_wp () in
    let t, _ = U.type_u() in
    let k = U.arrow [
      S.mk_binder a;
      S.null_binder wp_sort_a;
      S.null_binder wp_sort_a ] (S.mk_Total t) in
    check_and_gen' "stronger" 1 None ed.stronger (Some k) in

  log_combinator "stronger" stronger;

  let match_wps =
    let if_then_else, ite_wp, close_wp = U.get_match_with_close_wps ed.match_wps in

    let if_then_else =
      let a, wp_sort_a = fresh_a_and_wp () in
      let p = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
      let k = U.arrow [
        S.mk_binder a;
        S.mk_binder p;
        S.null_binder wp_sort_a;
        S.null_binder wp_sort_a ] (S.mk_Total wp_sort_a) in

      check_and_gen' "if_then_else" 1 None if_then_else (Some k) in

    log_combinator "if_then_else" if_then_else;

    let ite_wp =
      let a, wp_sort_a = fresh_a_and_wp () in
      let k = U.arrow [S.mk_binder a; S.null_binder wp_sort_a] (S.mk_Total wp_sort_a) in
      check_and_gen' "ite_wp" 1 None ite_wp (Some k) in

    log_combinator "ite_wp" ite_wp;

    let close_wp =
      let a, wp_sort_a = fresh_a_and_wp () in
      let b = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
      let wp_sort_b_a = U.arrow [S.null_binder (S.bv_to_name b)] (S.mk_Total wp_sort_a) in

      let k = U.arrow [S.mk_binder a; S.mk_binder b; S.null_binder wp_sort_b_a] (S.mk_Total wp_sort_a) in
      check_and_gen' "close_wp" 2 None close_wp (Some k) in

    log_combinator "close_wp" close_wp;

    Inl ({ if_then_else = if_then_else; ite_wp = ite_wp; close_wp = close_wp }) in

  let trivial =
    let a, wp_sort_a = fresh_a_and_wp () in
    let t, _ = U.type_u () in
    let k = U.arrow [S.mk_binder a; S.null_binder wp_sort_a] (S.mk_GTotal t) in
    let trivial = check_and_gen' "trivial" 1 None (ed.trivial |> must) (Some k) in

    log_combinator "trivial" trivial;

    Some trivial in

  let repr, return_repr, bind_repr, actions =
    match (SS.compress (snd ed.repr)).n with
    | Tm_unknown -> ed.repr, ed.return_repr, ed.bind_repr, ed.actions
    | _ ->
      let repr =
        let a, wp_sort_a = fresh_a_and_wp () in
        let t, _ = U.type_u () in
        let k = U.arrow [S.mk_binder a; S.null_binder wp_sort_a] (S.mk_GTotal t) in
        check_and_gen' "repr" 1 None ed.repr (Some k) in

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
        let a, _ = fresh_a_and_wp () in
        let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
        let res =
          let wp = mk_Tm_app
            (Env.inst_tscheme ret_wp |> snd)
            [S.bv_to_name a |> S.as_arg; S.bv_to_name x_a |> S.as_arg] None Range.dummyRange in
          mk_repr a wp in
        let k = U.arrow [S.mk_binder a; S.mk_binder x_a] (S.mk_Total res) in
        let k, _, _ = tc_tot_or_gtot_term env k in
        let env = Some (Env.set_range env (snd (ed.return_repr)).pos) in
        check_and_gen' "return_repr" 1 env ed.return_repr (Some k) in
    
      log_combinator "return_repr" return_repr;

      let bind_repr =
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
        let env = Env.set_range env (snd (ed.bind_repr)).pos in
        let env = {env with lax=true} |> Some in //we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
        check_and_gen' "bind_repr" 2 env ed.bind_repr (Some k) in

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
              let c = comp_to_comp_typ c in
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

      repr, return_repr, bind_repr, actions
  in

  //close the ed_univs and ed_bs
  let cl ts =
    let ts = SS.close_tscheme ed_bs ts in
    let ed_univs_closing = SS.univ_var_closing ed_univs in
    SS.subst_tscheme (SS.shift_subst (List.length ed_bs) ed_univs_closing) ts in
  
  //univs and binders have already been set
  let ed = { ed with
    signature     =cl signature;
    ret_wp        =cl ret_wp;
    bind_wp       =cl bind_wp;
    stronger      =cl stronger;
    match_wps     = U.map_match_wps cl match_wps;
    trivial       = map_opt trivial cl;
    repr          =cl repr;
    return_repr   =cl return_repr;
    bind_repr     =cl bind_repr;
    stronger_repr = None;
    actions       =
      List.map (fun a ->
        { a with
          action_typ  = cl (a.action_univs, a.action_typ) |> snd;
          action_defn = cl (a.action_univs, a.action_defn) |> snd }) actions } in

  if Env.debug env <| Options.Other "ED" then
    BU.print1 "Typechecked effect declaration:\n\t%s\n" (Print.eff_decl_to_string false ed);

  ed

let tc_lex_t env ses quals lids =
    (* We specifically type lex_t as:

          type lex_t<u> : Type(u) =
          datacon LexTop<utop>  : lex_t<utop>
          datacon LexCons<ucons1, ucons2> : #a:Type(ucons1) -> hd:a -> tl:lex_t<ucons2> -> lex_t<max ucons1 ucons2>
    *)
    assert (quals = []);
    let err_range = (List.hd ses).sigrng in
    begin match lids with
        | [lex_t; lex_top; lex_cons] when
            (lid_equals lex_t PC.lex_t_lid
             && lid_equals lex_top PC.lextop_lid
             && lid_equals lex_cons PC.lexcons_lid) -> ()
        | _ -> Errors.raise_error (Errors.Fatal_InvalidRedefinitionOfLexT, ("Invalid (partial) redefinition of lex_t")) err_range
    end;
    begin match ses with
      //AR: we were enforcing the univs to be [], which breaks down when we have two phases
      //    the typechecking of lex_t is anyway hardcoded, so it should be fine to ignore that restriction
      | [{ sigel = Sig_inductive_typ(lex_t, _, [], t, _, _);  sigquals = []; sigrng = r };
         { sigel = Sig_datacon(lex_top, _, _t_top, _lex_t_top, 0, _); sigquals = []; sigrng = r1 };
         { sigel = Sig_datacon(lex_cons, _, _t_cons, _lex_t_cons, 0, _); sigquals = []; sigrng = r2 }]
         when (lid_equals lex_t PC.lex_t_lid
            && lid_equals lex_top PC.lextop_lid
            && lid_equals lex_cons PC.lexcons_lid) ->

        let u = S.new_univ_name (Some r) in
        let t = mk (Tm_type(U_name u)) None r in
        let t = Subst.close_univ_vars [u] t in
        let tc = { sigel = Sig_inductive_typ(lex_t, [u], [], t, [], [PC.lextop_lid; PC.lexcons_lid]);
                   sigquals = [];
                   sigrng = r;
                   sigmeta = default_sigmeta;
                   sigattrs = [] } in

        let utop = S.new_univ_name (Some r1) in
        let lex_top_t = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r1) delta_constant None, [U_name utop])) None r1 in
        let lex_top_t = Subst.close_univ_vars [utop] lex_top_t in
        let dc_lextop = { sigel = Sig_datacon(lex_top, [utop], lex_top_t, PC.lex_t_lid, 0, []);
                          sigquals = [];
                          sigrng = r1;
                          sigmeta = default_sigmeta;
                          sigattrs = []  } in

        let ucons1 = S.new_univ_name (Some r2) in
        let ucons2 = S.new_univ_name (Some r2) in
        let lex_cons_t =
            let a = S.new_bv (Some r2) (mk (Tm_type(U_name ucons1)) None r2) in
            let hd = S.new_bv (Some r2) (S.bv_to_name a) in
            let tl = S.new_bv (Some r2) (mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) delta_constant None, [U_name ucons2])) None r2) in
            let res = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) delta_constant None, [U_max [U_name ucons1; U_name ucons2]])) None r2 in
            U.arrow [(a, Some S.imp_tag); (hd, None); (tl, None)] (S.mk_Total res) in
        let lex_cons_t = Subst.close_univ_vars [ucons1;ucons2]  lex_cons_t in
        let dc_lexcons = { sigel = Sig_datacon(lex_cons, [ucons1;ucons2], lex_cons_t, PC.lex_t_lid, 0, []);
                           sigquals = [];
                           sigrng = r2;
                           sigmeta = default_sigmeta;
                           sigattrs = []  } in
        { sigel = Sig_bundle([tc; dc_lextop; dc_lexcons], lids);
          sigquals = [];
          sigrng = Env.get_range env;
          sigmeta = default_sigmeta;
          sigattrs = []  }
      | _ ->
        let err_msg =
          BU.format1 "Invalid (re)definition of lex_t: %s\n"
            (Print.sigelt_to_string (mk_sigelt (Sig_bundle(ses, lids))))
        in
        raise_error (Errors.Fatal_InvalidRedefinitionOfLexT, err_msg) err_range
    end

let tc_type_common (env:env) ((uvs, t):tscheme) (expected_typ:typ) (r:Range.range) :tscheme =
  let uvs, t = SS.open_univ_vars uvs t in
  let env = Env.push_univ_vars env uvs in
  let t = tc_check_trivial_guard env t expected_typ in
  if uvs = [] then
    let uvs, t = TcUtil.generalize_universes env t in
    //AR: generalize_universes only calls N.reduce_uvar_solutions, so make sure there are no uvars left
    TcUtil.check_uvars r t;
    uvs, t
  else uvs, t |> N.remove_uvar_solutions env |> SS.close_univ_vars uvs

let tc_declare_typ (env:env) (ts:tscheme) (r:Range.range) :tscheme =
  tc_type_common env ts (U.type_u () |> fst) r

let tc_assume (env:env) (ts:tscheme) (r:Range.range) :tscheme =
  //AR: this might seem same as tc_declare_typ but come prop, this will change
  tc_type_common env ts (U.type_u () |> fst) r

let tc_inductive' env ses quals lids =
    if Env.debug env Options.Low then
        BU.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" (FStar.Common.string_of_list Print.sigelt_to_string ses);

    let sig_bndle, tcs, datas = TcInductive.check_inductive_well_typedness env ses quals lids in
    (* we have a well-typed inductive;
            we still need to check whether or not it supports equality
            and whether it is strictly positive
       *)

    (* Once the datacons are generalized we can construct the projectors with the right types *)
    let data_ops_ses = List.map (TcInductive.mk_data_operations quals env tcs) datas |> List.flatten in

    //strict positivity check
    if Options.no_positivity () || (not (Env.should_verify env)) then ()  //skipping positivity check if lax mode
    else begin
       let env = push_sigelt env sig_bndle in
       (* Check positivity of the inductives within the Sig_bundle *)
       List.iter (fun ty ->
         let b = TcInductive.check_positivity ty env in
         if not b then
           let lid, r =
             match ty.sigel with
             | Sig_inductive_typ (lid, _, _, _, _, _) -> lid, ty.sigrng
             | _                                         -> failwith "Impossible!"
           in
           Errors.log_issue r (Errors.Error_InductiveTypeNotSatisfyPositivityCondition, ("Inductive type " ^ lid.str ^ " does not satisfy the positivity condition"))
         else ()
       ) tcs;

       (* Separately, if any of the data constructors in the Sig_bundle are
        * exceptions, check their positivity separately. See issue #1535 *)
       List.iter (fun d ->
         let data_lid, ty_lid =
            match d.sigel with
            | Sig_datacon (data_lid, _, _, ty_lid, _, _) -> data_lid, ty_lid
            | _ -> failwith "Impossible"
         in
         if lid_equals ty_lid PC.exn_lid && not (TcInductive.check_exn_positivity data_lid env) then
            Errors.log_issue d.sigrng
                     (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                        ("Exception " ^ data_lid.str ^ " does not satisfy the positivity condition"))
       ) datas
    end;

    //generate hasEq predicate for this inductive
    //skip logical connectives types in prims, tcs is bound to the inductive type, caller ensures its length is > 0
    let skip_prims_type (_:unit) :bool =
        let lid =
            let ty = List.hd tcs in
            match ty.sigel with
                | Sig_inductive_typ (lid, _, _, _, _, _) -> lid
                | _                                         -> failwith "Impossible"
        in
        //these are the prims type we are skipping
        List.existsb (fun s -> s = lid.ident.idText) TcInductive.early_prims_inductives
    in

    let is_noeq = List.existsb (fun q -> q = Noeq) quals in

    let res =
        if ((List.length tcs = 0) || ((lid_equals env.curmodule PC.prims_lid) && skip_prims_type ()) || is_noeq)
        then sig_bndle, data_ops_ses
        else
            let is_unopteq = List.existsb (fun q -> q = Unopteq) quals in
            let ses =
              if is_unopteq then TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env
              else TcInductive.optimized_haseq_scheme sig_bndle tcs datas env
            in
            sig_bndle, ses@data_ops_ses in  //append hasEq axiom lids and data projectors and discriminators lids
    res

let tc_inductive env ses quals lids =
  let env = Env.push env "tc_inductive" in
  let pop () = ignore (Env.pop env "tc_inductive") in  //OK to ignore: caller will reuse original env
  try tc_inductive' env ses quals lids |> (fun r -> pop (); r)
  with e -> pop (); raise e

let get_fail_se (se:sigelt) : option<(list<int> * bool)> =
    let comb f1 f2 =
        match f1, f2 with
        | Some (e1, l1), Some (e2, l2) ->
            Some (e1@e2, l1 || l2)
        | Some (e, l), None
        | None, Some (e, l) ->
            Some (e, l)
        | _ -> None
    in
    List.fold_right (fun at acc -> comb (ToSyntax.get_fail_attr true at) acc) se.sigattrs None

let list_of_option = function
    | None -> []
    | Some x -> [x]

(* Finds a discrepancy between two multisets of ints. Result is (elem, amount1, amount2) *)
(* Precondition: lists are sorted *)
let check_multi_eq (l1 : list<int>) (l2 : list<int>) : option<(int * int * int)> =
    let rec collect (l : list<'a>) : list<('a * int)> =
        match l with
        | [] -> []
        | hd :: tl ->
            begin match collect tl with
            | [] -> [(hd, 1)]
            | (h, n) :: t ->
                if h = hd
                then (h, n+1) :: t
                else (hd, 1) :: (h, n) :: t
            end
    in
    let summ l =
        collect l
    in
    let l1 = summ l1 in
    let l2 = summ l2 in
    let rec aux l1 l2 =
        match l1, l2 with
        | [], [] -> None

        | (e, n) :: _, [] ->
            Some (e, n, 0)

        | [], (e, n) :: _ ->
            Some (e, 0, n)

        | (hd1, n1) :: tl1, (hd2, n2) :: tl2 ->
            if hd1 < hd2 then
                Some (hd1, n1, 0)
            else if hd1 > hd2 then
                Some (hd2, 0, n2)
            else if n1 <> n2 then
                Some (hd1, n1, n2)
            else aux tl1 tl2
    in
    aux l1 l2

(*
 *  Given `val t : Type` in an interface
 *  and   `let t = e`    in the corresponding implementation
 *  The val declaration should contains the `must_erase_for_extraction` attribute
 *  if and only if `e` is a type that's non-informative (e..g., unit, t -> unit, etc.)
 *)
let check_must_erase_attribute env se =
    match se.sigel with
    | Sig_let(lbs, l) ->
        if not (Options.ide())
        then
        begin
          match DsEnv.iface_decls (Env.dsenv env) (Env.current_module env) with
          | None ->
            ()

          | Some iface_decls ->
            snd lbs |> List.iter (fun lb ->
                let lbname = BU.right lb.lbname in
                let has_iface_val =
                    iface_decls |> BU.for_some (FStar.Parser.AST.decl_is_val lbname.fv_name.v.ident)
                in
                if has_iface_val
                then
                    let must_erase =
                      TcUtil.must_erase_for_extraction env lb.lbdef in
                    let has_attr =
                      Env.fv_has_attr env
                                      lbname
                                      FStar.Parser.Const.must_erase_for_extraction_attr in
                    if must_erase && not has_attr
                    then
                        FStar.Errors.log_issue
                            (range_of_fv lbname)
                            (FStar.Errors.Error_MustEraseMissing,
                                BU.format2
                                    "Values of type `%s` will be erased during extraction, \
                                    but its interface hides this fact. Add the `must_erase_for_extraction` \
                                    attribute to the `val %s` declaration for this symbol in the interface"
                                    (Print.fv_to_string lbname)
                                    (Print.fv_to_string lbname)
                                    )
                    else if has_attr && not must_erase
                    then FStar.Errors.log_issue
                        (range_of_fv lbname)
                        (FStar.Errors.Error_MustEraseMissing,
                            BU.format1
                                "Values of type `%s` cannot be erased during extraction, \
                                but the `must_erase_for_extraction` attribute claims that it can. \
                                Please remove the attribute."
                                (Print.fv_to_string lbname)
                                ))
    end

    | _ -> ()

let tc_decl' env0 se: list<sigelt> * list<sigelt> * Env.env =
  let env = env0 in
  TcUtil.check_sigelt_quals env se;
  let r = se.sigrng in
  match se.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ ->
    failwith "Impossible bare data-constructor"

  | Sig_bundle(ses, lids) when (lids |> BU.for_some (lid_equals PC.lex_t_lid)) ->
    //lex_t is very special; it uses a more expressive form of universe polymorphism than is allowed elsewhere
    //Instead of this special treatment, we could make use of explicit lifts, but LexCons is used pervasively
    (*
        type lex_t<u> =
          | LexTop<u>  : lex_t<u>
          | LexCons<u1, u2> : #a:Type(u1) -> a -> lex_t<u2> -> lex_t<max u1 u2>
    *)
    let env = Env.set_range env r in
    let se = tc_lex_t env ses se.sigquals lids  in
    [se], [], env0

  | Sig_bundle(ses, lids) ->
    let env = Env.set_range env r in
    let ses =
      if Options.use_two_phase_tc () && Env.should_verify env then begin
        //we generate extra sigelts even in the first phase, and then throw them away, would be nice to not generate them at all
        let ses = tc_inductive ({ env with phase1 = true; lax = true }) ses se.sigquals lids |> fst |> N.elim_uvars env |> U.ses_of_sigbundle in
        if Env.debug env <| Options.Other "TwoPhases" then BU.print1 "Inductive after phase 1: %s\n" (Print.sigelt_to_string ({ se with sigel = Sig_bundle (ses, lids) }));
        ses
      end
      else ses
    in
    let sigbndle, projectors_ses = tc_inductive env ses se.sigquals lids in
    let sigbndle = { sigbndle with sigattrs = se.sigattrs } in (* keep the attributes *)
    [ sigbndle ], projectors_ses, env0

  | Sig_pragma(p) ->  //no need for two-phase here
    U.process_pragma p r;
    [se], [], env0

  | Sig_new_effect_for_free (ne) ->  //no need for two-phase here, the elaborated ses are typechecked from the main loop in tc_decls
      (* This is only an elaboration rule not a typechecking one *)

      // Let the power of Dijkstra generate everything "for free", then defer
      // the rest of the job to [tc_decl].
      let ses, ne, lift_from_pure_opt = DMFF.cps_and_elaborate env ne in
      let effect_and_lift_ses = match lift_from_pure_opt with
          | Some lift -> [ { se with sigel = Sig_new_effect (ne) } ; lift ]
          | None -> [ { se with sigel = Sig_new_effect (ne) } ]
      in

      [], ses @ effect_and_lift_ses, env0

  | Sig_new_effect(ne) ->
    if Env.debug env <| Options.Other "LayeredEffects" then
      BU.print1 "Starting to typecheck layered effect:\n%s\n" (Print.sigelt_to_string se);
    let tc_fun = if ne.is_layered then tc_layered_eff_decl else tc_eff_decl in
    let ne =
      if Options.use_two_phase_tc () && Env.should_verify env then begin
        let ne = tc_fun ({ env with phase1 = true; lax = true }) ne |> (fun ne -> { se with sigel = Sig_new_effect ne }) |> N.elim_uvars env |> U.eff_decl_of_new_effect in
        if Env.debug env <| Options.Other "TwoPhases" then BU.print1 "Effect decl after phase 1: %s\n" (Print.sigelt_to_string ({ se with sigel = Sig_new_effect ne }));
        ne
      end
      else ne
    in
    let ne = tc_fun env ne in
    let se = { se with sigel = Sig_new_effect(ne) } in
    [se], [], env0

  | Sig_sub_effect(sub) ->  //no need to two-phase here, since lifts are already lax checked
    let ed_src = Env.get_effect_decl env sub.source in
    let ed_tgt = Env.get_effect_decl env sub.target in

    if ed_src.is_layered || ed_tgt.is_layered
    then
      let sub = tc_layered_lift env0 sub in
      [{ se with sigel = Sig_sub_effect(sub) }], [], env0
    else
      let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
      let b, wp_b_tgt = monad_signature env sub.target (Env.lookup_effect_lid env sub.target) in
      let wp_a_tgt    = SS.subst [NT(b, S.bv_to_name a)] wp_b_tgt in
      let expected_k  = U.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
      let repr_type eff_name a wp =
        if not (is_reifiable_effect env eff_name) then
            raise_error (Errors.Fatal_EffectCannotBeReified, (BU.format1 "Effect %s cannot be reified" eff_name.str)) (Env.get_range env);
        match Env.effect_decl_opt env eff_name with
        | None -> failwith "internal error: reifiable effect has no decl?"
        | Some (ed, qualifiers) ->
          let repr = Env.inst_effect_fun_with [U_unknown] env ed ed.repr in
          mk (Tm_app(repr, [as_arg a; as_arg wp])) None (Env.get_range env)
      in
      let lift, lift_wp =
        match sub.lift, sub.lift_wp with
        | None, None ->
          failwith "Impossible (parser)"
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
            if List.length what > 0 then
              let usubst, uvs = SS.univ_var_opening what in
              uvs, SS.subst usubst lift
            else [], lift
          in
          if Env.debug env (Options.Other "ED") then
              BU.print1 "Lift for free : %s\n" (Print.term_to_string lift) ;
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
//           printfn "LIFT: Expected type for lift = %s\n" (Print.term_to_string expected_k);
        let expected_k, _, _ =
          tc_tot_or_gtot_term env expected_k in
//          printfn "LIFT: Checking %s against expected type %s\n" (Print.term_to_string lift) (Print.term_to_string expected_k);
        let lift =
          if List.length uvs = 0 then check_and_gen env lift expected_k
          else
            let lift = tc_check_trivial_guard env lift expected_k in
            uvs, SS.close_univ_vars uvs lift in
//            printfn "LIFT: Checked %s against expected type %s\n" (Print.tscheme_to_string lift) (Print.term_to_string expected_k);
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
      let sub = {sub with lift_wp=Some lift_wp; lift=lift} in
      let se = { se with sigel = Sig_sub_effect(sub) } in
      [se], [], env0

  | Sig_effect_abbrev(lid, uvs, tps, c, flags) ->
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
    let se = { se with sigel = Sig_effect_abbrev(lid, uvs, tps, c, flags) } in
    [se], [], env0

  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _)
      when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) ->
      (* Dummy declaration which must be erased since it has been elaborated somewhere else *)
      [], [], env0

  | Sig_declare_typ(lid, uvs, t) -> //NS: No checks on the qualifiers?
    let env = Env.set_range env r in

    if lid_exists env lid
    then raise_error (Errors.Fatal_AlreadyDefinedTopLevelDeclaration, (BU.format1 "Top-level declaration %s for a name that is already used in this module; \
                                   top-level declarations must be unique in their module"
                                   (Ident.text_of_lid lid))) r;

    let uvs, t =
      if Options.use_two_phase_tc () && Env.should_verify env then begin
        let uvs, t = tc_declare_typ ({ env with lax = true }) (uvs, t) se.sigrng in //|> N.normalize [Env.NoFullNorm; Env.Beta; Env.DoNotUnfoldPureLets] env in
        if Env.debug env <| Options.Other "TwoPhases" then BU.print2 "Val declaration after phase 1: %s and uvs: %s\n" (Print.term_to_string t) (Print.univ_names_to_string uvs);
        uvs, t
      end
      else uvs, t
    in

    let uvs, t = tc_declare_typ env (uvs, t) se.sigrng in
    [ { se with sigel = Sig_declare_typ (lid, uvs, t) }], [], env0

  | Sig_assume(lid, uvs, t) ->
    let env = Env.set_range env r in

    let uvs, t =
      if Options.use_two_phase_tc () && Env.should_verify env then begin
        let uvs, t = tc_assume ({ env with phase1 = true; lax = true }) (uvs, t) se.sigrng in
        if Env.debug env <| Options.Other "TwoPhases" then BU.print2 "Assume after phase 1: %s and uvs: %s\n" (Print.term_to_string t) (Print.univ_names_to_string uvs);
        uvs, t
      end
      else uvs, t
    in

    let uvs, t = tc_assume env (uvs, t) se.sigrng in
    [ { se with sigel = Sig_assume (lid, uvs, t) }], [], env0

  | Sig_main(e) ->
    let env = Env.set_range env r in
    let env = Env.set_expected_typ env t_unit in
    let e, c, g1 = tc_term env e in
    let e, _, g =
      let c, g_lc = TcComm.lcomp_comp c in
      let e, _x, g = check_expected_effect env (Some (U.ml_comp t_unit r)) (e, c) in
      e, _x, Env.conj_guard g_lc g in
    Rel.force_trivial_guard env (Env.conj_guard g1 g);
    let se = { se with sigel = Sig_main(e) } in
    [se], [], env0

  | Sig_splice (lids, t) ->
    if Options.debug_any () then
        BU.print2 "%s: Found splice of (%s)\n" (string_of_lid env.curmodule) (Print.term_to_string t);

    // Check the tactic
    let t, _, g = tc_tactic env t in
    Rel.force_trivial_guard env g;

    let ses = env.splice env t in
    let lids' = List.collect U.lids_of_sigelt ses in
    List.iter (fun lid ->
        match List.tryFind (Ident.lid_equals lid) lids' with
        (* If env.nosynth is on, nothing will be generated, so don't raise an error
         * so flycheck does spuriously not mark the line red *)
        | None when not env.nosynth ->
            raise_error (Errors.Fatal_SplicedUndef, BU.format2 "Splice declared the name %s but it was not defined.\nThose defined were: %s" (string_of_lid lid) (String.concat ", " <| List.map string_of_lid lids')) r
        | _ -> ()
    ) lids;
    let dsenv = List.fold_left DsEnv.push_sigelt_force env.dsenv ses in
    let env = { env with dsenv = dsenv } in
    [], ses, env

  | Sig_let(lbs, lids) ->
    let env = Env.set_range env r in
    let check_quals_eq l qopt val_q = match qopt with
      | None -> Some val_q
      | Some q' ->
        //logic is now a deprecated qualifier, so discard it from the checking
        let drop_logic = List.filter (fun x -> not (x = Logic)) in
        if (let val_q, q' = drop_logic val_q, drop_logic q' in
            List.length val_q = List.length q'
            && List.forall2 U.qualifier_equal val_q q')
        then Some q'  //but retain it in the returned list of qualifiers, some code may still add type annotations of Type0, which will hinder `logical` inference
        else raise_error (Errors.Fatal_InconsistentQualifierAnnotation, (BU.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              (Print.lid_to_string l)
                              (Print.quals_to_string val_q)
                              (Print.quals_to_string q'))) r
    in

    let rename_parameters lb =
      let rename_in_typ def typ =
        let typ = Subst.compress typ in
        let def_bs = match (Subst.compress def).n with
                     | Tm_abs (binders, _, _) -> binders
                     | _ -> [] in
        match typ with
        | { n = Tm_arrow(val_bs, c); pos = r } -> begin
          let has_auto_name bv =
            BU.starts_with bv.ppname.idText Ident.reserved_prefix in
          let rec rename_binders def_bs val_bs =
            match def_bs, val_bs with
            | [], _ | _, [] -> val_bs
            | (body_bv, _) :: bt, (val_bv, aqual) :: vt ->
              (match has_auto_name body_bv, has_auto_name val_bv with
               | true, _ -> (val_bv, aqual)
               | false, true -> ({ val_bv with
                                   ppname = { val_bv.ppname with
                                              idText = body_bv.ppname.idText } }, aqual)
               | false, false ->
                 // if body_bv.ppname.idText <> val_bv.ppname.idText then
                 //   Errors.warn body_bv.ppname.idRange
                 //     (BU.format2 "Parameter name %s doesn't match name %s used in val declaration"
                 //                  body_bv.ppname.idText val_bv.ppname.idText);
                 (val_bv, aqual)) :: rename_binders bt vt in
          Syntax.mk (Tm_arrow(rename_binders def_bs val_bs, c)) None r end
        | _ -> typ in
      { lb with lbtyp = rename_in_typ lb.lbdef lb.lbtyp } in

    (* 1. (a) Annotate each lb in lbs with a type from the corresponding val decl, if there is one
          (b) Generalize the type of lb only if none of the lbs have val decls nor explicit universes
      *)
    let should_generalize, lbs', quals_opt =
       snd lbs |> List.fold_left (fun (gen, lbs, quals_opt) lb ->
          let lbname = right lb.lbname in //this is definitely not a local let binding
          let gen, lb, quals_opt = match Env.try_lookup_val_decl env lbname.fv_name.v with
            | None ->
                if lb.lbunivs <> []
                then false, lb, quals_opt // we already have generalized universes (e.g. elaborated term)
                else gen, lb, quals_opt //no annotation found; use whatever was in the let binding

            | Some ((uvs,tval), quals) ->
              let quals_opt = check_quals_eq lbname.fv_name.v quals_opt quals in
              let def = match lb.lbtyp.n with
                | Tm_unknown -> lb.lbdef
                | _ ->
                  (* If there are two type ascriptions we check that they are compatible *)
                  mk (Tm_ascribed (lb.lbdef, (Inl lb.lbtyp, None), None)) None lb.lbdef.pos
              in
              if lb.lbunivs <> [] && List.length lb.lbunivs <> List.length uvs
              then raise_error (Errors.Fatal_IncoherentInlineUniverse, ("Inline universes are incoherent with annotation from val declaration")) r;
              false, //explicit annotation provided; do not generalize
              mk_lb (Inr lbname, uvs, PC.effect_ALL_lid, tval, def, [], lb.lbpos),
              quals_opt
          in
          gen, lb::lbs, quals_opt)
          (true, [], (if se.sigquals=[] then None else Some se.sigquals))
    in

    let quals = match quals_opt with
      | None -> [Visible_default]
      | Some q ->
        if q |> BU.for_some (function Irreducible | Visible_default | Unfold_for_unification_and_vcgen -> true | _ -> false)
        then q
        else Visible_default::q //the default visibility for a let binding is Unfoldable
    in

    let lbs' = List.rev lbs' in

    (* 2. Turn the top-level lb into a Tm_let with a unit body *)
    let e = mk (Tm_let((fst lbs, lbs'), mk (Tm_constant (Const_unit)) None r)) None r in

    (* 3. Type-check the Tm_let and convert it back to Sig_let *)
    let env' = { env with top_level = true; generalize = should_generalize } in
    let e =
      if Options.use_two_phase_tc () && Env.should_verify env' then begin
        let drop_lbtyp (e_lax:term) :term =
          match (SS.compress e_lax).n with
          | Tm_let ((false, [ lb ]), e2) ->
            let lb_unannotated =
              match (SS.compress e).n with  //checking type annotation on e, the lb before phase 1, capturing e from above
              | Tm_let ((_, [ lb ]), _) ->
                (match (SS.compress lb.lbtyp).n with
                 | Tm_unknown -> true
                 | _ -> false)
              | _                       -> failwith "Impossible: first phase lb and second phase lb differ in structure!"
            in
            if lb_unannotated then { e_lax with n = Tm_let ((false, [ { lb with lbtyp = S.tun } ]), e2)}  //erase the type annotation
            else e_lax
          | _ -> e_lax  //leave recursive lets as is
        in
        let (e, ms) =
            BU.record_time (fun () ->
              tc_maybe_toplevel_term ({ env' with phase1 = true; lax = true }) e |> (fun (e, _, _) -> e) |> N.remove_uvar_solutions env' |> drop_lbtyp
            ) in
        if Env.debug env <| Options.Other "TwoPhases" then
          BU.print1 "Let binding after phase 1: %s\n"
            (Print.term_to_string e);
        if Env.debug env <| Options.Other "TCDeclTime" then
          BU.print1 "Let binding elaborated (phase 1) in %s milliseconds\n"
            (string_of_int ms);
        e
      end
      else e
    in

    let attrs, post_tau =
        match U.extract_attr' PC.postprocess_with se.sigattrs with
        | None -> se.sigattrs, None
        | Some (ats, [tau, None]) -> ats, Some tau
        | Some (ats, args) ->
            Errors.log_issue r (Errors.Warning_UnrecognizedAttribute,
                                   ("Ill-formed application of `postprocess_with`"));
            se.sigattrs, None
    in
    let se = { se with sigattrs = attrs } in (* to remove the postprocess_with *)
    let postprocess_lb (tau:term) (lb:letbinding) : letbinding =
        let lbdef = env.postprocess env tau lb.lbtyp lb.lbdef in
        { lb with lbdef = lbdef }
    in
    let (r, ms) = BU.record_time (fun () -> tc_maybe_toplevel_term env' e) in
    if Env.debug env <| Options.Other "TCDeclTime" then
      BU.print1 "Let binding typechecked in phase 2 in %s milliseconds\n"
        (string_of_int ms);

    let se, lbs = match r with
      | {n=Tm_let(lbs, e)}, _, g when Env.is_trivial g ->
        // Propagate binder names into signature
        let lbs = (fst lbs, (snd lbs) |> List.map rename_parameters) in

        // Postprocess the letbindings with the tactic, if any
        let lbs = (fst lbs,
                    (match post_tau with
                     | Some tau -> List.map (postprocess_lb tau) (snd lbs)
                     | None -> (snd lbs)))
        in

        //propagate the MaskedEffect tag to the qualifiers
        let quals = match e.n with
            | Tm_meta(_, Meta_desugared Masked_effect) -> HasMaskedEffect::quals
            | _ -> quals
        in
        { se with sigel = Sig_let(lbs, lids);
                  sigquals =  quals },
        lbs
      | _ -> failwith "impossible (typechecking should preserve Tm_let)"
    in

    (* 4. Record the type of top-level lets, and log if requested *)
    snd lbs |> List.iter (fun lb ->
        let fv = right lb.lbname in
        Env.insert_fv_info env fv lb.lbtyp);

    if log env
    then BU.print1 "%s\n" (snd lbs |> List.map (fun lb ->
          let should_log = match Env.try_lookup_val_decl env (right lb.lbname).fv_name.v with
              | None -> true
              | _ -> false in
          if should_log
          then BU.format2 "let %s : %s" (Print.lbname_to_string lb.lbname) (Print.term_to_string (*env*) lb.lbtyp)
          else "") |> String.concat "\n");

    check_must_erase_attribute env0 se;

    [se], [], env0

(* [tc_decl env se] typechecks [se] in environment [env] and returns *)
(* the list of typechecked sig_elts, and a list of new sig_elts elaborated during typechecking but not yet typechecked *)
let tc_decl env se: list<sigelt> * list<sigelt> * Env.env =
  let env = set_hint_correlator env se in
  if Env.debug env Options.Low
  then BU.print1 ">>>>>>>>>>>>>>tc_decl %s\n" (Print.sigelt_to_string se);
  match get_fail_se se with
  | Some (_, false) when not (Env.should_verify env) ->
    (* If we're --laxing, and this is not an `expect_lax_failure`, then just ignore the definition *)
    [], [], env

  | Some (errnos, lax) ->
    let env' = if lax then { env with lax = true } else env in
    if Env.debug env Options.Low then
        BU.print1 ">> Expecting errors: [%s]\n" (String.concat "; " <| List.map string_of_int errnos);
    let errs, _ = Errors.catch_errors (fun () -> Options.with_saved_options (fun () -> tc_decl' env' se)) in
    if Env.debug env Options.Low then begin
        BU.print_string ">> Got issues: [\n";
        List.iter Errors.print_issue errs;
        BU.print_string ">>]\n"
    end;
    let sort = List.sortWith (fun x y -> x - y) in
    let errnos = sort errnos in
    let actual = sort (List.concatMap (fun i -> list_of_option i.issue_number) errs) in
    begin match errs with
    | [] ->
        List.iter Errors.print_issue errs;
        Errors.log_issue se.sigrng (Errors.Error_DidNotFail, "This top-level definition was expected to fail, but it succeeded")
    | _ ->
        if errnos <> [] && errnos <> actual then
            let (e, n1, n2) = match check_multi_eq errnos actual with
                              | Some r -> r
                              | None -> (-1, -1, -1) // should be impossible
            in
            List.iter Errors.print_issue errs;
            Errors.log_issue
                     se.sigrng
                     (Errors.Error_DidNotFail,
                      BU.format5 "This top-level definition was expected to raise error codes %s, \
                                  but it raised %s. Error #%s was raised %s times, instead of %s."
                                    (FStar.Common.string_of_list string_of_int errnos)
                                    (FStar.Common.string_of_list string_of_int actual)
                                    (string_of_int e) (string_of_int n2) (string_of_int n1))
        else ()
    end;
    [], [], env

  | None ->
    tc_decl' env se

let for_export env hidden se : list<sigelt> * list<lident> =
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
   let is_abstract quals = quals |> BU.for_some (function Abstract-> true | _ -> false) in
   let is_hidden_proj_or_disc q = match q with
      | Projector(l, _)
      | Discriminator l -> hidden |> BU.for_some (lid_equals l)
      | _ -> false
   in
   match se.sigel with
  | Sig_pragma         _ -> [], hidden

  | Sig_splice _
  | Sig_inductive_typ _
  | Sig_datacon _ -> failwith "Impossible (Already handled)"

  | Sig_bundle(ses, _) ->
    if is_abstract se.sigquals
    then
      let for_export_bundle se (out, hidden) = match se.sigel with
        | Sig_inductive_typ(l, us, bs, t, _, _) ->
          let dec = { se with sigel = Sig_declare_typ(l, us, U.arrow bs (S.mk_Total t));
                              sigquals=Assumption::New::se.sigquals } in
          dec::out, hidden

        (* logically, each constructor just becomes an uninterpreted function *)
        | Sig_datacon(l, us, t, _, _, _) ->
          let dec = { se with sigel = Sig_declare_typ(l, us, t);
                              sigquals = [Assumption] } in
          dec::out, l::hidden

        | _ ->
          out, hidden
      in
      List.fold_right for_export_bundle ses ([], hidden)
    else [se], hidden

  | Sig_assume(_, _, _) ->
    if is_abstract se.sigquals
    then [], hidden
    else [se], hidden

  | Sig_declare_typ(l, us, t) ->
    if se.sigquals |> BU.for_some is_hidden_proj_or_disc //hidden projectors/discriminators become uninterpreted
    then [{se with sigel = Sig_declare_typ(l, us, t);
                   sigquals = [Assumption] }],
         l::hidden
    else if se.sigquals |> BU.for_some (function
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

  | Sig_let((false, [lb]), _)
        when se.sigquals |> BU.for_some is_hidden_proj_or_disc ->
    let fv = right lb.lbname in
    let lid = fv.fv_name.v in
    if hidden |> BU.for_some (S.fv_eq_lid fv)
    then [], hidden //this projector definition already has a declare_typ
    else let dec = { sigel = Sig_declare_typ(fv.fv_name.v, lb.lbunivs, lb.lbtyp);
                     sigquals =[Assumption];
                     sigrng = Ident.range_of_lid lid;
                     sigmeta = default_sigmeta;
                     sigattrs = [] } in
          [dec], lid::hidden

  | Sig_let(lbs, l) ->
    if is_abstract se.sigquals
    then (snd lbs |>  List.map (fun lb ->
           { se with sigel = Sig_declare_typ((right lb.lbname).fv_name.v, lb.lbunivs, lb.lbtyp);
                     sigquals = Assumption::se.sigquals}),
          hidden)
    else [se], hidden

(* adds the typechecked sigelt to the env, also performs any processing required in the env (such as reset options) *)
(* this was earlier part of tc_decl, but separating it might help if and when we cache type checked modules *)
let add_sigelt_to_env (env:Env.env) (se:sigelt) :Env.env =
  if Env.debug env Options.Low
  then BU.print1 ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n" (Print.sigelt_to_string se);
  match se.sigel with
  | Sig_inductive_typ _ -> failwith "add_sigelt_to_env: Impossible, bare data constructor"
  | Sig_datacon _ -> failwith "add_sigelt_to_env: Impossible, bare data constructor"

  | Sig_pragma (PushOptions _)
  | Sig_pragma PopOptions
  | Sig_pragma (SetOptions _)
  | Sig_pragma (ResetOptions _) ->
    (* we keep --using_facts_from reflected in the environment, so update it here *)
    let env = { env with proof_ns = Options.using_facts_from () } in
    env

  | Sig_pragma RestartSolver ->
    env.solver.refresh ();
    env

  | Sig_pragma _
  | Sig_new_effect_for_free _ -> env
  | Sig_new_effect ne ->
    let env = Env.push_sigelt env se in
    ne.actions |> List.fold_left (fun env a -> Env.push_sigelt env (U.action_as_lb ne.mname a a.action_defn.pos)) env
  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _) when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) -> env
  | _ -> Env.push_sigelt env se

let tc_decls env ses =
  let rec process_one_decl (ses, exports, env, hidden) se =
    if Env.debug env Options.Low
    then BU.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" (Print.sigelt_to_string se);

    let ses', ses_elaborated, env = tc_decl env se in
    let ses' = ses' |> List.map (fun se ->
        if Env.debug env (Options.Other "UF")
        then BU.print1 "About to elim vars from %s\n" (Print.sigelt_to_string se);
        N.elim_uvars env se) in
    let ses_elaborated = ses_elaborated |> List.map (fun se ->
        if Env.debug env (Options.Other "UF")
        then BU.print1 "About to elim vars from (elaborated) %s\m" (Print.sigelt_to_string se);
        N.elim_uvars env se) in

    Env.promote_id_info env (fun t ->
        N.normalize
               [Env.AllowUnboundUniverses; //this is allowed, since we're reducing types that appear deep within some arbitrary context
                Env.CheckNoUvars;
                Env.Beta; Env.DoNotUnfoldPureLets; Env.CompressUvars;
                Env.Exclude Env.Zeta; Env.Exclude Env.Iota; Env.NoFullNorm]
              env
              t); //update the id_info table after having removed their uvars
    let env = ses' |> List.fold_left (fun env se -> add_sigelt_to_env env se) env in
    FStar.Syntax.Unionfind.reset();

    if Options.log_types() || Env.debug env <| Options.Other "LogTypes"
    then begin
      BU.print1 "Checked: %s\n" (List.fold_left (fun s se -> s ^ Print.sigelt_to_string se ^ "\n") "" ses')
    end;

    List.iter (fun se -> env.solver.encode_sig env se) ses';

    let exports, hidden =
      if Options.use_extracted_interfaces () then List.rev_append ses' exports, []
      else
        let accum_exports_hidden (exports, hidden) se =
          let se_exported, hidden = for_export env hidden se in
          List.rev_append se_exported exports, hidden
        in
        List.fold_left accum_exports_hidden (exports, hidden) ses'
    in

    // GM: Aug 28 2018, pretty sure this is unneded as the only sigelt that can
    // be present in ses' is the typechecked se (or none). I'm taking it out
    // so I can make `postprocess_with` remove itself during typechecking
    // (otherwise, it would run twice with extracted interfaces)
    (* let ses' = List.map (fun s -> { s with sigattrs = se.sigattrs }) ses' in *)

    (List.rev_append ses' ses, exports, env, hidden), ses_elaborated
  in
  // A wrapper to (maybe) print the time taken for each sigelt
  let process_one_decl_timed acc se =
    let (_, _, env, _) = acc in
    let r =
      Profiling.profile
                 (fun () -> process_one_decl acc se)
                 (Some (Ident.string_of_lid (Env.current_module env)))
                 "FStar.TypeChecker.Tc.process_one_decl"
    in
    if Options.profile_group_by_decls()
    then begin
         let tag =
          match lids_of_sigelt se with
          | hd::_ -> Ident.string_of_lid hd
          | _ -> Range.string_of_range (range_of_sigelt se)
         in
         Profiling.report_and_clear tag
    end;
    r
  in
  let ses, exports, env, _ = BU.fold_flatten process_one_decl_timed ([], [], env, []) ses in
  List.rev_append ses [], List.rev_append exports [], env

(* Consider the module:
        module Test
        abstract type t = nat
        let f (x:t{x > 0}) : Tot t = x

   The type of f : x:t{x>0} -> t
   from the perspective of a client of Test
   is ill-formed, since it the sub-term `x > 0` requires x:int, not x:t

   `check_exports` checks the publicly visible symbols exported by a module
   to make sure that all of them have types that are well-formed from a client's
   perspective.
*)
open FStar.TypeChecker.Err
let check_exports env (modul:modul) exports =
    let env = {env with lax=true; lax_universes=true; top_level=true} in
    let check_term lid univs t =
        let univs, t = SS.open_univ_vars univs t in
        if Env.debug (Env.set_current_module env modul.name) <| Options.Other "Exports"
        then BU.print3 "Checking for export %s <%s> : %s\n"
                (Print.lid_to_string lid)
                (univs |> List.map (fun x -> Print.univ_to_string (U_name x)) |> String.concat ", ")
                (Print.term_to_string t);
        let env = Env.push_univ_vars env univs in
        TcTerm.tc_trivial_guard env t |> ignore
    in
    let check_term lid univs t =
        let _ = Errors.message_prefix.set_prefix
                (BU.format2 "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
                        (Print.lid_to_string modul.name)
                        (Print.lid_to_string lid)) in
        check_term lid univs t;
        Errors.message_prefix.clear_prefix()
    in
    let rec check_sigelt = fun se -> match se.sigel with
        | Sig_bundle(ses, _) ->
          if not (se.sigquals |> List.contains Private)
          then ses |> List.iter check_sigelt
        | Sig_inductive_typ (l, univs, binders, typ, _, _) ->
          let t = S.mk (Tm_arrow(binders, S.mk_Total typ)) None se.sigrng in
          check_term l univs t
        | Sig_datacon(l , univs, t, _, _, _) ->
          check_term l univs t
        | Sig_declare_typ(l, univs, t) ->
          if not (se.sigquals |> List.contains Private)
          then check_term l univs t
        | Sig_let((_, lbs), _) ->
          if not (se.sigquals |> List.contains Private)
          then lbs |> List.iter (fun lb ->
               let fv = right lb.lbname in
               check_term fv.fv_name.v lb.lbunivs lb.lbtyp)
        | Sig_effect_abbrev(l, univs, binders, comp, flags) ->
          if not (se.sigquals |> List.contains Private)
          then let arrow = S.mk (Tm_arrow(binders, comp)) None se.sigrng in
               check_term l univs arrow
        | Sig_main _
        | Sig_assume _
        | Sig_new_effect _
        | Sig_new_effect_for_free _
        | Sig_sub_effect _
        | Sig_splice _
        | Sig_pragma _ -> ()
    in
    if Ident.lid_equals modul.name PC.prims_lid
    then ()
    else List.iter check_sigelt exports

(*
 * extract an interface from m
 * this function uses the environment ONLY for unfolding effect abbreviations to see if the effect is reifiable etc.
 *)
let extract_interface (en:env) (m:modul) :modul =
  let is_abstract = List.contains Abstract in
  let is_irreducible = List.contains Irreducible in
  let is_assume = List.contains Assumption in
  let filter_out_abstract = List.filter (fun q -> not (q = Abstract || q = Irreducible || q = Visible_default)) in
  let filter_out_abstract_and_noeq = List.filter (fun q -> not (q = Abstract || q = Noeq || q = Unopteq || q = Irreducible || q = Visible_default)) in  //abstract inductive should not have noeq and unopteq
  let filter_out_abstract_and_inline = List.filter (fun q -> not (q = Abstract || q = Irreducible || q = Visible_default || q = Inline_for_extraction || q = Unfold_for_unification_and_vcgen)) in

  //we need to filter out projectors and discriminators of abstract inductive datacons, so keep track of such datacons, and keep tycons for haseq purposes
  let abstract_inductive_tycons   = BU.mk_ref [] in
  let abstract_inductive_datacons = BU.mk_ref [] in

  let is_projector_or_discriminator_of_an_abstract_inductive (quals:list<qualifier>) :bool =
    List.existsML (fun q ->
      match q with
      | Discriminator l
      | Projector (l, _) -> true //List.existsb (fun l' -> lid_equals l l') !abstract_inductive_datacons
      | _ -> false
    ) quals
  in

  let vals_of_abstract_inductive (s:sigelt) :sigelts =
    let mk_typ_for_abstract_inductive (bs:binders) (t:typ) (r:Range.range) :typ =
      match bs with
      | [] -> t
      | _  ->
        (match t.n with
         | Tm_arrow (bs', c ) -> mk (Tm_arrow (bs@bs', c)) None r  //flattening arrows?
         | _ -> mk (Tm_arrow (bs, mk_Total t)) None r)  //Total ok?
    in

    match s.sigel with
    | Sig_inductive_typ (lid, uvs, bs, t, _, _) ->  //add a val declaration for the type
      let s1 = { s with sigel = Sig_declare_typ (lid, uvs, mk_typ_for_abstract_inductive bs t s.sigrng);
                        sigquals = Assumption::New::(filter_out_abstract_and_noeq s.sigquals) }  //Assumption qualifier seems necessary, else smt encoding waits for the definition for the symbol to be encoded
      in
      [s1]
    | _ -> failwith "Impossible!"
  in

  let val_of_lb (s:sigelt) (lid:lident) ((uvs, t): (univ_names * typ)) (lbdef:term) :sigelt =
    let attrs =
      if TcUtil.must_erase_for_extraction en lbdef then (lid_as_fv PC.must_erase_for_extraction_attr delta_constant None |> fv_to_tm)::s.sigattrs
      else s.sigattrs
    in
    { s with sigel = Sig_declare_typ (lid, uvs, t); sigquals = Assumption::(filter_out_abstract_and_inline s.sigquals); sigattrs = attrs }
  in

  (*
   * When do we keep the body of the letbinding in the interface ...
   *)
  let should_keep_lbdef (t:typ) :bool =
    let comp_effect_name (c:comp) :lident = //internal function, caller makes sure c is a Comp case
      match c.n with | Comp c -> c.effect_name | _ -> failwith "Impossible!"
    in

    let c_opt =
      //if t is unit, make c_opt = Some (Tot unit), this will then be culled finally
      if is_unit t then Some (S.mk_Total t) else match (SS.compress t).n with | Tm_arrow (_, c) -> Some c | _ -> None
    in

    match c_opt with
    | None -> true //we can't get the comp type for sure, e.g. t is not an arrow (say if..then..else), so keep the body
    | Some c ->
        // discard lemmas, we don't need their bodies
        if is_lemma_comp c
        then false
        else if is_pure_or_ghost_comp c // keep all pure functions
        then true
        else Env.is_reifiable_effect en (comp_effect_name c) //else only keep it if the effect is reifiable
  in

  let extract_sigelt (s:sigelt) :list<sigelt> =
    if Env.debug en Options.Extreme
    then BU.print1 "Extracting interface for %s\n" (Print.sigelt_to_string s);
    match s.sigel with
    | Sig_inductive_typ _
    | Sig_datacon _ -> failwith "Impossible! extract_interface: bare data constructor"

    | Sig_splice _ -> failwith "Impossible! extract_interface: trying to extract splice"

    | Sig_bundle (sigelts, lidents) ->
      if is_abstract s.sigquals then
        //for an abstract inductive type, we will only retain the type declarations, in an unbundled form
        sigelts |> List.fold_left (fun sigelts s ->
          match s.sigel with
          | Sig_inductive_typ (lid, _, _, _, _, _) -> abstract_inductive_tycons := lid::!abstract_inductive_tycons; (vals_of_abstract_inductive s)@sigelts
          | Sig_datacon (lid, _, _, _, _, _) ->
            abstract_inductive_datacons := lid::!abstract_inductive_datacons;
            sigelts  //nothing to do for datacons
          | _ -> failwith "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon"
        ) []
      else [s]  //if it is not abstract, retain the bundle as is
    | Sig_declare_typ (lid, uvs, t) ->
      //if it's a projector or discriminator of an abstract inductive, got to go
      if is_projector_or_discriminator_of_an_abstract_inductive s.sigquals then []
      //if it's an assumption, no let is coming, so add it as is
      else if is_assume s.sigquals then [ { s with sigquals = filter_out_abstract s.sigquals } ]
      //else leave the decision to let
      else []
    | Sig_let (lbs, lids) ->
      //if it's a projector or discriminator of an abstract inductive, got to go
      if is_projector_or_discriminator_of_an_abstract_inductive s.sigquals then []
      else
        //extract the type annotations from all the letbindings
        let flbs, slbs = lbs in
        let typs_and_defs = slbs |> List.map (fun lb -> lb.lbunivs, lb.lbtyp, lb.lbdef) in

        let is_lemma = List.existsML (fun (_, t, _) -> t |> U.is_lemma) typs_and_defs in
        //if is it abstract or irreducible or lemma, keep just the vals
        let vals = List.map2 (fun lid (u, t, d) -> val_of_lb s lid (u, t) d) lids typs_and_defs in
        if is_abstract s.sigquals || is_irreducible s.sigquals || is_lemma then vals
        else
          let should_keep_defs = List.existsML (fun (_, t, _) -> t |> should_keep_lbdef) typs_and_defs in
          if should_keep_defs then [ s ]
          else vals
    | Sig_main t -> failwith "Did not anticipate main would arise when extracting interfaces!"
    | Sig_assume (lid, _, _) ->
      //keep hasEq of abstract inductive, and drop for others (since they will be regenerated)
      let is_haseq = TcInductive.is_haseq_lid lid in
      if is_haseq then
        let is_haseq_of_abstract_inductive = List.existsML (fun l -> lid_equals lid (TcInductive.get_haseq_axiom_lid l)) !abstract_inductive_tycons in
        if is_haseq_of_abstract_inductive then [ { s with sigquals = filter_out_abstract s.sigquals } ]
        else []
      else [ { s with sigquals = filter_out_abstract s.sigquals } ]
    | Sig_new_effect _
    | Sig_new_effect_for_free _
    | Sig_sub_effect _
    | Sig_effect_abbrev _ -> [s]
    | Sig_pragma _ -> [s]
  in

  { m with declarations = m.declarations |> List.map extract_sigelt |> List.flatten; is_interface = true }

let snapshot_context env msg = BU.atomically (fun () ->
    TypeChecker.Env.snapshot env msg)

let rollback_context solver msg depth : env = BU.atomically (fun () ->
    let env = TypeChecker.Env.rollback solver msg depth in
    env)

let push_context env msg = snd (snapshot_context env msg)
let pop_context env msg = rollback_context env.solver msg None

let tc_partial_modul env modul =
  let verify = Options.should_verify modul.name.str in
  let action = if verify then "Verifying" else "Lax-checking" in
  let label = if modul.is_interface then "interface" else "implementation" in
  if Options.debug_any () then
    BU.print3 "%s %s of %s\n" action label modul.name.str;

  let name = BU.format2 "%s %s"  (if modul.is_interface then "interface" else "module") modul.name.str in
  let env = {env with Env.is_iface=modul.is_interface; admit=not verify} in
  let env = Env.set_current_module env modul.name in
  let ses, exports, env = tc_decls env modul.declarations in
  {modul with declarations=ses}, exports, env

let tc_more_partial_modul env modul decls =
  let ses, exports, env = tc_decls env decls in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, exports, env

let rec tc_modul (env0:env) (m:modul) (iface_exists:bool) :(modul * env) =
  let msg = "Internals for " ^ m.name.str in
  //AR: push env, this will also push solver, and then finish_partial_modul will do the pop
  let env0 = push_context env0 msg in
  let modul, non_private_decls, env = tc_partial_modul env0 m in
  finish_partial_modul false iface_exists env modul non_private_decls

and finish_partial_modul (loading_from_cache:bool) (iface_exists:bool) (en:env) (m:modul) (exports:list<sigelt>) : (modul * env) =
  //AR: do we ever call finish_partial_modul for current buffer in the interactive mode?
  let should_extract_interface =
    (not loading_from_cache)            &&
    (not iface_exists)                  &&
    Options.use_extracted_interfaces () &&
    (not m.is_interface)                &&
    FStar.Errors.get_err_count() = 0
  in
  if should_extract_interface then begin //if we are using extracted interfaces and this is not already an interface
    //extract the interface in the new environment, this helps us figure out things like if an effect is reifiable
    let modul_iface = extract_interface en m in
    if Env.debug en <| Options.Low then
      BU.print4 "Extracting and type checking module %s interface%s%s%s\n" m.name.str
                (if Options.should_verify m.name.str then "" else " (in lax mode) ")
                (if Options.dump_module m.name.str then ("\nfrom: " ^ (Syntax.Print.modul_to_string m) ^ "\n") else "")
                (if Options.dump_module m.name.str then ("\nto: " ^ (Syntax.Print.modul_to_string modul_iface) ^ "\n") else "");

    //set up the environment to verify the interface
    let en0 =
      //pop to get the env before this module type checking...
      let en0 = pop_context en ("Ending modul " ^ m.name.str) in
      //.. but restore the dsenv, since typechecking `m` might have elaborated
      // some %splices that we need to properly resolve further modules
      let en0 = { en0 with dsenv = en.dsenv } in
      //for hints, we want to use the same id counter as was used in typechecking the module itself, so use the tbl from latest env
      let en0 = { en0 with qtbl_name_and_index = en.qtbl_name_and_index |> fst, None } in
      //restore command line options ad restart z3 (to reset things like nl.arith options)
      if not (Options.interactive ()) then begin  //we should not have this case actually since extracted interfaces are not supported in ide yet
        Options.restore_cmd_line_options true |> ignore;
        en0
      end
      else en0
    in

    //AR: the third flag 'true' is for iface_exists for the current file, since it's an iface already, pass true
    let modul_iface, env = tc_modul en0 modul_iface true in
    { m with exports = modul_iface.exports }, env  //note: setting the exports for m, once extracted_interfaces is default, exports should just go away
  end
  else
    let modul = { m with exports = exports } in
    let env = Env.finish_module en modul in

    //we can clear the lid to query index table
    env.qtbl_name_and_index |> fst |> BU.smap_clear;

    if not (Options.lax())
    && not loading_from_cache
    && not (Options.use_extracted_interfaces ())
    then check_exports env modul exports;

    //pop BUT ignore the old env
    pop_context env ("Ending modul " ^ modul.name.str) |> ignore;

    //moved the code for encoding the module to smt to Universal

    modul, env

let load_checked_module (en:env) (m:modul) :env =
  //This function tries to very carefully mimic the effect of the environment
  //of having checked the module from scratch, i.e., using tc_module below
  let env = Env.set_current_module en m.name in
  //push context, finish_partial_modul will do the pop
  let env = push_context env ("Internals for " ^ Ident.string_of_lid m.name) in
  let env = List.fold_left (fun env se ->
             //push every sigelt in the environment
             let env = Env.push_sigelt env se in
             //and then query it back immediately to populate the environment's internal cache
             //this is important for extraction to work correctly,
             //in particular, when extracting a module we want the module's internal symbols
             //that may be marked "abstract" externally to be visible internally
             //populating the cache enables this behavior, rather indirectly, sadly : (
             let lids = Util.lids_of_sigelt se in
             lids |> List.iter (fun lid -> ignore (Env.try_lookup_lid env lid));
             env)
             env
             m.declarations in
  //And then call finish_partial_modul, which is the normal workflow of tc_modul below
  //except with the flag `must_check_exports` set to false, since this is already a checked module
  //the second true flag is for iface_exists, used to determine whether should extract interface or not
  let _, env = finish_partial_modul true true env m m.exports in
  env

let check_module env m b =
  if Options.debug_any()
  then BU.print2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.lid_to_string m.name);
  if Options.dump_module m.name.str
  then BU.print1 "Module before type checking:\n%s\n" (Print.modul_to_string m);

  let env = {env with lax=not (Options.should_verify m.name.str)} in
  let m, env = tc_modul env m b in

  (* Debug information for level Normalize : normalizes all toplevel declarations an dump the current module *)
  if Options.dump_module m.name.str
  then BU.print1 "Module after type checking:\n%s\n" (Print.modul_to_string m);
  if Options.dump_module m.name.str && Options.debug_at_level m.name.str (Options.Other "Normalize")
  then begin
    let normalize_toplevel_lets = fun se -> match se.sigel with
        | Sig_let ((b, lbs), ids) ->
            let n = N.normalize [Env.Beta ; Env.Eager_unfolding; Env.Reify ; Env.Inlining ; Env.Primops ; Env.UnfoldUntil S.delta_constant ; Env.AllowUnboundUniverses ] in
            let update lb =
                let univnames, e = SS.open_univ_vars lb.lbunivs lb.lbdef in
                { lb with lbdef = n (Env.push_univ_vars env univnames) e }
            in
            { se with sigel = Sig_let ((b, List.map update lbs), ids) }
        | _ -> se
    in
    let normalized_module = { m with declarations = List.map normalize_toplevel_lets m.declarations } in
    BU.print1 "%s\n" (Print.modul_to_string normalized_module)
  end;

  m, env
