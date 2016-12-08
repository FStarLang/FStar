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
open FStar.TypeChecker.TcTerm
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print

// VALS_HACK_HERE

//set the name of the query so that we can correlate hints to source program fragments
let set_hint_correlator env se =
    match Options.reuse_hint_for () with
    | Some l ->
      let lid = Ident.lid_add_suffix (Env.current_module env) l in
      {env with qname_and_index=Some (lid, 0)}

    | None ->
      let lids = Util.lids_of_sigelt se in
      let lid = match lids with
            | [] -> Ident.lid_add_suffix (Env.current_module env)
                                         (S.next_id () |> Util.string_of_int)
            | l::_ -> l in
      {env with qname_and_index=Some (lid, 0)}

let log env = (Options.log_types()) && not(lid_equals Const.prims_lid (Env.current_module env))

(*****************Type-checking the signature of a module*****************************)

let tc_check_trivial_guard env t k =
  let t, c, g = tc_check_tot_or_gtot_term env t k in
  t.tk := Some c.res_typ.n;
  Rel.force_trivial_guard env g;
  t

// A helper to check that the terms elaborated by DMFF are well-typed
let recheck_debug s env t =
  if Env.debug env (Options.Other "ED") then
    Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s (Print.term_to_string t);
  let t', _, _ = tc_term env t in
  if Env.debug env (Options.Other "ED") then
    Util.print1 "Re-checked; got:\n%s\n----------\n" (Print.term_to_string t');
  // Return the original term (without universes unification variables);
  // because [tc_eff_decl] will take care of these
  t


let check_and_gen env t k =
    // Util.print1 "\x1b[01;36mcheck and gen \x1b[00m%s\n" (Print.term_to_string t);
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
        | [(a, _);(wp, _)] -> a, wp.sort
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

let rec tc_eff_decl env0 (ed:Syntax.eff_decl) =
  assert (ed.univs = []); //no explicit universe variables in the source; Q: But what about re-type-checking a program?
  let effect_params_un, signature_un, opening = SS.open_term' ed.binders ed.signature in
  let effect_params, env, _ = tc_tparams env0 effect_params_un in
  let signature, _    = tc_trivial_guard env signature_un in
  let ed = {ed with binders=effect_params;
                    signature=signature} in
  //open ed's operations with respect to the effect parameters that are already in scope
  let ed = match effect_params with
    | [] -> ed
    | _ ->
        let op ts =
            assert (fst ts = []);
            let t1 = SS.subst opening (snd ts) in
            ([], t1) in
        { ed with
            ret_wp        =op ed.ret_wp
            ; bind_wp     =op ed.bind_wp
            ; return_repr =op ed.return_repr
            ; bind_repr   =op ed.bind_repr
            ; if_then_else=op ed.if_then_else
            ; ite_wp      =op ed.ite_wp
            ; stronger    =op ed.stronger
            ; close_wp    =op ed.close_wp
            ; assert_p    =op ed.assert_p
            ; assume_p    =op ed.assume_p
            ; null_wp     =op ed.null_wp
            ; trivial     =op ed.trivial
            ; repr        = snd (op ([], ed.repr))
            ; actions     = List.map (fun a ->
            { a with
                action_defn = snd (op ([], a.action_defn));
                action_typ = snd (op ([], a.action_typ)) }) ed.actions
        }
  in
   //Returns (a:Type) and M.WP a, for a fresh name a
  let wp_with_fresh_result_type env mname signature =
       let fail t = raise (Error(Errors.unexpected_signature_for_monad env mname t, range_of_lid mname)) in
       match (SS.compress signature).n with
          | Tm_arrow(bs, c) ->
            let bs = SS.open_binders bs in
            begin match bs with
                | [(a, _);(wp, _)] -> a, wp.sort
                | _ -> fail signature
            end
          | _ -> fail signature
  in
  let a, wp_a = wp_with_fresh_result_type env ed.mname ed.signature in
  let fresh_effect_signature ()  =
    //we type-check the signature_un again, because we want a fresh universe
    let signature, _ = tc_trivial_guard env signature_un in
    wp_with_fresh_result_type env ed.mname signature in

  //put the signature in the environment to prevent generalizing its free universe variables until we're done
  let env = Env.push_bv env (S.new_bv None ed.signature) in

  if Env.debug env0 <| Options.Other "ED"
  then Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                        (Print.lid_to_string ed.mname)
                        (Print.binders_to_string " " ed.binders)
                        (Print.term_to_string ed.signature)
                        (Print.term_to_string (S.bv_to_name a))
                        (Print.term_to_string a.sort);

  let check_and_gen' env (_,t) k =
    check_and_gen env t k in

  let return_wp =
    let expected_k = Util.arrow [S.mk_binder a; S.null_binder (S.bv_to_name a)] (S.mk_GTotal wp_a) in
    check_and_gen' env ed.ret_wp expected_k in

  let bind_wp =
    let b, wp_b = fresh_effect_signature () in
    let a_wp_b = Util.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_b) in
    let expected_k = Util.arrow [S.null_binder t_range;
                                 S.mk_binder a; S.mk_binder b;
                                 S.null_binder wp_a;
                                 S.null_binder a_wp_b]
                                 (S.mk_Total wp_b) in
    check_and_gen' env ed.bind_wp expected_k in

  let if_then_else =
    let p = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let expected_k = Util.arrow [S.mk_binder a; S.mk_binder p;
                                 S.null_binder wp_a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.if_then_else expected_k in

  let ite_wp =
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.ite_wp expected_k in

  let stronger =
    let t, _ = U.type_u() in
    let expected_k = Util.arrow [S.mk_binder a;
                                 S.null_binder wp_a;
                                 S.null_binder wp_a]
                                (S.mk_Total t) in
    check_and_gen' env ed.stronger expected_k in

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

  let repr, bind_repr, return_repr, actions =
      match (SS.compress ed.repr).n with
      | Tm_unknown -> //This is not a DM4F effect definition; so nothing to do
        ed.repr, ed.bind_repr, ed.return_repr, ed.actions
      | _ ->
        //This is a DM4F effect definition
        //Need to check that the repr, bind, return and actions have their expected types
        let repr =
            let t, _ = Util.type_u () in
            let expected_k = Util.arrow [S.mk_binder a;
                                         S.null_binder wp_a]
                                         (S.mk_GTotal t) in
            (* printfn "About to check repr=%s\nat type %s\n" (Print.term_to_string ed.repr) (Print.term_to_string expected_k); *)
            tc_check_trivial_guard env ed.repr expected_k in

        let mk_repr' t wp =
            let repr = N.normalize [N.EraseUniverses; N.AllowUnboundUniverses] env repr in
            mk (Tm_app(repr, [as_arg t; as_arg wp])) None Range.dummyRange in

        let mk_repr a wp =
            mk_repr' (S.bv_to_name a) wp in

        let destruct_repr t =
            match (SS.compress t).n with
            | Tm_app(_, [(t, _); (wp, _)]) -> t, wp
            | _ -> failwith "Unexpected repr type" in

        let bind_repr =
            let r = S.lid_as_fv FStar.Syntax.Const.range_0 Delta_constant None |> S.fv_to_tm in
            let b, wp_b = fresh_effect_signature () in
            let a_wp_b = Util.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_b) in
            let wp_f = S.gen_bv "wp_f" None wp_a in
            let wp_g = S.gen_bv "wp_g" None a_wp_b in
            let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
            let wp_g_x = mk_Tm_app (S.bv_to_name wp_g) [as_arg <| S.bv_to_name x_a] None Range.dummyRange in
            let res =
                let wp = mk_Tm_app (Env.inst_tscheme bind_wp |> snd)
                                   (List.map as_arg [r; S.bv_to_name a;
                                                     S.bv_to_name b; S.bv_to_name wp_f;
                                                     S.bv_to_name wp_g])
                                   None Range.dummyRange in
                mk_repr b wp in

            let expected_k = Util.arrow [S.mk_binder a;
                                         S.mk_binder b;
                                         S.mk_binder wp_f;
                                         S.null_binder (mk_repr a (S.bv_to_name wp_f));
                                         S.mk_binder wp_g;
                                         S.null_binder (Util.arrow [S.mk_binder x_a] (S.mk_Total <| mk_repr b (wp_g_x)))]
                                        (S.mk_Total res) in
//            printfn "About to check expected_k %s\n"
//                     (Print.term_to_string expected_k);
            let expected_k, _, _ =
                tc_tot_or_gtot_term env expected_k in
//            printfn "About to check bind=%s\n\n, at type %s\n"
//                     (Print.term_to_string (snd ed.bind_repr))
//                     (Print.term_to_string expected_k);
            let env = Env.set_range env (snd (ed.bind_repr)).pos in
            let env = {env with lax=true} in //we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
            let br = check_and_gen' env ed.bind_repr expected_k in
//            let _ = printfn "After checking bind_repr is %s\nexpected_k is %s\n" (Print.tscheme_to_string br) (Print.term_to_string expected_k) in
            br in

        let return_repr =
            let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
            let res =
                let wp = mk_Tm_app (Env.inst_tscheme return_wp |> snd)
                                   (List.map as_arg [S.bv_to_name a; S.bv_to_name x_a])
                                   None Range.dummyRange in
                mk_repr a wp in
            let expected_k = Util.arrow [S.mk_binder a;
                                         S.mk_binder x_a]
                                       (S.mk_Total res) in
            let expected_k, _, _ =
                tc_tot_or_gtot_term env expected_k in
            (* printfn "About to check return_repr=%s, at type %s\n" *)
            (*         (Print.term_to_string (snd ed.return_repr)) *)
            (*         (Print.term_to_string expected_k); *)
            let env = Env.set_range env (snd (ed.return_repr)).pos in
            let univs, repr = check_and_gen' env ed.return_repr expected_k in
            match univs with
            | [] -> [], repr
            | _ -> raise (Error("Unexpected universe-polymorphic return for effect", repr.pos)) in

      let actions =
        let check_action act =
          // 0) The action definition has a (possibly) useless type; the
          // action cps'd type contains the "good" wp that tells us EVERYTHING
          // about what this action does. Please note that this "good" wp is
          // of the form [binders -> repr ...], i.e. is it properly curried.
          let act_typ, _, g_t = tc_tot_or_gtot_term env act.action_typ in

          // 1) Check action definition, setting its expected type to
          //    [action_typ]
          let env' = Env.set_expected_typ env act_typ in
          if Env.debug env (Options.Other "ED") then
            Util.print3 "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
              (text_of_lid act.action_name) (Print.term_to_string act.action_defn)
              (Print.term_to_string act_typ);
          let act_defn, _, g_a = tc_tot_or_gtot_term env' act.action_defn in

          let act_defn = N.normalize [ N.UnfoldUntil S.Delta_constant ] env act_defn in
          let act_typ = N.normalize [ N.UnfoldUntil S.Delta_constant; N.Eager_unfolding; N.Beta ] env act_typ in

          // 2) This implies that [action_typ] has Type(k): good for us!

          // 3) Unify [action_typ] against [expected_k], because we also need
          // to check that the action typ is of the form [binders -> repr ...]
          let expected_k, g_k =
            let act_typ = SS.compress act_typ in
            match act_typ.n with
            | Tm_arrow(bs, c) ->
              let bs, _ = SS.open_comp bs c in
              let res = mk_repr' S.tun S.tun in
              let k = Util.arrow bs (S.mk_Total res) in
              let k, _, g = tc_tot_or_gtot_term env k in
              k, g
            | _ -> raise (Error(Util.format2
              "Actions must have function types (not: %s, a.k.a. %s)"
                (Print.term_to_string act_typ) (Print.tag_of_term act_typ), act_defn.pos))
          in
          let g = Rel.teq env act_typ expected_k in
          Rel.force_trivial_guard env (Rel.conj_guard g_a (Rel.conj_guard g_k (Rel.conj_guard g_t g)));

          // 4) Do a bunch of plumbing to assign a type in the new monad to
          //    the action
          let act_typ = match (SS.compress expected_k).n with
              | Tm_arrow(bs, c) ->
                let bs, c = SS.open_comp bs c in
                let a, wp = destruct_repr (Util.comp_result c) in
                let c = {
                  comp_univs=[env.universe_of env a];
		          effect_name = ed.mname;
                  result_typ = a;
                  effect_args = [as_arg wp];
                  flags = []
                } in
                Util.arrow bs (S.mk_Comp c)
              | _ -> failwith "" in

          (* printfn "Checked action %s against type %s\n" *)
          (*         (Print.term_to_string act_defn) *)
          (*         (Print.term_to_string (N.normalize [N.Beta] env act_typ)); *)
          let univs, act_defn = TcUtil.generalize_universes env act_defn in
          let act_typ = N.normalize [N.Beta] env act_typ in
          {act with
              action_univs=univs;
              action_defn=act_defn;
              action_typ =act_typ } in
        ed.actions |> List.map check_action in
      repr, bind_repr, return_repr, actions
  in

  //generalize and close
  let t = U.arrow ed.binders (S.mk_Total ed.signature) in
  let (univs, t) = TcUtil.generalize_universes env0 t in
  let signature = match effect_params, (SS.compress t).n with
    | [], _ -> t
    | _, Tm_arrow(_, c) -> Util.comp_result c
    | _ -> failwith "Impossible" in
  let close n ts =
    let ts = SS.close_univ_vars_tscheme univs (SS.close_tscheme effect_params ts) in
    // We always close [bind_repr], even though it may be [Tm_unknown]
    // (non-reifiable, non-reflectable effect)
    let m = List.length (fst ts) in
    if n >= 0 && not (is_unknown (snd ts)) && m <> n
    then begin
        let error = if m < n then "not universe-polymorphic enough" else "too universe-polymorphic" in
        failwith (Util.format3
                  "The effect combinator is %s (n=%s) (%s)"
                  error
                  (string_of_int n)
                  (Print.tscheme_to_string ts))
    end ;
    ts in
  let close_action act =
    let univs, defn = close (-1) (act.action_univs, act.action_defn) in
    let univs', typ = close (-1) (act.action_univs, act.action_typ) in
    assert (List.length univs = List.length univs');
    { act with
        action_univs=univs;
        action_defn=defn;
        action_typ=typ; } in
  let nunivs = List.length univs in
  assert (List.length effect_params > 0 || nunivs = 1);
  let ed = { ed with
      univs       = univs
    ; binders     = effect_params
    ; signature   = signature
    ; ret_wp      = close 0 return_wp
    ; bind_wp     = close 1 bind_wp
    ; if_then_else= close 0 if_then_else
    ; ite_wp      = close 0 ite_wp
    ; stronger    = close 0 stronger
    ; close_wp    = close 1 close_wp
    ; assert_p    = close 0 assert_p
    ; assume_p    = close 0 assume_p
    ; null_wp     = close 0 null_wp
    ; trivial     = close 0 trivial_wp
    ; repr        = (snd (close 0 ([], repr)))
    ; return_repr = close 0 return_repr
    ; bind_repr   = close 1 bind_repr
    ; actions     = List.map close_action actions} in

  if Env.debug env Options.Low
  || Env.debug env <| Options.Other "ED"
  then Util.print_string (Print.eff_decl_to_string false ed);
  ed


and cps_and_elaborate env ed =
  // Using [STInt: a:Type -> Effect] as an example...
  let effect_binders_un, signature_un = SS.open_term ed.binders ed.signature in
  // [binders] is the empty list (for [ST (h: heap)], there would be one binder)
  let effect_binders, env, _ = tc_tparams env effect_binders_un in
  // [signature] is a:Type -> effect
  let signature, _ = tc_trivial_guard env signature_un in
  // We will open binders through [open_and_check]

  let effect_binders = List.map (fun (bv, qual) ->
    { bv with sort = N.normalize [ N.EraseUniverses ] env bv.sort }, qual
  ) effect_binders in

  // Every combinator found in the effect declaration is parameterized over
  // [binders], then [a]. This is a variant of [open_effect_signature] where we
  // just extract the binder [a].
  let a, effect_marker =
    // TODO: more stringent checks on the shape of the signature; better errors
    match (SS.compress signature_un).n with
    | Tm_arrow ([(a, _)], effect_marker) ->
        a, effect_marker
    | _ ->
        failwith "bad shape for effect-for-free signature"
  in

  (* TODO : having "_" as a variable name can create a really strange shadowing
            behaviour between uu___ variables in the tcterm ; needs to be investigated *)
  let a =
      if S.is_null_bv a
      then S.gen_bv "a" (Some (S.range_of_bv a)) a.sort
      else a
  in

  let open_and_check t =
    let subst = SS.opening_of_binders effect_binders in
    let t = SS.subst subst t in
    let t, comp, _ = tc_term env t in
    t, comp
  in
  let mk x = mk x None signature.pos in

  // TODO: check that [_comp] is [Tot Type]
  let repr, _comp = open_and_check ed.repr in
  if Env.debug env (Options.Other "ED") then
    Util.print1 "Representation is: %s\n" (Print.term_to_string repr);

  let dmff_env = DMFF.empty env (tc_constant Range.dummyRange) in
  let wp_type = DMFF.star_type dmff_env repr in
  let wp_type = recheck_debug "*" env wp_type in
  let wp_a = N.normalize [ N.Beta ] env (mk (Tm_app (wp_type, [ (S.bv_to_name a, S.as_implicit false) ]))) in

  // Building: [a -> wp a -> Effect]
  let effect_signature =
    let binders = [ (a, S.as_implicit false); S.gen_bv "dijkstra_wp" None wp_a |> S.mk_binder ] in
    let binders = close_binders binders in
    mk (Tm_arrow (binders, effect_marker))
  in
  let effect_signature = recheck_debug "turned into the effect signature" env effect_signature in

  let sigelts = ref [] in
  let mk_lid name: lident =
    lid_of_path (path_of_text (text_of_lid ed.mname ^ "_" ^ name)) Range.dummyRange
  in

  // TODO: we assume that reading the top-level definitions in the order that
  // they come in the effect definition is enough... probably not
  let elaborate_and_star dmff_env item =
    let u_item, item = item in
    // TODO: assert no universe polymorphism
    let item, item_comp = open_and_check item in
    if not (Util.is_total_lcomp item_comp) then
      raise (Err (Util.format2 "Computation for [%s] is not total : %s !" (Print.term_to_string item) (Print.lcomp_to_string item_comp)));
    let item_t, item_wp, item_elab = DMFF.star_expr dmff_env item in
    let item_wp = recheck_debug "*" env item_wp in
    let item_elab = recheck_debug "_" env item_elab in
    dmff_env, item_t, item_wp, item_elab
  in

  let dmff_env, _, bind_wp, bind_elab = elaborate_and_star dmff_env ed.bind_repr in
  let dmff_env, _, return_wp, return_elab = elaborate_and_star dmff_env ed.return_repr in

  let lift_from_pure_wp =
      match (SS.compress return_wp).n with
      | Tm_abs (b1 :: b2 :: bs, body, what) ->
          let b1,b2, body =
              match SS.open_term [b1 ; b2] (U.abs bs body None) with
                  | [b1 ; b2], body -> b1, b2, body
                  | _ -> failwith "Impossible : open_term not preserving binders arity"
          in
          // WARNING : pushing b1 and b2 in env might break the well-typedness invariant
          let env0 = push_binders (DMFF.get_env dmff_env) [b1 ; b2] in
          let wp_b1 = N.normalize [ N.Beta ] env0 (mk (Tm_app (wp_type, [ (S.bv_to_name (fst b1), S.as_implicit false) ]))) in
          let bs, body, what' = U.abs_formals <|  N.eta_expand_with_type body (Util.unascribe wp_b1) in
          (* TODO : Should check that what' is Tot Type0 *)
          let t2 = (fst b2).sort in
          let pure_wp_type = DMFF.double_star t2 in
          let wp = S.gen_bv "wp" None pure_wp_type in
          // fun b1 wp -> (fun bs@bs'-> wp (fun b2 -> body $$ Type0) $$ Type0) $$ wp_a
          let body = mk_Tm_app (S.bv_to_name wp) [U.abs [b2] body what', None] None Range.dummyRange in
          U.abs ([ b1; S.mk_binder wp ]) (U.abs (bs) body what) (Some (Inr (Const.effect_GTot_lid, [])))
      | _ ->
          failwith "unexpected shape for return"
  in

  let return_wp =
    // TODO: fix [tc_eff_decl] to deal with currying
    match (SS.compress return_wp).n with
    | Tm_abs (b1 :: b2 :: bs, body, what) ->
        U.abs ([ b1; b2 ]) (U.abs bs body what) (Some (Inr (Const.effect_GTot_lid, [])))
    | _ ->
        failwith "unexpected shape for return"
  in
  let bind_wp =
    match (SS.compress bind_wp).n with
    | Tm_abs (binders, body, what) ->
        // TODO: figure out how to deal with ranges
        let r = S.lid_as_fv Const.range_lid (S.Delta_defined_at_level 1) None in
        U.abs ([ S.null_binder (mk (Tm_fvar r)) ] @ binders) body what
    | _ ->
        failwith "unexpected shape for bind"
  in

  let apply_close t =
    if List.length effect_binders = 0 then
      t
    else
      close effect_binders (mk (Tm_app (t, snd (U.args_of_binders effect_binders))))
  in
  let register name item =
    let sigelt, fv = TcUtil.mk_toplevel_definition env (mk_lid name) (U.abs effect_binders item None) in
    sigelts := sigelt :: !sigelts;
    fv
  in
  let lift_from_pure_wp = register "lift_from_pure" lift_from_pure_wp in

  // we do not expect the return_elab to verify, since that may require internalizing monotonicity of WPs (i.e. continuation monad)
  let return_wp = register "return_wp" return_wp in
  sigelts := Sig_pragma (SetOptions "--admit_smt_queries true", Range.dummyRange) :: !sigelts;
  let return_elab = register "return_elab" return_elab in
  sigelts := Sig_pragma (SetOptions "--admit_smt_queries false", Range.dummyRange) :: !sigelts;

  // we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
  let bind_wp = register "bind_wp" bind_wp in
  sigelts := Sig_pragma (SetOptions "--admit_smt_queries true", Range.dummyRange) :: !sigelts;
  let bind_elab = register "bind_elab" bind_elab in
  sigelts := Sig_pragma (SetOptions "--admit_smt_queries false", Range.dummyRange) :: !sigelts;

  let dmff_env, actions = List.fold_left (fun (dmff_env, actions) action ->
    // We need to reverse-engineer what tc_eff_decl wants here...
    let dmff_env, action_t, action_wp, action_elab =
      elaborate_and_star dmff_env (action.action_univs, action.action_defn)
    in
    let name = action.action_name.ident.idText in
    let action_typ_with_wp = DMFF.trans_F dmff_env action_t action_wp in
    let action_elab = register (name ^ "_elab") action_elab in
    let action_typ_with_wp = register (name ^ "_complete_type") action_typ_with_wp in
    dmff_env, { action with action_defn = apply_close action_elab; action_typ = apply_close action_typ_with_wp } :: actions
  ) (dmff_env, []) ed.actions in
  let actions = List.rev actions in

  let repr =
    let wp = S.gen_bv "wp_a" None wp_a in
    let binders = [ S.mk_binder a; S.mk_binder wp ] in
    U.abs binders (DMFF.trans_F dmff_env (mk (Tm_app (repr, [ S.bv_to_name a, S.as_implicit false ]))) (S.bv_to_name wp)) None
  in
  let repr = recheck_debug "FC" env repr in
  let repr = register "repr" repr in

  (* We are still lacking a principled way to generate pre/post condition *)
  (* Current algorithm takes the type of wps : fun (a: Type) -> (t1 -> t2 ... -> tn -> Type0) *)
  (* Checks that there is exactly one ti containing the type variable a and returns that ti *)
  (* as type of postconditons, the rest as type of preconditions *)
  let pre, post =
    match (unascribe <| SS.compress wp_type).n with
    | Tm_abs (type_param :: effect_param, arrow, _) ->
        let type_param , effect_param, arrow =
            match SS.open_term (type_param :: effect_param) arrow with
                | (b :: bs), body -> b, bs, body
                | _ -> failwith "Impossible : open_term nt preserving binders arity"
        in
        begin match (unascribe <| SS.compress arrow).n with
        | Tm_arrow (wp_binders, c) ->
            let wp_binders, c = SS.open_comp wp_binders c in
            let pre_args, post_args =
                List.partition (fun (bv,_) ->
                  Free.names bv.sort |> Util.set_mem (fst type_param) |> not
                ) wp_binders
            in
            let post = match post_args with
                | [post] -> post
                | _ -> failwith (Util.format1 "Impossible: multiple post candidates %s" (Print.term_to_string arrow))
            in
            // Pre-condition does not mention the return type; don't close over it
            U.arrow pre_args c,
            // Post-condition does, however!
            U.abs (type_param :: effect_param) (fst post).sort None
        | _ ->
            failwith (Util.format1 "Impossible: pre/post arrow %s" (Print.term_to_string arrow))
        end
    | _ ->
        failwith (Util.format1 "Impossible: pre/post abs %s" (Print.term_to_string wp_type))
  in
  // Desugaring is aware of these names and generates references to them when
  // the user writes something such as [STINT.repr]
  ignore (register "pre" pre);
  ignore (register "post" post);
  ignore (register "wp" wp_type);

  let ed = { ed with
    signature = close effect_binders effect_signature;
    repr = apply_close repr;
    ret_wp = [], apply_close return_wp;
    bind_wp = [], apply_close bind_wp;
    return_repr = [], apply_close return_elab;
    bind_repr = [], apply_close bind_elab;
    actions = actions; // already went through apply_close
    binders = close_binders effect_binders
  } in


  // Generate the missing combinators.
  let sigelts', ed = DMFF.gen_wps_for_free env effect_binders a wp_a ed in
  if Env.debug env (Options.Other "ED") then
    Util.print_string (Print.eff_decl_to_string true ed);

  let lift_from_pure_opt =
    if List.length effect_binders = 0 then begin
      // Won't work with parameterized effect
      let lift_from_pure = {
          source = Const.effect_PURE_lid;
          target = ed.mname ;
          lift_wp = Some ([], apply_close lift_from_pure_wp) ;
          lift = None //Some ([], apply_close return_elab)
      } in
      Some (Sig_sub_effect (lift_from_pure, Range.dummyRange))
    end else None
  in

  List.rev !sigelts @ sigelts', ed, lift_from_pure_opt


and tc_lex_t env ses quals lids =
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

and tc_assume (env:env) (lid:lident) (phi:formula) (quals:list<qualifier>) (r:Range.range) :sigelt =
    let env = Env.set_range env r in
    let k, _ = U.type_u() in
    let phi = tc_check_trivial_guard env phi k |> N.normalize [N.Beta; N.Eager_unfolding] env in
    TcUtil.check_uvars r phi;
    Sig_assume(lid, phi, quals, r)

and tc_inductive env ses quals lids =
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
                                * guard_t        (* constraints on implicit variables *)
                                = match s with
       | Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> //the only valid qual is Private
         assert (uvs = []);
         warn_positivity tc r;
 (*open*)let tps, k = SS.open_term tps k in
         let tps, env_tps, guard_params, us = tc_binders env tps in
         let indices, t = Util.arrow_formals k in
         let indices, env', guard_indices, us' = tc_binders env_tps indices in
         let t, guard =
             let t, _, g = tc_tot_or_gtot_term env' t in
             t, Rel.discharge_guard env' (Rel.conj_guard guard_params (Rel.conj_guard guard_indices g)) in
         let k = Util.arrow indices (S.mk_Total t) in
         let t_type, u = U.type_u() in
         Rel.force_trivial_guard env' (Rel.teq env' t t_type);

(*close*)let t_tc = Util.arrow (tps@indices) (S.mk_Total t) in
         let tps = SS.close_binders tps in
         let k = SS.close tps k in
         let fv_tc = S.lid_as_fv tc Delta_constant None in
         Env.push_let_binding env_tps (Inr fv_tc) ([], t_tc),
         Sig_inductive_typ(tc, [], tps, k, mutuals, data, quals, r),
         u,
         guard

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
         let result, res_lcomp = tc_trivial_guard env' result in
         (match (SS.compress res_lcomp.res_typ).n with
         | Tm_type _ -> ()
         | ty -> raise (Error(Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                        (Print.term_to_string result)
                                        (Print.term_to_string (res_lcomp.res_typ)), r)));
         let head, _ = Util.head_and_args result in
         let _ = match (SS.compress head).n with
            | Tm_fvar fv when S.fv_eq_lid fv tc_lid -> ()
            | _ -> raise (Error(Util.format2 "Expected a constructor of type %s; got %s"
                                        (Print.lid_to_string tc_lid)
                                        (Print.term_to_string head), r)) in
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
    if datas |> Util.for_some (function Sig_datacon _ -> false | _ -> true)
    then raise (Error("Mutually defined type contains a non-inductive element", Env.get_range env));
    let env0 = env in

    (* Check each tycon *)
    let env, tcs, g = List.fold_right (fun tc (env, all_tcs, g)  ->
            let env, tc, tc_u, guard = tc_tycon env tc in
            let g' = Rel.universe_inequality S.U_zero tc_u in
            if Env.debug env Options.Low
            then Util.print1 "Checked inductive: %s\n" (Print.sigelt_to_string tc);
            env, (tc, tc_u)::all_tcs, Rel.conj_guard g (Rel.conj_guard guard g'))
        tys
        (env, [], Rel.trivial_guard) in

    (* Check each datacon *)
    let datas, g = List.fold_right (fun se (datas, g) ->
            let data, g' = tc_data env tcs se in
            data::datas, Rel.conj_guard g g')
        datas
        ([], g) in

    let tcs, datas = generalize_and_inst_within env0 g (List.map fst tcs) datas in
    let sig_bndle = Sig_bundle(tcs@datas, quals, lids, Env.get_range env0) in

    //generate hasEq predicate for this inductive

    let datacon_typ (data:sigelt) :term = match data with
        | Sig_datacon (_, _, t, _, _, _, _, _) -> t
        | _                                    -> failwith "Impossible!"
    in

    let dr = Range.dummyRange in

    //tcs is the list of type constructors, datas is the list of data constructors

    let optimized_haseq_scheme (_:unit) :list<sigelt> =
        //this is the folding function for tcs
        //usubst and us are the universe variables substitution and universe names, we open each type constructor type, and data constructor type with these
        //in the type of the accumulator:
          //list<lident * term> is the list of type constructor lidents and formulas of haseq axioms we are accumulating
          //env is the environment in which the next two terms are well-formed (e.g. data constructors are dependent function types, so they may refer to their arguments)
          //term is the lhs of the implication for soundness formula
          //term is the soundness condition derived from all the data constructors of this type
        let haseq_ty usubst us acc ty =
            let lid, bs, t, d_lids =
                match ty with
                    | Sig_inductive_typ (lid, _, bs, t, _, d_lids, _, _) -> lid, bs, t, d_lids
                    | _                                                  -> failwith "Impossible!"
            in

             //apply usubt to bs
            let bs = SS.subst_binders usubst bs in
            //apply usubst to t, but first shift usubst -- is there a way to apply usubst to bs and t together ?
            let t = SS.subst (SS.shift_subst (List.length bs) usubst) t in
            //open t with binders bs
            let bs, t = SS.open_term bs t in
            //get the index binders, if any
            let ibs =
                match (SS.compress t).n with
                    | Tm_arrow (ibs, _) -> ibs
                    | _                 -> []
            in
            //open the ibs binders
            let ibs = SS.open_binders ibs in
            //term for unapplied inductive type, making a Tm_uinst, otherwise there are unresolved universe variables, may be that's fine ?
            let ind = mk_Tm_uinst (S.fvar lid Delta_constant None) (List.map (fun u -> U_name u) us) in
            //apply the bs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
            let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) bs) None dr in
            //apply the ibs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
            let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) ibs) None dr in
            //haseq of ind
            let haseq_ind = mk_Tm_app U.t_haseq [S.as_arg ind] None dr in
            //haseq of all binders in bs, we will add only those binders x:t for which t <: Type u for some fresh universe variable u
            //we want to avoid the case of binders such as (x:nat), as hasEq x is not well-typed
            let bs' = List.filter (fun b ->
                let _, en, _, _ = acc in
                //false means don't use SMT solver
                let opt = Rel.try_subtype' en (fst b).sort  (fst (type_u ())) false in
                //is this criteria for success/failure ok ?
                match opt with
                    | None   -> false
                    | Some _ -> true
            ) bs in
            let haseq_bs = List.fold_left (fun (t:term) (b:binder) -> U.mk_conj t (mk_Tm_app U.t_haseq [S.as_arg (S.bv_to_name (fst b))] None dr)) U.t_true bs' in
            //implication
            let fml = U.mk_imp haseq_bs haseq_ind in
            //attach pattern -- is this the right place ?
            let fml = { fml with n = Tm_meta (fml, Meta_pattern [[S.as_arg haseq_ind]]) } in
            //fold right with ibs, close and add a forall b
	        //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
            let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None dr) ibs fml in
            //fold right with bs, close and add a forall b
	        //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
            let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None dr) bs fml in
            //so now fml is the haseq axiom we want to generate

            //onto the soundness condition for the above axiom
            //this is the soundness guard
            let guard = U.mk_conj haseq_bs fml in

            //now work on checking the soundness of this formula
            //split acc
            let l_axioms, env, guard', cond' = acc in

            //push universe variables, bs, and ibs, universe variables are pushed at the top level below
            let env = Env.push_binders env bs in
            let env = Env.push_binders env ibs in

            //now generate the soundness condition by iterating over the data constructors
            //get the data constructors for this type
            let t_datas = List.filter (fun s ->
                match s with
                    | Sig_datacon (_, _, _, t_lid, _, _, _, _) -> t_lid = lid
                    | _                                        -> failwith "Impossible"
            ) datas in


            //soundness condition for this data constructor
            let haseq_data data =
                let dt = datacon_typ data in
                //apply the universes substitution to dt
                let dt = SS.subst usubst dt in
                match (SS.compress dt).n with
                    | Tm_arrow (dbs, _) ->
                        //filter out the inductive type parameters, dbs are the remaining binders
                        let dbs = snd (List.splitAt (List.length bs) dbs) in
                        //substitute bs into dbs
                        let dbs = SS.subst_binders (SS.opening_of_binders bs) dbs in
                        //open dbs
                        let dbs = SS.open_binders dbs in
                        //fold on dbs, add haseq of its sort to the guard
                        let cond = List.fold_left (fun (t:term) (b:binder) ->
                            let haseq_b = mk_Tm_app U.t_haseq [S.as_arg (fst b).sort] None dr in
                            //label the haseq predicate so that we get a proper error message if the assertion fails
                            let sort_range = (fst b).sort.pos in
                            let haseq_b = Util.label
                                (Util.format1 "Failed to prove that the type '%s' supports decidable equality because of this argument; add the 'noeq' qualifier"
                                      (Print.term_to_string ind))
                                sort_range
                                haseq_b in
                            U.mk_conj t haseq_b) U.t_true dbs in

            	        //fold right over dbs and add a forall for each binder in dbs
                        List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None dr) dbs cond
                    | _                -> U.t_true
            in

            //fold over t_datas
            let cond = List.fold_left (fun acc d -> U.mk_conj acc (haseq_data d)) U.t_true t_datas in

            //return new accumulator
            let axiom_lid = lid_of_ids (lid.ns @ [(id_of_text (lid.ident.idText ^ "_haseq"))]) in
            l_axioms @ [axiom_lid, fml], env, U.mk_conj guard' guard, U.mk_conj cond' cond
        in

        let us =
            let ty = List.hd tcs in
            match ty with
                | Sig_inductive_typ (_, us, _, _, _, _, _, _) -> us
                | _                                           -> failwith "Impossible!"
        in
        let usubst, us = SS.univ_var_opening us in

        //we need the sigbundle for the inductive to be in the type environment
        let env = Env.push_sigelt env0 sig_bndle in
        env.solver.push "haseq";
        env.solver.encode_sig env sig_bndle;
        let env = Env.push_univ_vars env us in

        let axioms, env, guard, cond = List.fold_left (haseq_ty usubst us) ([], env, U.t_true, U.t_true) tcs in

        let phi = U.mk_imp guard cond in
        let phi, _ = tc_trivial_guard env phi in
        let _ =
            //is this inline with verify_module ?
            if Env.should_verify env then
                Rel.force_trivial_guard env (Rel.guard_of_guard_formula (NonTrivial phi))
            else ()
        in

        //create Sig_assume for the axioms
        let ses = List.fold_left (fun (l:list<sigelt>) (lid, fml) ->
            let se = tc_assume env lid fml [] dr in
            //se has free universe variables in it, TODO: fix it by making Sig_assume a type scheme
            l @ [se]
        ) [] axioms in

        env.solver.pop "haseq";
        ses
    in

    let unoptimized_haseq_scheme (_:unit) :list<sigelt> =
        //TODO: perhaps make it a map ?
        let mutuals = List.map (fun ty ->
            match ty with
                | Sig_inductive_typ (lid, _, _, _, _, _, _, _) -> lid
                | _                                            -> failwith "Impossible!") tcs
        in

        //tcs is the list of type constructors, datas is the list of data constructors

        //this is the folding function for tcs
        //usubst and us are the universe variables substitution and universe names, we open each type constructor type, and data constructor type with these
        //the accumulator is the formula that we are building, for each type constructor, we add a conjunct to it
        let haseq_ty usubst us acc ty =
            let lid, bs, t, d_lids =
                match ty with
                    | Sig_inductive_typ (lid, _, bs, t, _, d_lids, _, _) -> lid, bs, t, d_lids
                    | _                                                  -> failwith "Impossible!"
            in

             //apply usubt to bs
            let bs = SS.subst_binders usubst bs in
            //apply usubst to t, but first shift usubst -- is there a way to apply usubst to bs and t together ?
            let t = SS.subst (SS.shift_subst (List.length bs) usubst) t in
            //open t with binders bs
            let bs, t = SS.open_term bs t in
            //get the index binders, if any
            let ibs =
                match (SS.compress t).n with
                    | Tm_arrow (ibs, _) -> ibs
                    | _                 -> []
            in
            //open the ibs binders
            let ibs = SS.open_binders ibs in
            //term for unapplied inductive type, making a Tm_uinst, otherwise there are unresolved universe variables, may be that's fine ?
            let ind = mk_Tm_uinst (S.fvar lid Delta_constant None) (List.map (fun u -> U_name u) us) in
            //apply the bs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
            let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) bs) None dr in
            //apply the ibs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
            let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) ibs) None dr in
            //haseq of ind applied to all bs and ibs
            let haseq_ind = mk_Tm_app U.t_haseq [S.as_arg ind] None dr in

            //identify if the type t is a mutually defined type
            let rec is_mutual t =  //TODO: this should handle more cases
                match (SS.compress t).n with
                    | Tm_fvar fv         -> List.existsb (fun lid -> lid_equals lid fv.fv_name.v) mutuals
                    | Tm_uinst (t', _)   -> is_mutual t'
                    | Tm_refine (bv, t') -> is_mutual bv.sort
                    | Tm_app (t', args)  -> if is_mutual t' then true else exists_mutual (List.map fst args)
                    | Tm_meta (t', _)    -> is_mutual t'
                    | _                  -> false

            and exists_mutual = function
                | [] -> false
                | hd::tl -> is_mutual hd || exists_mutual tl
            in

            //folding function for t_datas
            let haseq_data acc data =
                let dt = datacon_typ data in
                //apply the universes substitution to dt
                let dt = SS.subst usubst dt in
                match (SS.compress dt).n with
                    | Tm_arrow (dbs, _) ->
                        //filter out the inductive type parameters, dbs are the remaining binders
                        let dbs = snd (List.splitAt (List.length bs) dbs) in
                        //substitute bs into dbs
                        let dbs = SS.subst_binders (SS.opening_of_binders bs) dbs in
                        //open dbs
                        let dbs = SS.open_binders dbs in
                        //fold on dbs, add haseq of its sort to the guard
                        //if the sort is a mutual, guard its hasEq with the hasEq of the current type constructor
                        //cond is the conjunct of the hasEq of all the data constructor arguments
                        let cond = List.fold_left (fun (t:term) (b:binder) ->
                            let sort = (fst b).sort in
                            let haseq_sort = mk_Tm_app U.t_haseq [S.as_arg (fst b).sort] None dr in
                            let haseq_sort = if is_mutual sort then U.mk_imp haseq_ind haseq_sort else haseq_sort in
                            U.mk_conj t haseq_sort) U.t_true dbs
                        in

                        //fold right with dbs, close and add a forall b
	                    //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
                        let cond = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None dr) dbs cond in

                        //new accumulator is old one /\ cond
                        U.mk_conj acc cond
                    | _                -> acc
            in

            //filter out data constructors for this type constructor
            let t_datas = List.filter (fun s ->
                match s with
                    | Sig_datacon (_, _, _, t_lid, _, _, _, _) -> t_lid = lid
                    | _                                        -> failwith "Impossible"
            ) datas in

            //fold over t_datas
            let data_cond = List.fold_left haseq_data U.t_true t_datas in

            //make the implication
            let fml = U.mk_imp data_cond haseq_ind in

            //attach pattern -- is this the right place ?
            let fml = { fml with n = Tm_meta (fml, Meta_pattern [[S.as_arg haseq_ind]]) } in

            //fold right with ibs, close and add a forall b
	        //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
            let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None dr) ibs fml in
            //fold right with bs, close and add a forall b
	        //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
            let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None dr) bs fml in

            //new accumulator is old accumulator /\ fml
            U.mk_conj acc fml
        in

        let lid, us =
            let ty = List.hd tcs in
            match ty with
                | Sig_inductive_typ (lid, us, _, _, _, _, _, _) -> lid, us
                | _                                           -> failwith "Impossible!"
        in
        let usubst, us = SS.univ_var_opening us in

        let fml = List.fold_left (haseq_ty usubst us) U.t_true tcs in

        let env = Env.push_sigelt env0 sig_bndle in
        env.solver.push "haseq";

        env.solver.encode_sig env sig_bndle;
        let env = Env.push_univ_vars env us in
        let se = tc_assume env (lid_of_ids (lid.ns @ [(id_of_text (lid.ident.idText ^ "_haseq"))])) fml [] dr in

        env.solver.pop "haseq";
        [se]
    in

    //skip logical connectives types in prims, tcs is bound to the inductive type, caller ensures its length is > 0
    let skip_prims_type (_:unit) :bool =
        let lid =
            let ty = List.hd tcs in
            match ty with
                | Sig_inductive_typ (lid, _, _, _, _, _, _, _) -> lid
                | _                                            -> failwith "Impossible"
        in
        //these are the prims type we are skipping
        let types_to_skip = [ "c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"; ] in
        List.existsb (fun s -> s = lid.ident.idText) types_to_skip
    in

    let is_noeq = List.existsb (fun q -> q = Noeq) quals in

    if ((List.length tcs = 0) || ((lid_equals env.curmodule Const.prims_lid) && skip_prims_type ()) || is_noeq) then [sig_bndle]
    else
        let is_unopteq = List.existsb (fun q -> q = Unopteq) quals in
        let ses = if is_unopteq then unoptimized_haseq_scheme () else optimized_haseq_scheme () in
        (Sig_bundle(tcs@datas, quals, lids, Env.get_range env0))::ses

and tc_decl env se: list<sigelt> * _ =
    let env = set_hint_correlator env se in
    TcUtil.check_sigelt_quals env se;
    match se with
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
      [se], Env.push_sigelt env se

    | Sig_bundle(ses, quals, lids, r) ->
      let env = Env.set_range env r in
      let ses = tc_inductive env ses quals lids  in
      let env = List.fold_left (fun env' se -> Env.push_sigelt env' se) env ses in
      ses, env

    | Sig_pragma(p, r) ->
       let set_options t s = match Options.set_options t s with
            | Getopt.Success -> ()
            | Getopt.Help  -> raise (Error ("Failed to process pragma: use 'fstar --help' to see which options are available", r))
            | Getopt.Error s -> raise (Error ("Failed to process pragma: " ^s, r)) in
        begin match p with
            | SetOptions o ->
                set_options Options.Set o;
                [se], env
            | ResetOptions sopt ->
                Options.restore_cmd_line_options false |> ignore;
                let _ = match sopt with
                    | None -> ()
                    | Some s -> set_options Options.Reset s in
                env.solver.refresh();
                [se], env
        end


    | Sig_new_effect_for_free _ ->
        failwith "impossible"

    | Sig_new_effect(ne, r) ->
      let ne = tc_eff_decl env ne in
      let se = Sig_new_effect(ne, r) in
      let env = Env.push_sigelt env se in
      let env, ses = ne.actions |> List.fold_left (fun (env, ses) a ->
          let se_let = Util.action_as_lb a in
          Env.push_sigelt env se_let, se_let::ses) (env, [se]) in
      [se], env

    | Sig_sub_effect(sub, r) ->
      let ed_src = Env.get_effect_decl env sub.source in
      let ed_tgt = Env.get_effect_decl env sub.target in
      let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
      let b, wp_b_tgt = monad_signature env sub.target (Env.lookup_effect_lid env sub.target) in
      let wp_a_tgt    = SS.subst [NT(b, S.bv_to_name a)] wp_b_tgt in
      let expected_k  = Util.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
      let repr_type eff_name a wp =
        let no_reify l = raise (Error(Util.format1 "Effect %s cannot be reified" l.str, Env.get_range env)) in
        match Env.effect_decl_opt env eff_name with
        | None -> no_reify eff_name
        | Some ed ->
            let repr = Env.inst_effect_fun_with [U_unknown] env ed ([], ed.repr) in
            if not (ed.qualifiers |> List.contains Reifiable) then
              no_reify eff_name
            else
              mk (Tm_app(repr, [as_arg a; as_arg wp])) None (Env.get_range env) in
      let lift, lift_wp =
        match sub.lift, sub.lift_wp with
        | None, None ->
            failwith "Impossible"
        | lift, Some (_, lift_wp) ->
            (* Covers both the "classic" format and the reifiable case. *)
            lift, check_and_gen env lift_wp expected_k
        | Some (what, lift), None ->
            let dmff_env = DMFF.empty env (tc_constant Range.dummyRange) in
            let _, lift_wp, lift_elab = DMFF.star_expr dmff_env lift in
            let _ = recheck_debug "lift-wp" env lift_wp in
            let _ = recheck_debug "lift-elab" env lift_elab in
            Some ([], lift_elab), ([], lift_wp)
      in
      let lax = env.lax in
      let env = {env with lax=true} in //we do not expect the lift to verify, since that requires internalizing monotonicity of WPs
      let lift = match lift with
        | None -> None
        | Some (_, lift) ->
          let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
          let wp_a = S.new_bv None wp_a_src in
          let a_typ = S.bv_to_name a in
          let wp_a_typ = S.bv_to_name wp_a in
          let repr_f = repr_type sub.source a_typ wp_a_typ in
          let repr_result =
            let lift_wp = N.normalize [N.EraseUniverses; N.AllowUnboundUniverses] env (snd lift_wp) in
            let lift_wp_a = mk (Tm_app(lift_wp, [as_arg a_typ; as_arg wp_a_typ])) None (Env.get_range env) in
            repr_type sub.target a_typ lift_wp_a in
          let expected_k =
            Util.arrow [S.mk_binder a; S.mk_binder wp_a; S.null_binder repr_f]
                        (S.mk_Total repr_result) in
//          printfn "LIFT: Expected type for lift = %s\n" (Print.term_to_string expected_k);
          let expected_k, _, _ =
            tc_tot_or_gtot_term env expected_k in
//          printfn "LIFT: Checking %s against expected type %s\n" (Print.term_to_string lift) (Print.term_to_string expected_k);
          let lift = check_and_gen env lift expected_k in
//          printfn "LIFT: Checked %s against expected type %s\n" (Print.tscheme_to_string lift) (Print.term_to_string expected_k);
          Some lift in
      // Restore the proper lax flag!
      let env = { env with lax = lax } in
      let sub = {sub with lift_wp=Some lift_wp; lift=lift} in
      let se = Sig_sub_effect(sub, r) in
      let env = Env.push_sigelt env se in
      [se], env

    | Sig_effect_abbrev(lid, uvs, tps, c, tags, flags, r) ->
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
      if List.length uvs <> 1
      && not (Ident.lid_equals lid Const.effect_Lemma_lid)
      then (let _, t = Subst.open_univ_vars uvs t in
            raise (Error(Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                    (Print.lid_to_string lid)
                                    (List.length uvs |> Util.string_of_int)
                                    (Print.term_to_string t), r)));
      let se = Sig_effect_abbrev(lid, uvs, tps, c, tags, flags, r) in
      let env = Env.push_sigelt env0 se in
      [se], env

    | Sig_declare_typ(lid, uvs, t, quals, r) -> //NS: No checks on the qualifiers?
      let env = Env.set_range env r in
      assert (uvs = []);
      let uvs, t = check_and_gen env t (fst (U.type_u())) in
      let se = Sig_declare_typ(lid, uvs, t, quals, r) in
      let env = Env.push_sigelt env se in
      [se], env

    | Sig_assume(lid, phi, quals, r) ->
      let se = tc_assume env lid phi quals r in
      let env = Env.push_sigelt env se in
      [se], env

    | Sig_main(e, r) ->
      let env = Env.set_range env r in
      let env = Env.set_expected_typ env Common.t_unit in
      let e, c, g1 = tc_term env e in
      let e, _, g = check_expected_effect env (Some (Util.ml_comp Common.t_unit r)) (e, c.comp()) in
      Rel.force_trivial_guard env (Rel.conj_guard g1 g);
      let se = Sig_main(e, r) in
      let env = Env.push_sigelt env se in
      [se], env

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
        | None -> [Visible_default]
        | Some q ->
          if q |> Util.for_some (function Irreducible | Visible_default | Unfold_for_unification_and_vcgen -> true | _ -> false)
          then q
          else Visible_default::q in //the default visibility for a let binding is Unfoldable

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
      [se], env


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

    | Sig_bundle(ses, quals, _, r) ->
      if is_abstract quals
      then List.fold_right (fun se (out, hidden) -> match se with
            | Sig_inductive_typ(l, us, bs, t, _, _, quals, r) ->
              let dec = Sig_declare_typ(l, us, U.arrow bs (S.mk_Total t), Assumption::New::quals, r) in
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
  let process_one_decl (ses, exports, env, hidden) se =
    if Env.debug env Options.Low
    then Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" (Print.sigelt_to_string se);

    let ses', env = tc_decl env se  in

    if (Options.log_types()) || Env.debug env <| Options.Other "LogTypes"
    then Util.print1 "Checked: %s\n" (List.fold_left (fun s se -> s ^ (Print.sigelt_to_string se) ^ "\n") "" ses');

    List.iter (fun se -> env.solver.encode_sig env se) ses';

    let exported, hidden = List.fold_left (fun (le, lh) se -> let tup = for_export hidden se in List.rev_append (fst tup) le, List.rev_append (snd tup) lh) ([], []) ses' in
    List.rev_append ses' ses, (List.rev_append exported [])::exports, env, hidden
  in
  let ses, exports, env, _ =
    List.fold_left (fun acc se ->
      match se with
      | Sig_new_effect_for_free(ne, r) ->
          // Let the power of Dijkstra generate everything "for free", then defer
          // the rest of the job to [tc_decl].
          let _, _, env, _ = acc in
          let ses, ne, lift_from_pure_opt = cps_and_elaborate env ne in
          let ses = match lift_from_pure_opt with
                    | Some lift -> ses @ [ Sig_new_effect (ne, r) ; lift ]
                    | None -> ses @ [ Sig_new_effect (ne, r) ]
          in
          List.fold_left process_one_decl acc ses
      | _ ->
          process_one_decl acc se
    ) ([], [], env, []) ses
  in
  List.rev_append ses [], (List.rev_append exports []) |> List.flatten, env

let tc_partial_modul env modul =
  let name = Util.format2 "%s %s"  (if modul.is_interface then "interface" else "module") modul.name.str in
  let msg = "Internals for " ^name in
  let env = {env with Env.is_iface=modul.is_interface;
                      admit=not (Options.should_verify modul.name.str)} in
  env.solver.push msg;
  let env = Env.set_current_module env modul.name in
  let ses, exports, env = tc_decls env modul.declarations in
  {modul with declarations=ses}, exports, env

let tc_more_partial_modul env modul decls =
  let ses, exports, env = tc_decls env decls in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, exports, env

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
open FStar.TypeChecker.Errors
let check_exports env (modul:modul) exports =
    let env = {env with lax=true; lax_universes=true; top_level=true} in
    let check_term lid univs t =
        let univs, t = SS.open_univ_vars univs t in
        if Env.debug (Env.set_current_module env modul.name) <| Options.Other "Exports"
        then Util.print3 "Checking for export %s <%s> : %s\n"
                (Print.lid_to_string lid)
                (univs |> List.map (fun x -> Print.univ_to_string (U_name x)) |> String.concat ", ")
                (Print.term_to_string t);
        let env = Env.push_univ_vars env univs in
        TcTerm.tc_trivial_guard env t |> ignore
    in
    let check_term lid univs t =
        let _ = Errors.message_prefix.set_prefix
                (Util.format2 "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
                        (Print.lid_to_string modul.name)
                        (Print.lid_to_string lid)) in
        check_term lid univs t;
        Errors.message_prefix.clear_prefix()
    in
    let rec check_sigelt = function
        | Sig_bundle(ses, quals, _, _) ->
          if not (quals |> List.contains Private)
          then ses |> List.iter check_sigelt
        | Sig_inductive_typ (l, univs, binders, typ, _, _, _, r) ->
          let t = S.mk (Tm_arrow(binders, S.mk_Total typ)) None r in
          check_term l univs t
        | Sig_datacon(l , univs, t, _, _, _, _, _) ->
          check_term l univs t
        | Sig_declare_typ(l, univs, t, quals, _) ->
          if not (quals |> List.contains Private)
          then check_term l univs t
        | Sig_let((_, lbs), _, _, quals) ->
          if not (quals |> List.contains Private)
          then lbs |> List.iter (fun lb ->
               let fv = right lb.lbname in
               check_term fv.fv_name.v lb.lbunivs lb.lbtyp)
        | Sig_effect_abbrev(l, univs, binders, comp, quals, flags, r) ->
          if not (quals |> List.contains Private)
          then let arrow = S.mk (Tm_arrow(binders, comp)) None r in
               check_term l univs arrow
        | Sig_main _
        | Sig_assume _
        | Sig_new_effect _
        | Sig_new_effect_for_free _
        | Sig_sub_effect _
        | Sig_pragma _ -> ()
    in
    if Ident.lid_equals modul.name Const.prims_lid
    then ()
    else List.iter check_sigelt exports


let finish_partial_modul env modul exports =
  let modul = {modul with exports=exports; is_interface=modul.is_interface} in
  let env = Env.finish_module env modul in
  check_exports env modul exports;
  env.solver.pop ("Ending modul " ^ modul.name.str);
  env.solver.encode_modul env modul;
  env.solver.refresh();
  Options.restore_cmd_line_options true |> ignore;
  modul, env

let tc_modul env modul =
  let modul, non_private_decls, env = tc_partial_modul env modul in
  finish_partial_modul env modul non_private_decls

let check_module env m =
    if Options.debug_any()
    then Util.print2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.lid_to_string m.name);
    let m, env = tc_modul env m in
    if Options.dump_module m.name.str
    then Util.print1 "%s\n" (Print.modul_to_string m);
    m, env
