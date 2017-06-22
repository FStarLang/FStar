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
open FStar.TypeChecker.TcTerm
module S  = FStar.Syntax.Syntax
module SP  = FStar.Syntax.Print
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module BU = FStar.Util //basic util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print
module TcInductive = FStar.TypeChecker.TcInductive



//set the name of the query so that we can correlate hints to source program fragments
let set_hint_correlator env se =
    match Options.reuse_hint_for () with
    | Some l ->
      let lid = Ident.lid_add_suffix (Env.current_module env) l in
      {env with qname_and_index=Some (lid, 0)}

    | None ->
      let lids = U.lids_of_sigelt se in
      let lid = match lids with
            | [] -> Ident.lid_add_suffix (Env.current_module env)
                                         (S.next_id () |> BU.string_of_int)
            | l::_ -> l in
      {env with qname_and_index=Some (lid, 0)}

let log env = (Options.log_types()) &&  not(lid_equals Const.prims_lid (Env.current_module env))

(*****************Type-checking the signature of a module*****************************)

let tc_check_trivial_guard env t k =
  let t, c, g = tc_check_tot_or_gtot_term env t k in
  t.tk := Some c.res_typ.n;
  Rel.force_trivial_guard env g;
  t

// A helper to check that the terms elaborated by DMFF are well-typed
let recheck_debug s env t =
  if Env.debug env (Options.Other "ED") then
    BU.print2 "Term has been %s-transformed to:\n%s\n----------\n" s (Print.term_to_string t);
  let t', _, _ = tc_term env t in
  if Env.debug env (Options.Other "ED") then
    BU.print1 "Re-checked; got:\n%s\n----------\n" (Print.term_to_string t');
  // Return the original term (without universes unification variables);
  // because [tc_eff_decl] will take care of these
  t


let check_and_gen env t k =
    // BU.print1 "\x1b[01;36mcheck and gen \x1b[00m%s\n" (Print.term_to_string t);
    TcUtil.generalize_universes env (tc_check_trivial_guard env t k)

let check_nogen env t k =
    let t = tc_check_trivial_guard env t k in
    [], N.normalize [N.Beta] env t

let monad_signature env m s =
 let fail () = raise (Error(Err.unexpected_signature_for_monad env m s, range_of_lid m)) in
 let s = SS.compress s in
 match s.n with
  | Tm_arrow(bs, c) ->
    let bs = SS.open_binders bs in
    begin match bs with
        | [(a, _);(wp, _)] -> a, wp.sort
        | _ -> fail()
    end
  | _ -> fail()

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
       let fail t = raise (Error(Err.unexpected_signature_for_monad env mname t, range_of_lid mname)) in
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
  then BU.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                        (Print.lid_to_string ed.mname)
                        (Print.binders_to_string " " ed.binders)
                        (Print.term_to_string ed.signature)
                        (Print.term_to_string (S.bv_to_name a))
                        (Print.term_to_string a.sort);

  let check_and_gen' env (_,t) k =
    check_and_gen env t k in

  let return_wp =
    let expected_k = U.arrow [S.mk_binder a; S.null_binder (S.bv_to_name a)] (S.mk_GTotal wp_a) in
    check_and_gen' env ed.ret_wp expected_k in

  let bind_wp =
    let b, wp_b = fresh_effect_signature () in
    let a_wp_b = U.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_b) in
    let expected_k = U.arrow [S.null_binder t_range;
                                 S.mk_binder a; S.mk_binder b;
                                 S.null_binder wp_a;
                                 S.null_binder a_wp_b]
                                 (S.mk_Total wp_b) in
    check_and_gen' env ed.bind_wp expected_k in

  let if_then_else =
    let p = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let expected_k = U.arrow [S.mk_binder a; S.mk_binder p;
                                 S.null_binder wp_a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.if_then_else expected_k in

  let ite_wp =
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.ite_wp expected_k in

  let stronger =
    let t, _ = U.type_u() in
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder wp_a;
                                 S.null_binder wp_a]
                                (S.mk_Total t) in
    check_and_gen' env ed.stronger expected_k in

  let close_wp =
    let b = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let b_wp_a = U.arrow [S.null_binder (S.bv_to_name b)] (S.mk_Total wp_a) in
    let expected_k = U.arrow [S.mk_binder a; S.mk_binder b; S.null_binder b_wp_a]
                                (S.mk_Total wp_a) in
    check_and_gen' env ed.close_wp expected_k in

  let assert_p =
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder (U.type_u() |> fst);
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.assert_p expected_k in

  let assume_p =
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder (U.type_u() |> fst);
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.assume_p expected_k in

  let null_wp =
    let expected_k = U.arrow [S.mk_binder a]
                                (S.mk_Total wp_a) in
    check_and_gen' env ed.null_wp expected_k in

  let trivial_wp =
    let t, _ = U.type_u() in
    let expected_k = U.arrow [S.mk_binder a;
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
            let t, _ = U.type_u () in
            let expected_k = U.arrow [S.mk_binder a;
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
            let a_wp_b = U.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_b) in
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

            let expected_k = U.arrow [S.mk_binder a;
                                         S.mk_binder b;
                                         S.mk_binder wp_f;
                                         S.null_binder (mk_repr a (S.bv_to_name wp_f));
                                         S.mk_binder wp_g;
                                         S.null_binder (U.arrow [S.mk_binder x_a] (S.mk_Total <| mk_repr b (wp_g_x)))]
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
            let expected_k = U.arrow [S.mk_binder a;
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
          (* We should not have action params anymore, they should have been handled by dmff below *)
          assert (match act.action_params with | [] -> true | _ -> false) ;

          // 0) The action definition has a (possibly) useless type; the
          // action cps'd type contains the "good" wp that tells us EVERYTHING
          // about what this action does. Please note that this "good" wp is
          // of the form [binders -> repr ...], i.e. is it properly curried.
          let act_typ, _, g_t = tc_tot_or_gtot_term env act.action_typ in

          // 1) Check action definition, setting its expected type to
          //    [action_typ]
          let env' = { Env.set_expected_typ env act_typ with instantiate_imp = false } in
          if Env.debug env (Options.Other "ED") then
            BU.print3 "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
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
              let k = U.arrow bs (S.mk_Total res) in
              let k, _, g = tc_tot_or_gtot_term env k in
              k, g
            | _ -> raise (Error(BU.format2
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
                let a, wp = destruct_repr (U.comp_result c) in
                let c = {
                  comp_univs=[env.universe_of env a];
		          effect_name = ed.mname;
                  result_typ = a;
                  effect_args = [as_arg wp];
                  flags = []
                } in
                U.arrow bs (S.mk_Comp c)
              | _ -> failwith "" in

          (* printfn "Checked action %s against type %s\n" *)
          (*         (Print.term_to_string act_defn) *)
          (*         (Print.term_to_string (N.normalize [N.Beta] env act_typ)); *)

          let univs, act_defn = TcUtil.generalize_universes env act_defn in

          let act_typ = N.normalize [N.Beta] env act_typ in
          {act with
              action_univs=univs;
              action_defn=act_defn;
              action_typ =act_typ }
        in
        ed.actions |> List.map check_action in
      repr, bind_repr, return_repr, actions
  in

  //generalize and close
  (* QUESTION (KM) : Why do we close with ed.binders and not effect_params ?? *)
  let t = U.arrow ed.binders (S.mk_Total ed.signature) in
  let (univs, t) = TcUtil.generalize_universes env0 t in
  let signature = match effect_params, (SS.compress t).n with
    | [], _ -> t
    | _, Tm_arrow(_, c) -> U.comp_result c
    | _ -> failwith "Impossible" in
  let close n ts =
    let ts = SS.close_univ_vars_tscheme univs (SS.close_tscheme effect_params ts) in
    // We always close [bind_repr], even though it may be [Tm_unknown]
    // (non-reifiable, non-reflectable effect)
    let m = List.length (fst ts) in
    if n >= 0 && not (is_unknown (snd ts)) && m <> n
    then begin
        let error = if m < n then "not universe-polymorphic enough" else "too universe-polymorphic" in
        failwith (BU.format3
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
        action_typ=typ; }
  in
  assert (List.length effect_params > 0 || List.length univs = 1);
  let ed = { ed with
      univs       = univs
    ; binders     = effect_params (* QUESTION (KM) : don't we need to close the effect params ? *)
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
  then BU.print_string (Print.eff_decl_to_string false ed);
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

  let open_and_check env other_binders t =
    let subst = SS.opening_of_binders (effect_binders @ other_binders) in
    let t = SS.subst subst t in
    let t, comp, _ = tc_term env t in
    t, comp
  in
  let mk x = mk x None signature.pos in

  // TODO: check that [_comp] is [Tot Type]
  let repr, _comp = open_and_check env [] ed.repr in
  if Env.debug env (Options.Other "ED") then
    BU.print1 "Representation is: %s\n" (Print.term_to_string repr);

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

  let sigelts = BU.mk_ref [] in
  let mk_lid name : lident = U.dm4f_lid ed name in

  // TODO: we assume that reading the top-level definitions in the order that
  // they come in the effect definition is enough... probably not
  let elaborate_and_star dmff_env other_binders item =
    let env = DMFF.get_env dmff_env in
    let u_item, item = item in
    // TODO: assert no universe polymorphism
    let item, item_comp = open_and_check env other_binders item in
    if not (U.is_total_lcomp item_comp) then
      raise (Err (BU.format2 "Computation for [%s] is not total : %s !" (Print.term_to_string item) (Print.lcomp_to_string item_comp)));
    let item_t, item_wp, item_elab = DMFF.star_expr dmff_env item in
    let item_wp = recheck_debug "*" env item_wp in
    let item_elab = recheck_debug "_" env item_elab in
    dmff_env, item_t, item_wp, item_elab
  in

  let dmff_env, _, bind_wp, bind_elab = elaborate_and_star dmff_env [] ed.bind_repr in
  let dmff_env, _, return_wp, return_elab = elaborate_and_star dmff_env [] ed.return_repr in

  (* Starting from [return_wp (b1:Type) (b2:b1) : M.wp b1 = fun bs -> body <: Type0], we elaborate *)
  (* [lift_from_pure (b1:Type) (wp:(b1 -> Type0)-> Type0) : M.wp b1 = fun bs -> wp (fun b2 -> body)] *)
  let lift_from_pure_wp =
      match (SS.compress return_wp).n with
      | Tm_abs (b1 :: b2 :: bs, body, what) ->
        let b1,b2, body =
          match SS.open_term [b1 ; b2] (U.abs bs body None) with
          | [b1 ; b2], body -> b1, b2, body
          | _ -> failwith "Impossible : open_term not preserving binders arity"
        in
        (* WARNING : pushing b1 and b2 in env might break the well-typedness *)
        (* invariant but we need them for normalization *)
        let env0 = push_binders (DMFF.get_env dmff_env) [b1 ; b2] in
        let wp_b1 =
          let raw_wp_b1 = mk (Tm_app (wp_type, [ (S.bv_to_name (fst b1), S.as_implicit false) ])) in
          N.normalize [ N.Beta ] env0 raw_wp_b1
        in
        let bs, body, what' = U.abs_formals <| N.eta_expand_with_type env0 body (U.unascribe wp_b1) in

        (* We check that what' is Tot Type0 *)
        let fail () =
          let error_msg =
            BU.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s"
              (Print.term_to_string body)
              (match what' with
               | None -> "None"
               | Some (Inl lc) -> Print.lcomp_to_string lc
               | Some (Inr (lid, _)) -> FStar.Ident.text_of_lid lid)
          in failwith error_msg
        in
        begin match what' with
        | None -> fail ()
        | Some (Inl lc) ->
          if U.is_pure_or_ghost_lcomp lc
          then
            let g_opt = Rel.try_teq true env lc.res_typ U.ktype0 in
            match g_opt with
            | Some g' -> Rel.force_trivial_guard env g'
            | None -> fail ()
          else fail ()
        | Some (Inr (lid, _)) ->
          if not (U.is_pure_effect lid) then fail ()
        end ;

        let wp =
          let t2 = (fst b2).sort in
          let pure_wp_type = DMFF.double_star t2 in
          S.gen_bv "wp" None pure_wp_type
        in

        (* fun b1 wp -> (fun bs@bs'-> wp (fun b2 -> body $$ Type0) $$ Type0) $$ wp_a *)
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
  let rec apply_last f l = match l with
  | [] -> failwith "empty path.."
  | [a] -> [f a]
  | (x::xs) -> x :: (apply_last f xs) in
  let register name item =
    let p = path_of_lid ed.mname in
    let p' = apply_last (fun s -> "__" ^ s ^ "_eff_override_" ^ name) p in
    let l' = lid_of_path p' Range.dummyRange in
    match try_lookup_lid env l' with
    | Some (_us,_t) -> begin
        BU.print1 "DM4F: Applying override %s\n" (string_of_lid l');
        // TODO: GM: get exact delta depth, needs a change of interfaces
        fv_to_tm (lid_as_fv l' Delta_equational None)
        end
    | None -> let sigelt, fv = TcUtil.mk_toplevel_definition env (mk_lid name) (U.abs effect_binders item None) in
              sigelts := sigelt :: !sigelts;
              fv
  in
  let lift_from_pure_wp = register "lift_from_pure" lift_from_pure_wp in

  // we do not expect the return_elab to verify, since that may require internalizing monotonicity of WPs (i.e. continuation monad)
  let return_wp = register "return_wp" return_wp in
  sigelts := mk_sigelt (Sig_pragma (SetOptions "--admit_smt_queries true")) :: !sigelts;
  let return_elab = register "return_elab" return_elab in
  sigelts := mk_sigelt (Sig_pragma (SetOptions "--admit_smt_queries false")) :: !sigelts;

  // we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
  let bind_wp = register "bind_wp" bind_wp in
  sigelts := mk_sigelt (Sig_pragma (SetOptions "--admit_smt_queries true")) :: !sigelts;
  let bind_elab = register "bind_elab" bind_elab in
  sigelts := mk_sigelt (Sig_pragma (SetOptions "--admit_smt_queries false")) :: !sigelts;

  let dmff_env, actions = List.fold_left (fun (dmff_env, actions) action ->
    let params_un = SS.open_binders action.action_params in
    let action_params, env', _ = tc_tparams (DMFF.get_env dmff_env) params_un in
    let action_params = List.map (fun (bv, qual) ->
      { bv with sort = N.normalize [ N.EraseUniverses ] env' bv.sort }, qual
    ) action_params in
    let dmff_env' = DMFF.set_env dmff_env env' in
    // We need to reverse-engineer what tc_eff_decl wants here...
    let dmff_env, action_t, action_wp, action_elab =
      elaborate_and_star dmff_env' action_params (action.action_univs, action.action_defn)
    in
    let name = action.action_name.ident.idText in
    let action_typ_with_wp = DMFF.trans_F dmff_env' action_t action_wp in
    let action_params = SS.close_binders action_params in
    let action_elab = SS.close action_params action_elab in
    let action_typ_with_wp = SS.close action_params action_typ_with_wp in
    let action_elab = abs action_params action_elab None in
    let action_typ_with_wp =
      match action_params with
      | [] -> action_typ_with_wp
      | _ -> flat_arrow action_params (S.mk_Total action_typ_with_wp)
    in
    if Env.debug env <| Options.Other "ED"
    then BU.print4 "original action_params %s, end action_params %s, type %s, term %s\n"
        (Print.binders_to_string "," params_un)
        (Print.binders_to_string "," action_params)
        (Print.term_to_string action_typ_with_wp)
        (Print.term_to_string action_elab) ;
    let action_elab = register (name ^ "_elab") action_elab in
    let action_typ_with_wp = register (name ^ "_complete_type") action_typ_with_wp in
    (* it does not seem that dmff_env' has been modified  by elaborate_and_star so it should be okay to return the original env *)
    dmff_env,
    { action with
      action_params = [] ;
      action_defn = apply_close action_elab;
      action_typ = apply_close action_typ_with_wp
    } :: actions
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
                  Free.names bv.sort |> BU.set_mem (fst type_param) |> not
                ) wp_binders
            in
            let post = match post_args with
                | [post] -> post
                | _ -> failwith (BU.format1 "Impossible: multiple post candidates %s" (Print.term_to_string arrow))
            in
            // Pre-condition does not mention the return type; don't close over it
            U.arrow pre_args c,
            // Post-condition does, however!
            U.abs (type_param :: effect_param) (fst post).sort None
        | _ ->
            failwith (BU.format1 "Impossible: pre/post arrow %s" (Print.term_to_string arrow))
        end
    | _ ->
        failwith (BU.format1 "Impossible: pre/post abs %s" (Print.term_to_string wp_type))
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
    BU.print_string (Print.eff_decl_to_string true ed);

  let lift_from_pure_opt =
    if List.length effect_binders = 0 then begin
      // Won't work with parameterized effect
      let lift_from_pure = {
          source = Const.effect_PURE_lid;
          target = ed.mname ;
          lift_wp = Some ([], apply_close lift_from_pure_wp) ;
          lift = None //Some ([], apply_close return_elab)
      } in
      Some (mk_sigelt (Sig_sub_effect (lift_from_pure)))
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
      | [{ sigel = Sig_inductive_typ(lex_t, [], [], t, _, _);  sigquals = []; sigrng = r };
         { sigel = Sig_datacon(lex_top, [], _t_top, _lex_t_top, 0, _); sigquals = []; sigrng = r1 };
         { sigel = Sig_datacon(lex_cons, [], _t_cons, _lex_t_cons, 0, _); sigquals = []; sigrng = r2 }]
         when (lid_equals lex_t Const.lex_t_lid
            && lid_equals lex_top Const.lextop_lid
            && lid_equals lex_cons Const.lexcons_lid) ->

        let u = S.new_univ_name (Some r) in
        let t = mk (Tm_type(U_name u)) None r in
        let t = Subst.close_univ_vars [u] t in
        let tc = { sigel = Sig_inductive_typ(lex_t, [u], [], t, [], [Const.lextop_lid; Const.lexcons_lid]);
                   sigquals = [];
                   sigrng = r;
                   sigmeta = default_sigmeta } in

        let utop = S.new_univ_name (Some r1) in
        let lex_top_t = mk (Tm_uinst(S.fvar (Ident.set_lid_range Const.lex_t_lid r1) Delta_constant None, [U_name utop])) None r1 in
        let lex_top_t = Subst.close_univ_vars [utop] lex_top_t in
        let dc_lextop = { sigel = Sig_datacon(lex_top, [utop], lex_top_t, Const.lex_t_lid, 0, []);
                          sigquals = [];
                          sigrng = r1;
                          sigmeta = default_sigmeta  } in

        let ucons1 = S.new_univ_name (Some r2) in
        let ucons2 = S.new_univ_name (Some r2) in
        let lex_cons_t =
            let a = S.new_bv (Some r2) (mk (Tm_type(U_name ucons1)) None r2) in
            let hd = S.new_bv (Some r2) (S.bv_to_name a) in
            let tl = S.new_bv (Some r2) (mk (Tm_uinst(S.fvar (Ident.set_lid_range Const.lex_t_lid r2) Delta_constant None, [U_name ucons2])) None r2) in
            let res = mk (Tm_uinst(S.fvar (Ident.set_lid_range Const.lex_t_lid r2) Delta_constant None, [U_max [U_name ucons1; U_name ucons2]])) None r2 in
            U.arrow [(a, Some S.imp_tag); (hd, None); (tl, None)] (S.mk_Total res) in
        let lex_cons_t = Subst.close_univ_vars [ucons1;ucons2]  lex_cons_t in
        let dc_lexcons = { sigel = Sig_datacon(lex_cons, [ucons1;ucons2], lex_cons_t, Const.lex_t_lid, 0, []);
                           sigquals = [];
                           sigrng = r2;
                           sigmeta = default_sigmeta  } in
        { sigel = Sig_bundle([tc; dc_lextop; dc_lexcons], lids);
          sigquals = [];
          sigrng = Env.get_range env;
          sigmeta = default_sigmeta  }
      | _ ->
        failwith (BU.format1 "Unexpected lex_t: %s\n" (Print.sigelt_to_string (mk_sigelt (Sig_bundle(ses, lids)))))
    end

and tc_assume (env:env) (lid:lident) (phi:formula) (quals:list<qualifier>) (r:Range.range) :sigelt =
    let env = Env.set_range env r in
    let k, _ = U.type_u() in
    let phi = tc_check_trivial_guard env phi k |> N.normalize [N.Beta; N.Eager_unfolding] env in
    TcUtil.check_uvars r phi;
    { sigel = Sig_assume(lid, phi);
      sigquals = quals;
      sigrng = r;
      sigmeta = default_sigmeta  }

and tc_inductive env ses quals lids =
    let env0 = env in
    let sig_bndle, tcs, datas = TcInductive.check_inductive_well_typedness env ses quals lids in
    (* we have a well-typed inductive;
            we still need to check whether or not it supports equality
            and whether it is strictly positive
       *)

    (* Once the datacons are generalized we can construct the projectors with the right types *)
    let data_ops_ses = List.map (TcUtil.mk_data_operations quals env tcs) datas |> List.flatten in

    //strict positivity check
    (if Options.no_positivity () || Options.lax ()  then ()  //skipping positivity check if lax mode
     else
       let env = push_sigelt env0 sig_bndle in
       let b = List.iter (fun ty ->
         let b = TcInductive.check_positivity ty env in
         if not b then
           let lid, r =
             match ty.sigel with
             | Sig_inductive_typ (lid, _, _, _, _, _) -> lid, ty.sigrng
             | _                                         -> failwith "Impossible!"
           in
           Errors.err r ("Inductive type " ^ lid.str ^ " does not satisfy the positivity condition")
         else ()
       ) tcs in
       ());

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
        let types_to_skip = [ "c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"; ] in
        List.existsb (fun s -> s = lid.ident.idText) types_to_skip
    in

    let is_noeq = List.existsb (fun q -> q = Noeq) quals in

    if ((List.length tcs = 0) || ((lid_equals env.curmodule Const.prims_lid) && skip_prims_type ()) || is_noeq)
    then [sig_bndle], data_ops_ses
    else
        let is_unopteq = List.existsb (fun q -> q = Unopteq) quals in
        let ses =
          if is_unopteq then TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env0 tc_assume
          else TcInductive.optimized_haseq_scheme sig_bndle tcs datas env0 tc_assume
        in
        { sigel = Sig_bundle(tcs@datas, lids);
          sigquals = quals;
          sigrng = Env.get_range env0;
          sigmeta = default_sigmeta  }::ses, data_ops_ses


(* [tc_decl env se] typechecks [se] in environment [env] and returns *)
(* the list of typechecked sig_elts, and a list of new sig_elts elaborated during typechecking but not yet typechecked *)
and tc_decl env se: list<sigelt> * list<sigelt> =
  let env = set_hint_correlator env se in
  TcUtil.check_sigelt_quals env se;
  let r = se.sigrng in
  match se.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ ->
    failwith "Impossible bare data-constructor"

  | Sig_bundle(ses, lids) when (lids |> BU.for_some (lid_equals Const.lex_t_lid)) ->
    //lex_t is very special; it uses a more expressive form of universe polymorphism than is allowed elsewhere
    //Instead of this special treatment, we could make use of explicit lifts, but LexCons is used pervasively
    (*
        type lex_t<u> =
          | LexTop<u>  : lex_t<u>
          | LexCons<u1, u2> : #a:Type(u1) -> a -> lex_t<u2> -> lex_t<max u1 u2>
    *)
    let env = Env.set_range env r in
    let se = tc_lex_t env ses se.sigquals lids  in
    [se], []

  | Sig_bundle(ses, lids) ->
    let env = Env.set_range env r in
    let ses, projectors_ses = tc_inductive env ses se.sigquals lids in
    ses, projectors_ses

  | Sig_pragma(p) ->
    let set_options t s = match Options.set_options t s with
      | Getopt.Success -> ()
      | Getopt.Help  -> raise (Error ("Failed to process pragma: use 'fstar --help' to see which options are available", r))
      | Getopt.Error s -> raise (Error ("Failed to process pragma: " ^s, r))
    in
    begin match p with
      | LightOff ->
        if p = LightOff
        then Options.set_ml_ish();
        [se], []
      | SetOptions o ->
        set_options Options.Set o;
        [se], []
      | ResetOptions sopt ->
        Options.restore_cmd_line_options false |> ignore;
        let _ = match sopt with
          | None -> ()
          | Some s -> set_options Options.Reset s
        in
        [se], []
    end


  | Sig_new_effect_for_free (ne) ->
      (* This is only an elaboration rule not a typechecking one *)

      // Let the power of Dijkstra generate everything "for free", then defer
      // the rest of the job to [tc_decl].
      let ses, ne, lift_from_pure_opt = cps_and_elaborate env ne in
      let effect_and_lift_ses = match lift_from_pure_opt with
          | Some lift -> [ { se with sigel = Sig_new_effect (ne) } ; lift ]
          | None -> [ { se with sigel = Sig_new_effect (ne) } ]
      in

      [], ses @ effect_and_lift_ses

  | Sig_new_effect(ne) ->
    let ne = tc_eff_decl env ne in
    let se = { se with sigel = Sig_new_effect(ne) } in
    [se], []

  | Sig_sub_effect(sub) ->
    let ed_src = Env.get_effect_decl env sub.source in
    let ed_tgt = Env.get_effect_decl env sub.target in
    let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
    let b, wp_b_tgt = monad_signature env sub.target (Env.lookup_effect_lid env sub.target) in
    let wp_a_tgt    = SS.subst [NT(b, S.bv_to_name a)] wp_b_tgt in
    let expected_k  = U.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
    let repr_type eff_name a wp =
      let no_reify l = raise (Error(BU.format1 "Effect %s cannot be reified" l.str, Env.get_range env)) in
      match Env.effect_decl_opt env eff_name with
      | None -> no_reify eff_name
      | Some (ed, qualifiers) ->
          let repr = Env.inst_effect_fun_with [U_unknown] env ed ([], ed.repr) in
          if not (qualifiers |> List.contains Reifiable) then
            no_reify eff_name
          else
            mk (Tm_app(repr, [as_arg a; as_arg wp])) None (Env.get_range env)
    in
    let lift, lift_wp =
      match sub.lift, sub.lift_wp with
      | None, None ->
        failwith "Impossible"
      | lift, Some (_, lift_wp) ->
        (* Covers both the "classic" format and the reifiable case. *)
        lift, check_and_gen env lift_wp expected_k
      (* Sub-effect for free case *)
      | Some (what, lift), None ->
        if Env.debug env (Options.Other "ED") then
            BU.print1 "Lift for free : %s\n" (Print.term_to_string lift) ;
        let dmff_env = DMFF.empty env (tc_constant Range.dummyRange) in
        let lift, comp, _ = tc_term env lift in
        (* TODO : Check that comp is pure ? *)
        let _, lift_wp, lift_elab = DMFF.star_expr dmff_env lift in
        let _ = recheck_debug "lift-wp" env lift_wp in
        let _ = recheck_debug "lift-elab" env lift_elab in
        Some ([], lift_elab), ([], lift_wp)
    in
    let lax = env.lax in
    (* we do not expect the lift to verify, *)
    (* since that requires internalizing monotonicity of WPs *)
    let env = {env with lax=true} in
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
        U.arrow [S.mk_binder a; S.mk_binder wp_a; S.null_binder repr_f]
                    (S.mk_Total repr_result) in
//          printfn "LIFT: Expected type for lift = %s\n" (Print.term_to_string expected_k);
        let expected_k, _, _ =
          tc_tot_or_gtot_term env expected_k in
//          printfn "LIFT: Checking %s against expected type %s\n" (Print.term_to_string lift) (Print.term_to_string expected_k);
        let lift = check_and_gen env lift expected_k in
//          printfn "LIFT: Checked %s against expected type %s\n" (Print.tscheme_to_string lift) (Print.term_to_string expected_k);
        Some lift
    in
    let sub = {sub with lift_wp=Some lift_wp; lift=lift} in
    let se = { se with sigel = Sig_sub_effect(sub) } in
    [se], []

  | Sig_effect_abbrev(lid, uvs, tps, c, flags) ->
    assert (uvs = []);
    let env0 = env in
    let env = Env.set_range env r in
    let tps, c = SS.open_comp tps c in
    let tps, env, us = tc_tparams env tps in
    let c, u, g = tc_comp env c in
    Rel.force_trivial_guard env g;
    let tps = SS.close_binders tps in
    let c = SS.close_comp tps c in
    let uvs, t = TcUtil.generalize_universes env0 (mk (Tm_arrow(tps, c)) None r) in
    let tps, c = match tps, (SS.compress t).n with
      | [], Tm_arrow(_, c) -> [], c
      | _,  Tm_arrow(tps, c) -> tps, c
      | _ -> failwith "Impossible" in
    if List.length uvs <> 1
    then (let _, t = Subst.open_univ_vars uvs t in
          raise (Error(BU.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                  (Print.lid_to_string lid)
                                  (List.length uvs |> BU.string_of_int)
                                  (Print.term_to_string t), r)));
    let se = { se with sigel = Sig_effect_abbrev(lid, uvs, tps, c, flags) } in
    [se], []

  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _, _)
      when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) ->
      (* Dummy declaration which must be erased since it has been elaborated somewhere else *)
      [], []

  | Sig_declare_typ(lid, uvs, t) -> //NS: No checks on the qualifiers?
    let env = Env.set_range env r in
    //assert (uvs = []);
    let uvs, t =
        if uvs = []
        then check_and_gen env t (fst (U.type_u()))
        else
            let uvs, t = SS.open_univ_vars uvs t in
            let t = tc_check_trivial_guard env t (fst (U.type_u())) in
            let t = N.normalize [N.NoFullNorm; N.Beta] env t in
            uvs, SS.close_univ_vars uvs t
    in
    let se = { se with sigel = Sig_declare_typ(lid, uvs, t) } in
    [se], []

  | Sig_assume(lid, phi) ->
    let se = tc_assume env lid phi se.sigquals r in
    [se], []

  | Sig_main(e) ->
    let env = Env.set_range env r in
    let env = Env.set_expected_typ env Common.t_unit in
    let e, c, g1 = tc_term env e in
    let e, _, g = check_expected_effect env (Some (U.ml_comp Common.t_unit r)) (e, c.comp()) in
    Rel.force_trivial_guard env (Rel.conj_guard g1 g);
    let se = { se with sigel = Sig_main(e) } in
    [se], []

  | Sig_let(lbs, lids, attrs) ->
    let env = Env.set_range env r in
    let check_quals_eq l qopt q = match qopt with
      | None -> Some q
      | Some q' ->
        if List.length q = List.length q'
        && List.forall2 U.qualifier_equal q q'
        then Some q
        else raise (Error(BU.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              (Print.lid_to_string l)
                              (Print.quals_to_string q)
                              (Print.quals_to_string q'), r))
    in

    (* 1. (a) Annotate each lb in lbs with a type from the corresponding val decl, if there is one
          (b) Generalize the type of lb only if none of the lbs have val decls
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
              let _ = match lb.lbtyp.n with
                | Tm_unknown -> ()
                | _ -> Errors.warn r "Annotation from val declaration overrides inline type annotation"
              in
              if lb.lbunivs <> [] && List.length lb.lbunivs <> List.length uvs
              then raise (Error ("Inline universes are incoherent with annotation from val declaration", r));
              false, //explicit annotation provided; do not generalize
              mk_lb (Inr lbname, uvs, Const.effect_ALL_lid, tval, lb.lbdef),
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

    (* 3. Type-check the Tm_let and then convert it back to a Sig_let *)
    let se, lbs = match tc_maybe_toplevel_term ({env with top_level=true; generalize=should_generalize}) e with
        | {n=Tm_let(lbs, e)}, _, g when Rel.is_trivial g ->
          //propagate the MaskedEffect tag to the qualifiers
          let quals = match e.n with
              | Tm_meta(_, Meta_desugared Masked_effect) -> HasMaskedEffect::quals
              | _ -> quals
          in
          // drop inline_for_extraction unless pure (otherwise, this now
          // generates beta-redexes that kreMLin is particularly unhappy with)
          let quals = List.choose (function
            | Inline_for_extraction ->
                if not (List.for_all (fun lb ->
                  let ok = is_pure_or_ghost_function lb.lbtyp in
                  if not ok then
                    BU.print1_warning "Dropping inline_for_extraction from %s because it is not a pure function\n"
                      (SP.lbname_to_string lb.lbname);
                  ok
                ) (snd lbs)) then
                  None
                else
                  Some Inline_for_extraction
            | q ->
                Some q
          ) quals in
          { se with sigel = Sig_let(lbs, lids, attrs);
                    sigquals =  quals },
          lbs
      | _ -> failwith "impossible"
    in

    // CPC doc: Actually I don't need the let-val pairing; It's enough to register the docs of the val independently, since they won't be overwritten when the let is desugared with no docs.

    (* 4. Record the type of top-level lets, and log if requested *)
    snd lbs |> List.iter (fun lb ->
        let fv = right lb.lbname in
        Common.insert_fv fv lb.lbtyp);

    if log env
    then BU.print1 "%s\n" (snd lbs |> List.map (fun lb ->
          let should_log = match Env.try_lookup_val_decl env (right lb.lbname).fv_name.v with
              | None -> true
              | _ -> false in
          if should_log
          then BU.format2 "let %s : %s" (Print.lbname_to_string lb.lbname) (Print.term_to_string (*env*) lb.lbtyp)
          else "") |> String.concat "\n");

    [se], []


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
   let is_abstract quals = quals |> BU.for_some (function Abstract-> true | _ -> false) in
   let is_hidden_proj_or_disc q = match q with
      | Projector(l, _)
      | Discriminator l -> hidden |> BU.for_some (lid_equals l)
      | _ -> false
   in
   match se.sigel with
  | Sig_pragma         _ -> [], hidden

  | Sig_inductive_typ _
  | Sig_datacon _ -> failwith "Impossible"

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

  | Sig_assume(_, _) ->
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

  | Sig_let((false, [lb]), _, _)
        when se.sigquals |> BU.for_some is_hidden_proj_or_disc ->
    let fv = right lb.lbname in
    let lid = fv.fv_name.v in
    if hidden |> BU.for_some (S.fv_eq_lid fv)
    then [], hidden //this projector definition already has a declare_typ
    else let dec = { sigel = Sig_declare_typ(fv.fv_name.v, lb.lbunivs, lb.lbtyp);
                     sigquals =[Assumption];
                     sigrng = Ident.range_of_lid lid;
                     sigmeta = default_sigmeta  } in
          [dec], lid::hidden

  | Sig_let(lbs, l, _) ->
    if is_abstract se.sigquals
    then (snd lbs |>  List.map (fun lb ->
           { se with sigel = Sig_declare_typ((right lb.lbname).fv_name.v, lb.lbunivs, lb.lbtyp);
                     sigquals = Assumption::se.sigquals}),
          hidden)
    else [se], hidden

(* adds the typechecked sigelt to the env, also performs any processing required in the env (such as reset options) *)
(* this was earlier part of tc_decl, but separating it might help if and when we cache type checked modules *)
let add_sigelt_to_env (env:Env.env) (se:sigelt) :Env.env =
  match se.sigel with
  | Sig_inductive_typ _ -> failwith "add_sigelt_to_env: Impossible, bare data constructor"
  | Sig_datacon _ -> failwith "add_sigelt_to_env: Impossible, bare data constructor"
  | Sig_pragma (p) ->
    (match p with
     | ResetOptions _ -> env.solver.refresh (); env
     | _ -> env)
  | Sig_new_effect_for_free _ -> env
  | Sig_new_effect (ne) ->
    let env = Env.push_sigelt env se in
    ne.actions |> List.fold_left (fun env a -> Env.push_sigelt env (U.action_as_lb ne.mname a)) env
  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _, _) when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) -> env
  | _ -> Env.push_sigelt env se


let tc_decls env ses =
  let rec process_one_decl (ses, exports, env, hidden) se =
    if Env.debug env Options.Low
    then BU.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" (Print.sigelt_to_string se);

    let ses', ses_elaborated = tc_decl env se  in
    let env = ses' |> List.fold_left (fun env se -> add_sigelt_to_env env se) env in

    if (Options.log_types()) || Env.debug env <| Options.Other "LogTypes"
    then BU.print1 "Checked: %s\n" (List.fold_left (fun s se -> s ^ Print.sigelt_to_string se ^ "\n") "" ses');

    List.iter (fun se -> env.solver.encode_sig env se) ses';

    let exports, hidden =
      let accum_exports_hidden (exports, hidden) se =
        let se_exported, hidden = for_export hidden se in
        List.rev_append se_exported exports, hidden
      in
      List.fold_left accum_exports_hidden (exports, hidden) ses'
    in

    (List.rev_append ses' ses, exports, env, hidden), ses_elaborated
  in

  let ses, exports, env, _ = BU.fold_flatten process_one_decl ([], [], env, []) ses in
  List.rev_append ses [], List.rev_append exports [], env

let tc_partial_modul env modul =
  let verify = Options.should_verify modul.name.str in
  let action = if verify then "Verifying" else "Lax-checking" in
  let label = if modul.is_interface then "interface" else "implementation" in
  if Options.debug_any () then
    BU.print3 "%s %s of %s\n" action label modul.name.str;

  let name = BU.format2 "%s %s"  (if modul.is_interface then "interface" else "module") modul.name.str in
  let msg = "Internals for " ^name in
  let env = {env with Env.is_iface=modul.is_interface; admit=not verify} in
  //AR: the interactive mode calls this function, because of which there is an extra solver push.
  //    the interactive mode does not call finish_partial_modul, so this push is not popped.
  //    currently, there is a cleanup function in the interactive mode tc, that does this extra pop.
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
        | Sig_let((_, lbs), _, _) ->
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
        | Sig_pragma _ -> ()
    in
    if Ident.lid_equals modul.name Const.prims_lid
    then ()
    else List.iter check_sigelt exports


let finish_partial_modul env modul exports =
  let modul = {modul with exports=exports; is_interface=modul.is_interface} in
  let env = Env.finish_module env modul in
  if not (Options.lax())
  then check_exports env modul exports;
  env.solver.pop ("Ending modul " ^ modul.name.str);
  env.solver.encode_modul env modul;
  env.solver.refresh();
  //interactive mode manages it itself
  let _ = if not (Options.interactive ()) then Options.restore_cmd_line_options true |> ignore else () in
  modul, env

let tc_modul env modul =
  let modul, non_private_decls, env = tc_partial_modul env modul in
  finish_partial_modul env modul non_private_decls

let check_module env m =
  if Options.debug_any()
  then BU.print2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.lid_to_string m.name);

  let env = {env with lax=not (Options.should_verify m.name.str)} in
  let m, env = tc_modul env m in

  (* Debug information for level Normalize : normalizes all toplevel declarations an dump the current module *)
  if Options.dump_module m.name.str
  then BU.print1 "%s\n" (Print.modul_to_string m);
  if Options.dump_module m.name.str && Options.debug_at_level m.name.str (Options.Other "Normalize")
  then begin
    let normalize_toplevel_lets = fun se -> match se.sigel with
        | Sig_let ((b, lbs), ids, attrs) ->
            let n = N.normalize [N.Beta ; N.Eager_unfolding; N.Reify ; N.Inlining ; N.Primops ; N.UnfoldUntil S.Delta_constant ; N.AllowUnboundUniverses ] in
            let update lb =
                let univnames, e = SS.open_univ_vars lb.lbunivs lb.lbdef in
                { lb with lbdef = n (Env.push_univ_vars env univnames) e }
            in
            { se with sigel = Sig_let ((b, List.map update lbs), ids, attrs) }
        | _ -> se
    in
    let normalized_module = { m with declarations = List.map normalize_toplevel_lets m.declarations } in
    BU.print1 "%s\n" (Print.modul_to_string normalized_module)
  end;

  m, env
