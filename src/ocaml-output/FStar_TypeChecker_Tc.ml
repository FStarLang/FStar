open Prims

let set_hint_correlator
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt
      -> FStar_TypeChecker_Env.env =
  fun env se ->
    let uu____7 = FStar_Options.reuse_hint_for () in
    match uu____7 with
    | FStar_Pervasives_Native.Some l ->
        let lid =
          let uu____12 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.lid_add_suffix uu____12 l
        in
        let uu___61_13 = env in
        { FStar_TypeChecker_Env.solver= uu___61_13.FStar_TypeChecker_Env.solver
        ; FStar_TypeChecker_Env.range= uu___61_13.FStar_TypeChecker_Env.range
        ; FStar_TypeChecker_Env.curmodule=
            uu___61_13.FStar_TypeChecker_Env.curmodule
        ; FStar_TypeChecker_Env.gamma= uu___61_13.FStar_TypeChecker_Env.gamma
        ; FStar_TypeChecker_Env.gamma_cache=
            uu___61_13.FStar_TypeChecker_Env.gamma_cache
        ; FStar_TypeChecker_Env.modules=
            uu___61_13.FStar_TypeChecker_Env.modules
        ; FStar_TypeChecker_Env.expected_typ=
            uu___61_13.FStar_TypeChecker_Env.expected_typ
        ; FStar_TypeChecker_Env.sigtab= uu___61_13.FStar_TypeChecker_Env.sigtab
        ; FStar_TypeChecker_Env.is_pattern=
            uu___61_13.FStar_TypeChecker_Env.is_pattern
        ; FStar_TypeChecker_Env.instantiate_imp=
            uu___61_13.FStar_TypeChecker_Env.instantiate_imp
        ; FStar_TypeChecker_Env.effects=
            uu___61_13.FStar_TypeChecker_Env.effects
        ; FStar_TypeChecker_Env.generalize=
            uu___61_13.FStar_TypeChecker_Env.generalize
        ; FStar_TypeChecker_Env.letrecs=
            uu___61_13.FStar_TypeChecker_Env.letrecs
        ; FStar_TypeChecker_Env.top_level=
            uu___61_13.FStar_TypeChecker_Env.top_level
        ; FStar_TypeChecker_Env.check_uvars=
            uu___61_13.FStar_TypeChecker_Env.check_uvars
        ; FStar_TypeChecker_Env.use_eq= uu___61_13.FStar_TypeChecker_Env.use_eq
        ; FStar_TypeChecker_Env.is_iface=
            uu___61_13.FStar_TypeChecker_Env.is_iface
        ; FStar_TypeChecker_Env.admit= uu___61_13.FStar_TypeChecker_Env.admit
        ; FStar_TypeChecker_Env.lax= uu___61_13.FStar_TypeChecker_Env.lax
        ; FStar_TypeChecker_Env.lax_universes=
            uu___61_13.FStar_TypeChecker_Env.lax_universes
        ; FStar_TypeChecker_Env.failhard=
            uu___61_13.FStar_TypeChecker_Env.failhard
        ; FStar_TypeChecker_Env.nosynth=
            uu___61_13.FStar_TypeChecker_Env.nosynth
        ; FStar_TypeChecker_Env.tc_term=
            uu___61_13.FStar_TypeChecker_Env.tc_term
        ; FStar_TypeChecker_Env.type_of=
            uu___61_13.FStar_TypeChecker_Env.type_of
        ; FStar_TypeChecker_Env.universe_of=
            uu___61_13.FStar_TypeChecker_Env.universe_of
        ; FStar_TypeChecker_Env.check_type_of=
            uu___61_13.FStar_TypeChecker_Env.check_type_of
        ; FStar_TypeChecker_Env.use_bv_sorts=
            uu___61_13.FStar_TypeChecker_Env.use_bv_sorts
        ; FStar_TypeChecker_Env.qname_and_index=
            FStar_Pervasives_Native.Some (lid, Prims.parse_int "0")
        ; FStar_TypeChecker_Env.proof_ns=
            uu___61_13.FStar_TypeChecker_Env.proof_ns
        ; FStar_TypeChecker_Env.synth= uu___61_13.FStar_TypeChecker_Env.synth
        ; FStar_TypeChecker_Env.is_native_tactic=
            uu___61_13.FStar_TypeChecker_Env.is_native_tactic
        ; FStar_TypeChecker_Env.identifier_info=
            uu___61_13.FStar_TypeChecker_Env.identifier_info
        ; FStar_TypeChecker_Env.tc_hooks=
            uu___61_13.FStar_TypeChecker_Env.tc_hooks
        ; FStar_TypeChecker_Env.dsenv= uu___61_13.FStar_TypeChecker_Env.dsenv
        ; FStar_TypeChecker_Env.dep_graph=
            uu___61_13.FStar_TypeChecker_Env.dep_graph }
    | FStar_Pervasives_Native.None ->
        let lids = FStar_Syntax_Util.lids_of_sigelt se in
        let lid =
          match lids with
          | [] ->
              let uu____22 = FStar_TypeChecker_Env.current_module env in
              let uu____23 =
                let uu____24 = FStar_Syntax_Syntax.next_id () in
                FStar_All.pipe_right uu____24 FStar_Util.string_of_int
              in
              FStar_Ident.lid_add_suffix uu____22 uu____23
          | l :: uu____26 -> l
        in
        let uu___62_29 = env in
        { FStar_TypeChecker_Env.solver= uu___62_29.FStar_TypeChecker_Env.solver
        ; FStar_TypeChecker_Env.range= uu___62_29.FStar_TypeChecker_Env.range
        ; FStar_TypeChecker_Env.curmodule=
            uu___62_29.FStar_TypeChecker_Env.curmodule
        ; FStar_TypeChecker_Env.gamma= uu___62_29.FStar_TypeChecker_Env.gamma
        ; FStar_TypeChecker_Env.gamma_cache=
            uu___62_29.FStar_TypeChecker_Env.gamma_cache
        ; FStar_TypeChecker_Env.modules=
            uu___62_29.FStar_TypeChecker_Env.modules
        ; FStar_TypeChecker_Env.expected_typ=
            uu___62_29.FStar_TypeChecker_Env.expected_typ
        ; FStar_TypeChecker_Env.sigtab= uu___62_29.FStar_TypeChecker_Env.sigtab
        ; FStar_TypeChecker_Env.is_pattern=
            uu___62_29.FStar_TypeChecker_Env.is_pattern
        ; FStar_TypeChecker_Env.instantiate_imp=
            uu___62_29.FStar_TypeChecker_Env.instantiate_imp
        ; FStar_TypeChecker_Env.effects=
            uu___62_29.FStar_TypeChecker_Env.effects
        ; FStar_TypeChecker_Env.generalize=
            uu___62_29.FStar_TypeChecker_Env.generalize
        ; FStar_TypeChecker_Env.letrecs=
            uu___62_29.FStar_TypeChecker_Env.letrecs
        ; FStar_TypeChecker_Env.top_level=
            uu___62_29.FStar_TypeChecker_Env.top_level
        ; FStar_TypeChecker_Env.check_uvars=
            uu___62_29.FStar_TypeChecker_Env.check_uvars
        ; FStar_TypeChecker_Env.use_eq= uu___62_29.FStar_TypeChecker_Env.use_eq
        ; FStar_TypeChecker_Env.is_iface=
            uu___62_29.FStar_TypeChecker_Env.is_iface
        ; FStar_TypeChecker_Env.admit= uu___62_29.FStar_TypeChecker_Env.admit
        ; FStar_TypeChecker_Env.lax= uu___62_29.FStar_TypeChecker_Env.lax
        ; FStar_TypeChecker_Env.lax_universes=
            uu___62_29.FStar_TypeChecker_Env.lax_universes
        ; FStar_TypeChecker_Env.failhard=
            uu___62_29.FStar_TypeChecker_Env.failhard
        ; FStar_TypeChecker_Env.nosynth=
            uu___62_29.FStar_TypeChecker_Env.nosynth
        ; FStar_TypeChecker_Env.tc_term=
            uu___62_29.FStar_TypeChecker_Env.tc_term
        ; FStar_TypeChecker_Env.type_of=
            uu___62_29.FStar_TypeChecker_Env.type_of
        ; FStar_TypeChecker_Env.universe_of=
            uu___62_29.FStar_TypeChecker_Env.universe_of
        ; FStar_TypeChecker_Env.check_type_of=
            uu___62_29.FStar_TypeChecker_Env.check_type_of
        ; FStar_TypeChecker_Env.use_bv_sorts=
            uu___62_29.FStar_TypeChecker_Env.use_bv_sorts
        ; FStar_TypeChecker_Env.qname_and_index=
            FStar_Pervasives_Native.Some (lid, Prims.parse_int "0")
        ; FStar_TypeChecker_Env.proof_ns=
            uu___62_29.FStar_TypeChecker_Env.proof_ns
        ; FStar_TypeChecker_Env.synth= uu___62_29.FStar_TypeChecker_Env.synth
        ; FStar_TypeChecker_Env.is_native_tactic=
            uu___62_29.FStar_TypeChecker_Env.is_native_tactic
        ; FStar_TypeChecker_Env.identifier_info=
            uu___62_29.FStar_TypeChecker_Env.identifier_info
        ; FStar_TypeChecker_Env.tc_hooks=
            uu___62_29.FStar_TypeChecker_Env.tc_hooks
        ; FStar_TypeChecker_Env.dsenv= uu___62_29.FStar_TypeChecker_Env.dsenv
        ; FStar_TypeChecker_Env.dep_graph=
            uu___62_29.FStar_TypeChecker_Env.dep_graph }


let log : FStar_TypeChecker_Env.env -> Prims.bool =
  fun env ->
    FStar_Options.log_types ()
    &&
    let uu____38 =
      let uu____39 = FStar_TypeChecker_Env.current_module env in
      FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____39
    in
    Prims.op_Negation uu____38


let get_tactic_fv:
      'Auu____44. 'Auu____44 -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
      -> FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option =
  fun env tac_lid h ->
    match h.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (h', uu____60) -> (
        let uu____65 =
          let uu____66 = FStar_Syntax_Subst.compress h' in
          uu____66.FStar_Syntax_Syntax.n
        in
        match uu____65 with
        | FStar_Syntax_Syntax.Tm_fvar fv
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.tactic_lid ->
            FStar_Pervasives_Native.Some fv
        | uu____72 -> FStar_Pervasives_Native.None )
    | uu____73 -> FStar_Pervasives_Native.None


let user_tactics_modules : Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []


let tc_check_trivial_guard
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
      -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term =
  fun env t k ->
    let uu____115 =
      FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k
    in
    match uu____115 with t1, c, g ->
      FStar_TypeChecker_Rel.force_trivial_guard env g ;
      t1


let recheck_debug
    : Prims.string -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
      -> FStar_Syntax_Syntax.term =
  fun s env t ->
    (let uu____136 =
       FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
     in
     if uu____136 then
       let uu____137 = FStar_Syntax_Print.term_to_string t in
       FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s
         uu____137
     else ()) ;
    let uu____139 = FStar_TypeChecker_TcTerm.tc_term env t in
    match uu____139 with t', uu____147, uu____148 ->
      (let uu____150 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
       in
       if uu____150 then
         let uu____151 = FStar_Syntax_Print.term_to_string t' in
         FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" uu____151
       else ()) ;
      t


let check_and_gen
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
      -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme =
  fun env t k ->
    let uu____162 = tc_check_trivial_guard env t k in
    FStar_TypeChecker_Util.generalize_universes env uu____162


let check_nogen:
      'Auu____167. FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
      -> FStar_Syntax_Syntax.typ
      -> ( 'Auu____167 Prims.list
         , FStar_Syntax_Syntax.term )
         FStar_Pervasives_Native.tuple2 =
  fun env t k ->
    let t1 = tc_check_trivial_guard env t k in
    let uu____187 =
      FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
        env t1
    in
    ([], uu____187)


let monad_signature
    : FStar_TypeChecker_Env.env -> FStar_Ident.lident
      -> FStar_Syntax_Syntax.term
      -> ( FStar_Syntax_Syntax.bv
         , FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax )
         FStar_Pervasives_Native.tuple2 =
  fun env m s ->
    let fail uu____214 =
      let uu____215 =
        FStar_TypeChecker_Err.unexpected_signature_for_monad env m s
      in
      FStar_Errors.raise_error uu____215 (FStar_Ident.range_of_lid m)
    in
    let s1 = FStar_Syntax_Subst.compress s in
    match s1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) -> (
        let bs1 = FStar_Syntax_Subst.open_binders bs in
        match bs1 with
        | [(a, uu____259); (wp, uu____261)] -> (a, wp.FStar_Syntax_Syntax.sort)
        | uu____276 -> fail () )
    | uu____277 -> fail ()


let tc_eff_decl
    : FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.eff_decl
      -> FStar_Syntax_Syntax.eff_decl =
  fun env0 ed ->
    let uu____284 =
      FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
    in
    match uu____284 with open_annotated_univs, annotated_univ_names ->
      let open_univs n_binders t =
        let uu____310 =
          FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
        in
        FStar_Syntax_Subst.subst uu____310 t
      in
      let open_univs_binders n_binders bs =
        let uu____320 =
          FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
        in
        FStar_Syntax_Subst.subst_binders uu____320 bs
      in
      let n_effect_params = FStar_List.length ed.FStar_Syntax_Syntax.binders in
      let uu____328 =
        let uu____335 =
          open_univs_binders (Prims.parse_int "0")
            ed.FStar_Syntax_Syntax.binders
        in
        let uu____336 =
          open_univs n_effect_params ed.FStar_Syntax_Syntax.signature
        in
        FStar_Syntax_Subst.open_term' uu____335 uu____336
      in
      match uu____328 with effect_params_un, signature_un, opening ->
        let uu____346 =
          FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
        in
        match uu____346 with effect_params, env, uu____355 ->
          let uu____356 =
            FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un
          in
          match uu____356 with signature, uu____362 ->
            let ed1 =
              let uu___63_364 = ed in
              { FStar_Syntax_Syntax.cattributes=
                  uu___63_364.FStar_Syntax_Syntax.cattributes
              ; FStar_Syntax_Syntax.mname=
                  uu___63_364.FStar_Syntax_Syntax.mname
              ; FStar_Syntax_Syntax.univs=
                  uu___63_364.FStar_Syntax_Syntax.univs
              ; FStar_Syntax_Syntax.binders= effect_params
              ; FStar_Syntax_Syntax.signature
              ; FStar_Syntax_Syntax.ret_wp=
                  uu___63_364.FStar_Syntax_Syntax.ret_wp
              ; FStar_Syntax_Syntax.bind_wp=
                  uu___63_364.FStar_Syntax_Syntax.bind_wp
              ; FStar_Syntax_Syntax.if_then_else=
                  uu___63_364.FStar_Syntax_Syntax.if_then_else
              ; FStar_Syntax_Syntax.ite_wp=
                  uu___63_364.FStar_Syntax_Syntax.ite_wp
              ; FStar_Syntax_Syntax.stronger=
                  uu___63_364.FStar_Syntax_Syntax.stronger
              ; FStar_Syntax_Syntax.close_wp=
                  uu___63_364.FStar_Syntax_Syntax.close_wp
              ; FStar_Syntax_Syntax.assert_p=
                  uu___63_364.FStar_Syntax_Syntax.assert_p
              ; FStar_Syntax_Syntax.assume_p=
                  uu___63_364.FStar_Syntax_Syntax.assume_p
              ; FStar_Syntax_Syntax.null_wp=
                  uu___63_364.FStar_Syntax_Syntax.null_wp
              ; FStar_Syntax_Syntax.trivial=
                  uu___63_364.FStar_Syntax_Syntax.trivial
              ; FStar_Syntax_Syntax.repr= uu___63_364.FStar_Syntax_Syntax.repr
              ; FStar_Syntax_Syntax.return_repr=
                  uu___63_364.FStar_Syntax_Syntax.return_repr
              ; FStar_Syntax_Syntax.bind_repr=
                  uu___63_364.FStar_Syntax_Syntax.bind_repr
              ; FStar_Syntax_Syntax.actions=
                  uu___63_364.FStar_Syntax_Syntax.actions }
            in
            let ed2 =
              match (effect_params, annotated_univ_names) with
              | [], [] -> ed1
              | uu____380 ->
                  let op uu____402 =
                    match uu____402 with us, t ->
                      let n_us = FStar_List.length us in
                      let uu____422 =
                        let uu____423 =
                          FStar_Syntax_Subst.shift_subst n_us opening
                        in
                        let uu____432 =
                          open_univs (n_effect_params + n_us) t
                        in
                        FStar_Syntax_Subst.subst uu____423 uu____432
                      in
                      (us, uu____422)
                  in
                  let uu___64_445 = ed1 in
                  let uu____446 = op ed1.FStar_Syntax_Syntax.ret_wp in
                  let uu____447 = op ed1.FStar_Syntax_Syntax.bind_wp in
                  let uu____448 = op ed1.FStar_Syntax_Syntax.if_then_else in
                  let uu____449 = op ed1.FStar_Syntax_Syntax.ite_wp in
                  let uu____450 = op ed1.FStar_Syntax_Syntax.stronger in
                  let uu____451 = op ed1.FStar_Syntax_Syntax.close_wp in
                  let uu____452 = op ed1.FStar_Syntax_Syntax.assert_p in
                  let uu____453 = op ed1.FStar_Syntax_Syntax.assume_p in
                  let uu____454 = op ed1.FStar_Syntax_Syntax.null_wp in
                  let uu____455 = op ed1.FStar_Syntax_Syntax.trivial in
                  let uu____456 =
                    let uu____457 = op ([], ed1.FStar_Syntax_Syntax.repr) in
                    FStar_Pervasives_Native.snd uu____457
                  in
                  let uu____468 = op ed1.FStar_Syntax_Syntax.return_repr in
                  let uu____469 = op ed1.FStar_Syntax_Syntax.bind_repr in
                  let uu____470 =
                    FStar_List.map
                      (fun a ->
                        let uu___65_478 = a in
                        let uu____479 =
                          let uu____480 =
                            op ([], a.FStar_Syntax_Syntax.action_defn)
                          in
                          FStar_Pervasives_Native.snd uu____480
                        in
                        let uu____491 =
                          let uu____492 =
                            op ([], a.FStar_Syntax_Syntax.action_typ)
                          in
                          FStar_Pervasives_Native.snd uu____492
                        in
                        { FStar_Syntax_Syntax.action_name=
                            uu___65_478.FStar_Syntax_Syntax.action_name
                        ; FStar_Syntax_Syntax.action_unqualified_name=
                            uu___65_478
                              .FStar_Syntax_Syntax.action_unqualified_name
                        ; FStar_Syntax_Syntax.action_univs=
                            uu___65_478.FStar_Syntax_Syntax.action_univs
                        ; FStar_Syntax_Syntax.action_params=
                            uu___65_478.FStar_Syntax_Syntax.action_params
                        ; FStar_Syntax_Syntax.action_defn= uu____479
                        ; FStar_Syntax_Syntax.action_typ= uu____491 } )
                      ed1.FStar_Syntax_Syntax.actions
                  in
                  { FStar_Syntax_Syntax.cattributes=
                      uu___64_445.FStar_Syntax_Syntax.cattributes
                  ; FStar_Syntax_Syntax.mname=
                      uu___64_445.FStar_Syntax_Syntax.mname
                  ; FStar_Syntax_Syntax.univs= annotated_univ_names
                  ; FStar_Syntax_Syntax.binders=
                      uu___64_445.FStar_Syntax_Syntax.binders
                  ; FStar_Syntax_Syntax.signature=
                      uu___64_445.FStar_Syntax_Syntax.signature
                  ; FStar_Syntax_Syntax.ret_wp= uu____446
                  ; FStar_Syntax_Syntax.bind_wp= uu____447
                  ; FStar_Syntax_Syntax.if_then_else= uu____448
                  ; FStar_Syntax_Syntax.ite_wp= uu____449
                  ; FStar_Syntax_Syntax.stronger= uu____450
                  ; FStar_Syntax_Syntax.close_wp= uu____451
                  ; FStar_Syntax_Syntax.assert_p= uu____452
                  ; FStar_Syntax_Syntax.assume_p= uu____453
                  ; FStar_Syntax_Syntax.null_wp= uu____454
                  ; FStar_Syntax_Syntax.trivial= uu____455
                  ; FStar_Syntax_Syntax.repr= uu____456
                  ; FStar_Syntax_Syntax.return_repr= uu____468
                  ; FStar_Syntax_Syntax.bind_repr= uu____469
                  ; FStar_Syntax_Syntax.actions= uu____470 }
            in
            let wp_with_fresh_result_type env1 mname signature1 =
              let fail t =
                let uu____529 =
                  FStar_TypeChecker_Err.unexpected_signature_for_monad env1
                    mname t
                in
                FStar_Errors.raise_error uu____529
                  (FStar_Ident.range_of_lid mname)
              in
              let uu____540 =
                let uu____541 = FStar_Syntax_Subst.compress signature1 in
                uu____541.FStar_Syntax_Syntax.n
              in
              match uu____540 with
              | FStar_Syntax_Syntax.Tm_arrow (bs, c) -> (
                  let bs1 = FStar_Syntax_Subst.open_binders bs in
                  match bs1 with
                  | [(a, uu____576); (wp, uu____578)] ->
                      (a, wp.FStar_Syntax_Syntax.sort)
                  | uu____593 -> fail signature1 )
              | uu____594 -> fail signature1
            in
            let uu____595 =
              wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname
                ed2.FStar_Syntax_Syntax.signature
            in
            match uu____595 with a, wp_a ->
              let fresh_effect_signature uu____617 =
                match annotated_univ_names with
                | [] -> (
                    let uu____624 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                    in
                    match uu____624 with signature1, uu____636 ->
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname signature1 )
                | uu____637 ->
                    let uu____640 =
                      let uu____645 =
                        let uu____646 =
                          FStar_Syntax_Subst.close_univ_vars
                            annotated_univ_names signature
                        in
                        (annotated_univ_names, uu____646)
                      in
                      FStar_TypeChecker_Env.inst_tscheme uu____645
                    in
                    match uu____640 with uu____655, signature1 ->
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname signature1
              in
              let env1 =
                let uu____658 =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    ed2.FStar_Syntax_Syntax.signature
                in
                FStar_TypeChecker_Env.push_bv env uu____658
              in
              (let uu____660 =
                 FStar_All.pipe_left
                   (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "ED")
               in
               if uu____660 then
                 let uu____661 =
                   FStar_Syntax_Print.lid_to_string
                     ed2.FStar_Syntax_Syntax.mname
                 in
                 let uu____662 =
                   FStar_Syntax_Print.binders_to_string " "
                     ed2.FStar_Syntax_Syntax.binders
                 in
                 let uu____663 =
                   FStar_Syntax_Print.term_to_string
                     ed2.FStar_Syntax_Syntax.signature
                 in
                 let uu____664 =
                   let uu____665 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Print.term_to_string uu____665
                 in
                 let uu____666 =
                   FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort
                 in
                 FStar_Util.print5
                   "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                   uu____661 uu____662 uu____663 uu____664 uu____666
               else ()) ;
              let check_and_gen' env2 uu____682 k =
                match uu____682 with us, t ->
                  match annotated_univ_names with
                  | [] -> check_and_gen env2 t k
                  | uu____696 :: uu____697 ->
                      let uu____700 =
                        FStar_Syntax_Subst.subst_tscheme open_annotated_univs
                          (us, t)
                      in
                      match uu____700 with us1, t1 ->
                        let uu____709 =
                          FStar_Syntax_Subst.open_univ_vars us1 t1
                        in
                        match uu____709 with us2, t2 ->
                          let uu____716 = tc_check_trivial_guard env2 t2 k in
                          let uu____717 =
                            FStar_Syntax_Subst.close_univ_vars us2 t2
                          in
                          (us2, uu____717)
              in
              let return_wp =
                let expected_k =
                  let uu____722 =
                    let uu____729 = FStar_Syntax_Syntax.mk_binder a in
                    let uu____730 =
                      let uu____733 =
                        let uu____734 = FStar_Syntax_Syntax.bv_to_name a in
                        FStar_Syntax_Syntax.null_binder uu____734
                      in
                      [uu____733]
                    in
                    uu____729 :: uu____730
                  in
                  let uu____735 = FStar_Syntax_Syntax.mk_GTotal wp_a in
                  FStar_Syntax_Util.arrow uu____722 uu____735
                in
                check_and_gen' env1 ed2.FStar_Syntax_Syntax.ret_wp expected_k
              in
              let bind_wp =
                let uu____739 = fresh_effect_signature () in
                match uu____739 with b, wp_b ->
                  let a_wp_b =
                    let uu____755 =
                      let uu____762 =
                        let uu____763 = FStar_Syntax_Syntax.bv_to_name a in
                        FStar_Syntax_Syntax.null_binder uu____763
                      in
                      [uu____762]
                    in
                    let uu____764 = FStar_Syntax_Syntax.mk_Total wp_b in
                    FStar_Syntax_Util.arrow uu____755 uu____764
                  in
                  let expected_k =
                    let uu____770 =
                      let uu____777 =
                        FStar_Syntax_Syntax.null_binder
                          FStar_Syntax_Syntax.t_range
                      in
                      let uu____778 =
                        let uu____781 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____782 =
                          let uu____785 = FStar_Syntax_Syntax.mk_binder b in
                          let uu____786 =
                            let uu____789 =
                              FStar_Syntax_Syntax.null_binder wp_a
                            in
                            let uu____790 =
                              let uu____793 =
                                FStar_Syntax_Syntax.null_binder a_wp_b
                              in
                              [uu____793]
                            in
                            uu____789 :: uu____790
                          in
                          uu____785 :: uu____786
                        in
                        uu____781 :: uu____782
                      in
                      uu____777 :: uu____778
                    in
                    let uu____794 = FStar_Syntax_Syntax.mk_Total wp_b in
                    FStar_Syntax_Util.arrow uu____770 uu____794
                  in
                  check_and_gen' env1 ed2.FStar_Syntax_Syntax.bind_wp
                    expected_k
              in
              let if_then_else1 =
                let p =
                  let uu____799 =
                    let uu____800 = FStar_Syntax_Util.type_u () in
                    FStar_All.pipe_right uu____800 FStar_Pervasives_Native.fst
                  in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some
                       (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))
                    uu____799
                in
                let expected_k =
                  let uu____812 =
                    let uu____819 = FStar_Syntax_Syntax.mk_binder a in
                    let uu____820 =
                      let uu____823 = FStar_Syntax_Syntax.mk_binder p in
                      let uu____824 =
                        let uu____827 = FStar_Syntax_Syntax.null_binder wp_a in
                        let uu____828 =
                          let uu____831 =
                            FStar_Syntax_Syntax.null_binder wp_a
                          in
                          [uu____831]
                        in
                        uu____827 :: uu____828
                      in
                      uu____823 :: uu____824
                    in
                    uu____819 :: uu____820
                  in
                  let uu____832 = FStar_Syntax_Syntax.mk_Total wp_a in
                  FStar_Syntax_Util.arrow uu____812 uu____832
                in
                check_and_gen' env1 ed2.FStar_Syntax_Syntax.if_then_else
                  expected_k
              in
              let ite_wp =
                let expected_k =
                  let uu____839 =
                    let uu____846 = FStar_Syntax_Syntax.mk_binder a in
                    let uu____847 =
                      let uu____850 = FStar_Syntax_Syntax.null_binder wp_a in
                      [uu____850]
                    in
                    uu____846 :: uu____847
                  in
                  let uu____851 = FStar_Syntax_Syntax.mk_Total wp_a in
                  FStar_Syntax_Util.arrow uu____839 uu____851
                in
                check_and_gen' env1 ed2.FStar_Syntax_Syntax.ite_wp expected_k
              in
              let stronger =
                let uu____855 = FStar_Syntax_Util.type_u () in
                match uu____855 with t, uu____861 ->
                  let expected_k =
                    let uu____865 =
                      let uu____872 = FStar_Syntax_Syntax.mk_binder a in
                      let uu____873 =
                        let uu____876 = FStar_Syntax_Syntax.null_binder wp_a in
                        let uu____877 =
                          let uu____880 =
                            FStar_Syntax_Syntax.null_binder wp_a
                          in
                          [uu____880]
                        in
                        uu____876 :: uu____877
                      in
                      uu____872 :: uu____873
                    in
                    let uu____881 = FStar_Syntax_Syntax.mk_Total t in
                    FStar_Syntax_Util.arrow uu____865 uu____881
                  in
                  check_and_gen' env1 ed2.FStar_Syntax_Syntax.stronger
                    expected_k
              in
              let close_wp =
                let b =
                  let uu____886 =
                    let uu____887 = FStar_Syntax_Util.type_u () in
                    FStar_All.pipe_right uu____887 FStar_Pervasives_Native.fst
                  in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some
                       (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))
                    uu____886
                in
                let b_wp_a =
                  let uu____899 =
                    let uu____906 =
                      let uu____907 = FStar_Syntax_Syntax.bv_to_name b in
                      FStar_Syntax_Syntax.null_binder uu____907
                    in
                    [uu____906]
                  in
                  let uu____908 = FStar_Syntax_Syntax.mk_Total wp_a in
                  FStar_Syntax_Util.arrow uu____899 uu____908
                in
                let expected_k =
                  let uu____914 =
                    let uu____921 = FStar_Syntax_Syntax.mk_binder a in
                    let uu____922 =
                      let uu____925 = FStar_Syntax_Syntax.mk_binder b in
                      let uu____926 =
                        let uu____929 =
                          FStar_Syntax_Syntax.null_binder b_wp_a
                        in
                        [uu____929]
                      in
                      uu____925 :: uu____926
                    in
                    uu____921 :: uu____922
                  in
                  let uu____930 = FStar_Syntax_Syntax.mk_Total wp_a in
                  FStar_Syntax_Util.arrow uu____914 uu____930
                in
                check_and_gen' env1 ed2.FStar_Syntax_Syntax.close_wp expected_k
              in
              let assert_p =
                let expected_k =
                  let uu____937 =
                    let uu____944 = FStar_Syntax_Syntax.mk_binder a in
                    let uu____945 =
                      let uu____948 =
                        let uu____949 =
                          let uu____950 = FStar_Syntax_Util.type_u () in
                          FStar_All.pipe_right uu____950
                            FStar_Pervasives_Native.fst
                        in
                        FStar_Syntax_Syntax.null_binder uu____949
                      in
                      let uu____959 =
                        let uu____962 = FStar_Syntax_Syntax.null_binder wp_a in
                        [uu____962]
                      in
                      uu____948 :: uu____959
                    in
                    uu____944 :: uu____945
                  in
                  let uu____963 = FStar_Syntax_Syntax.mk_Total wp_a in
                  FStar_Syntax_Util.arrow uu____937 uu____963
                in
                check_and_gen' env1 ed2.FStar_Syntax_Syntax.assert_p expected_k
              in
              let assume_p =
                let expected_k =
                  let uu____970 =
                    let uu____977 = FStar_Syntax_Syntax.mk_binder a in
                    let uu____978 =
                      let uu____981 =
                        let uu____982 =
                          let uu____983 = FStar_Syntax_Util.type_u () in
                          FStar_All.pipe_right uu____983
                            FStar_Pervasives_Native.fst
                        in
                        FStar_Syntax_Syntax.null_binder uu____982
                      in
                      let uu____992 =
                        let uu____995 = FStar_Syntax_Syntax.null_binder wp_a in
                        [uu____995]
                      in
                      uu____981 :: uu____992
                    in
                    uu____977 :: uu____978
                  in
                  let uu____996 = FStar_Syntax_Syntax.mk_Total wp_a in
                  FStar_Syntax_Util.arrow uu____970 uu____996
                in
                check_and_gen' env1 ed2.FStar_Syntax_Syntax.assume_p expected_k
              in
              let null_wp =
                let expected_k =
                  let uu____1003 =
                    let uu____1010 = FStar_Syntax_Syntax.mk_binder a in
                    [uu____1010]
                  in
                  let uu____1011 = FStar_Syntax_Syntax.mk_Total wp_a in
                  FStar_Syntax_Util.arrow uu____1003 uu____1011
                in
                check_and_gen' env1 ed2.FStar_Syntax_Syntax.null_wp expected_k
              in
              let trivial_wp =
                let uu____1015 = FStar_Syntax_Util.type_u () in
                match uu____1015 with t, uu____1021 ->
                  let expected_k =
                    let uu____1025 =
                      let uu____1032 = FStar_Syntax_Syntax.mk_binder a in
                      let uu____1033 =
                        let uu____1036 =
                          FStar_Syntax_Syntax.null_binder wp_a
                        in
                        [uu____1036]
                      in
                      uu____1032 :: uu____1033
                    in
                    let uu____1037 = FStar_Syntax_Syntax.mk_GTotal t in
                    FStar_Syntax_Util.arrow uu____1025 uu____1037
                  in
                  check_and_gen' env1 ed2.FStar_Syntax_Syntax.trivial
                    expected_k
              in
              let uu____1040 =
                let uu____1051 =
                  let uu____1052 =
                    FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr
                  in
                  uu____1052.FStar_Syntax_Syntax.n
                in
                match uu____1051 with
                | FStar_Syntax_Syntax.Tm_unknown ->
                    ( ed2.FStar_Syntax_Syntax.repr
                    , ed2.FStar_Syntax_Syntax.bind_repr
                    , ed2.FStar_Syntax_Syntax.return_repr
                    , ed2.FStar_Syntax_Syntax.actions )
                | uu____1067 ->
                    let repr =
                      let uu____1069 = FStar_Syntax_Util.type_u () in
                      match uu____1069 with t, uu____1075 ->
                        let expected_k =
                          let uu____1079 =
                            let uu____1086 = FStar_Syntax_Syntax.mk_binder a in
                            let uu____1087 =
                              let uu____1090 =
                                FStar_Syntax_Syntax.null_binder wp_a
                              in
                              [uu____1090]
                            in
                            uu____1086 :: uu____1087
                          in
                          let uu____1091 = FStar_Syntax_Syntax.mk_GTotal t in
                          FStar_Syntax_Util.arrow uu____1079 uu____1091
                        in
                        tc_check_trivial_guard env1
                          ed2.FStar_Syntax_Syntax.repr expected_k
                    in
                    let mk_repr' t wp =
                      let repr1 =
                        FStar_TypeChecker_Normalize.normalize
                          [ FStar_TypeChecker_Normalize.EraseUniverses
                          ; FStar_TypeChecker_Normalize.AllowUnboundUniverses
                          ] env1 repr
                      in
                      let uu____1104 =
                        let uu____1107 =
                          let uu____1108 =
                            let uu____1123 =
                              let uu____1126 = FStar_Syntax_Syntax.as_arg t in
                              let uu____1127 =
                                let uu____1130 =
                                  FStar_Syntax_Syntax.as_arg wp
                                in
                                [uu____1130]
                              in
                              uu____1126 :: uu____1127
                            in
                            (repr1, uu____1123)
                          in
                          FStar_Syntax_Syntax.Tm_app uu____1108
                        in
                        FStar_Syntax_Syntax.mk uu____1107
                      in
                      uu____1104 FStar_Pervasives_Native.None
                        FStar_Range.dummyRange
                    in
                    let mk_repr a1 wp =
                      let uu____1145 = FStar_Syntax_Syntax.bv_to_name a1 in
                      mk_repr' uu____1145 wp
                    in
                    let destruct_repr t =
                      let uu____1158 =
                        let uu____1159 = FStar_Syntax_Subst.compress t in
                        uu____1159.FStar_Syntax_Syntax.n
                      in
                      match uu____1158 with
                      | FStar_Syntax_Syntax.Tm_app
                          (uu____1170, [(t1, uu____1172); (wp, uu____1174)]) ->
                          (t1, wp)
                      | uu____1217 -> failwith "Unexpected repr type"
                    in
                    let bind_repr =
                      let r =
                        let uu____1228 =
                          FStar_Syntax_Syntax.lid_as_fv
                            FStar_Parser_Const.range_0
                            FStar_Syntax_Syntax.Delta_constant
                            FStar_Pervasives_Native.None
                        in
                        FStar_All.pipe_right uu____1228
                          FStar_Syntax_Syntax.fv_to_tm
                      in
                      let uu____1229 = fresh_effect_signature () in
                      match uu____1229 with b, wp_b ->
                        let a_wp_b =
                          let uu____1245 =
                            let uu____1252 =
                              let uu____1253 =
                                FStar_Syntax_Syntax.bv_to_name a
                              in
                              FStar_Syntax_Syntax.null_binder uu____1253
                            in
                            [uu____1252]
                          in
                          let uu____1254 = FStar_Syntax_Syntax.mk_Total wp_b in
                          FStar_Syntax_Util.arrow uu____1245 uu____1254
                        in
                        let wp_f =
                          FStar_Syntax_Syntax.gen_bv "wp_f"
                            FStar_Pervasives_Native.None wp_a
                        in
                        let wp_g =
                          FStar_Syntax_Syntax.gen_bv "wp_g"
                            FStar_Pervasives_Native.None a_wp_b
                        in
                        let x_a =
                          let uu____1260 = FStar_Syntax_Syntax.bv_to_name a in
                          FStar_Syntax_Syntax.gen_bv "x_a"
                            FStar_Pervasives_Native.None uu____1260
                        in
                        let wp_g_x =
                          let uu____1264 =
                            let uu____1265 =
                              FStar_Syntax_Syntax.bv_to_name wp_g
                            in
                            let uu____1266 =
                              let uu____1267 =
                                let uu____1268 =
                                  FStar_Syntax_Syntax.bv_to_name x_a
                                in
                                FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                                  uu____1268
                              in
                              [uu____1267]
                            in
                            FStar_Syntax_Syntax.mk_Tm_app uu____1265 uu____1266
                          in
                          uu____1264 FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                        in
                        let res =
                          let wp =
                            let uu____1277 =
                              let uu____1278 =
                                let uu____1279 =
                                  FStar_TypeChecker_Env.inst_tscheme bind_wp
                                in
                                FStar_All.pipe_right uu____1279
                                  FStar_Pervasives_Native.snd
                              in
                              let uu____1288 =
                                let uu____1289 =
                                  let uu____1292 =
                                    let uu____1295 =
                                      FStar_Syntax_Syntax.bv_to_name a
                                    in
                                    let uu____1296 =
                                      let uu____1299 =
                                        FStar_Syntax_Syntax.bv_to_name b
                                      in
                                      let uu____1300 =
                                        let uu____1303 =
                                          FStar_Syntax_Syntax.bv_to_name wp_f
                                        in
                                        let uu____1304 =
                                          let uu____1307 =
                                            FStar_Syntax_Syntax.bv_to_name wp_g
                                          in
                                          [uu____1307]
                                        in
                                        uu____1303 :: uu____1304
                                      in
                                      uu____1299 :: uu____1300
                                    in
                                    uu____1295 :: uu____1296
                                  in
                                  r :: uu____1292
                                in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1289
                              in
                              FStar_Syntax_Syntax.mk_Tm_app uu____1278
                                uu____1288
                            in
                            uu____1277 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange
                          in
                          mk_repr b wp
                        in
                        let expected_k =
                          let uu____1313 =
                            let uu____1320 = FStar_Syntax_Syntax.mk_binder a in
                            let uu____1321 =
                              let uu____1324 =
                                FStar_Syntax_Syntax.mk_binder b
                              in
                              let uu____1325 =
                                let uu____1328 =
                                  FStar_Syntax_Syntax.mk_binder wp_f
                                in
                                let uu____1329 =
                                  let uu____1332 =
                                    let uu____1333 =
                                      let uu____1334 =
                                        FStar_Syntax_Syntax.bv_to_name wp_f
                                      in
                                      mk_repr a uu____1334
                                    in
                                    FStar_Syntax_Syntax.null_binder uu____1333
                                  in
                                  let uu____1335 =
                                    let uu____1338 =
                                      FStar_Syntax_Syntax.mk_binder wp_g
                                    in
                                    let uu____1339 =
                                      let uu____1342 =
                                        let uu____1343 =
                                          let uu____1344 =
                                            let uu____1351 =
                                              FStar_Syntax_Syntax.mk_binder x_a
                                            in
                                            [uu____1351]
                                          in
                                          let uu____1352 =
                                            let uu____1355 =
                                              mk_repr b wp_g_x
                                            in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.mk_Total
                                              uu____1355
                                          in
                                          FStar_Syntax_Util.arrow uu____1344
                                            uu____1352
                                        in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1343
                                      in
                                      [uu____1342]
                                    in
                                    uu____1338 :: uu____1339
                                  in
                                  uu____1332 :: uu____1335
                                in
                                uu____1328 :: uu____1329
                              in
                              uu____1324 :: uu____1325
                            in
                            uu____1320 :: uu____1321
                          in
                          let uu____1356 = FStar_Syntax_Syntax.mk_Total res in
                          FStar_Syntax_Util.arrow uu____1313 uu____1356
                        in
                        let uu____1359 =
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                            expected_k
                        in
                        match uu____1359
                        with expected_k1, uu____1367, uu____1368 ->
                          let env2 =
                            FStar_TypeChecker_Env.set_range env1
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.bind_repr)
                                .FStar_Syntax_Syntax.pos
                          in
                          let env3 =
                            let uu___66_1373 = env2 in
                            { FStar_TypeChecker_Env.solver=
                                uu___66_1373.FStar_TypeChecker_Env.solver
                            ; FStar_TypeChecker_Env.range=
                                uu___66_1373.FStar_TypeChecker_Env.range
                            ; FStar_TypeChecker_Env.curmodule=
                                uu___66_1373.FStar_TypeChecker_Env.curmodule
                            ; FStar_TypeChecker_Env.gamma=
                                uu___66_1373.FStar_TypeChecker_Env.gamma
                            ; FStar_TypeChecker_Env.gamma_cache=
                                uu___66_1373.FStar_TypeChecker_Env.gamma_cache
                            ; FStar_TypeChecker_Env.modules=
                                uu___66_1373.FStar_TypeChecker_Env.modules
                            ; FStar_TypeChecker_Env.expected_typ=
                                uu___66_1373.FStar_TypeChecker_Env.expected_typ
                            ; FStar_TypeChecker_Env.sigtab=
                                uu___66_1373.FStar_TypeChecker_Env.sigtab
                            ; FStar_TypeChecker_Env.is_pattern=
                                uu___66_1373.FStar_TypeChecker_Env.is_pattern
                            ; FStar_TypeChecker_Env.instantiate_imp=
                                uu___66_1373
                                  .FStar_TypeChecker_Env.instantiate_imp
                            ; FStar_TypeChecker_Env.effects=
                                uu___66_1373.FStar_TypeChecker_Env.effects
                            ; FStar_TypeChecker_Env.generalize=
                                uu___66_1373.FStar_TypeChecker_Env.generalize
                            ; FStar_TypeChecker_Env.letrecs=
                                uu___66_1373.FStar_TypeChecker_Env.letrecs
                            ; FStar_TypeChecker_Env.top_level=
                                uu___66_1373.FStar_TypeChecker_Env.top_level
                            ; FStar_TypeChecker_Env.check_uvars=
                                uu___66_1373.FStar_TypeChecker_Env.check_uvars
                            ; FStar_TypeChecker_Env.use_eq=
                                uu___66_1373.FStar_TypeChecker_Env.use_eq
                            ; FStar_TypeChecker_Env.is_iface=
                                uu___66_1373.FStar_TypeChecker_Env.is_iface
                            ; FStar_TypeChecker_Env.admit=
                                uu___66_1373.FStar_TypeChecker_Env.admit
                            ; FStar_TypeChecker_Env.lax= true
                            ; FStar_TypeChecker_Env.lax_universes=
                                uu___66_1373
                                  .FStar_TypeChecker_Env.lax_universes
                            ; FStar_TypeChecker_Env.failhard=
                                uu___66_1373.FStar_TypeChecker_Env.failhard
                            ; FStar_TypeChecker_Env.nosynth=
                                uu___66_1373.FStar_TypeChecker_Env.nosynth
                            ; FStar_TypeChecker_Env.tc_term=
                                uu___66_1373.FStar_TypeChecker_Env.tc_term
                            ; FStar_TypeChecker_Env.type_of=
                                uu___66_1373.FStar_TypeChecker_Env.type_of
                            ; FStar_TypeChecker_Env.universe_of=
                                uu___66_1373.FStar_TypeChecker_Env.universe_of
                            ; FStar_TypeChecker_Env.check_type_of=
                                uu___66_1373
                                  .FStar_TypeChecker_Env.check_type_of
                            ; FStar_TypeChecker_Env.use_bv_sorts=
                                uu___66_1373.FStar_TypeChecker_Env.use_bv_sorts
                            ; FStar_TypeChecker_Env.qname_and_index=
                                uu___66_1373
                                  .FStar_TypeChecker_Env.qname_and_index
                            ; FStar_TypeChecker_Env.proof_ns=
                                uu___66_1373.FStar_TypeChecker_Env.proof_ns
                            ; FStar_TypeChecker_Env.synth=
                                uu___66_1373.FStar_TypeChecker_Env.synth
                            ; FStar_TypeChecker_Env.is_native_tactic=
                                uu___66_1373
                                  .FStar_TypeChecker_Env.is_native_tactic
                            ; FStar_TypeChecker_Env.identifier_info=
                                uu___66_1373
                                  .FStar_TypeChecker_Env.identifier_info
                            ; FStar_TypeChecker_Env.tc_hooks=
                                uu___66_1373.FStar_TypeChecker_Env.tc_hooks
                            ; FStar_TypeChecker_Env.dsenv=
                                uu___66_1373.FStar_TypeChecker_Env.dsenv
                            ; FStar_TypeChecker_Env.dep_graph=
                                uu___66_1373.FStar_TypeChecker_Env.dep_graph }
                          in
                          let br =
                            check_and_gen' env3
                              ed2.FStar_Syntax_Syntax.bind_repr expected_k1
                          in
                          br
                    in
                    let return_repr =
                      let x_a =
                        let uu____1383 = FStar_Syntax_Syntax.bv_to_name a in
                        FStar_Syntax_Syntax.gen_bv "x_a"
                          FStar_Pervasives_Native.None uu____1383
                      in
                      let res =
                        let wp =
                          let uu____1390 =
                            let uu____1391 =
                              let uu____1392 =
                                FStar_TypeChecker_Env.inst_tscheme return_wp
                              in
                              FStar_All.pipe_right uu____1392
                                FStar_Pervasives_Native.snd
                            in
                            let uu____1401 =
                              let uu____1402 =
                                let uu____1405 =
                                  FStar_Syntax_Syntax.bv_to_name a
                                in
                                let uu____1406 =
                                  let uu____1409 =
                                    FStar_Syntax_Syntax.bv_to_name x_a
                                  in
                                  [uu____1409]
                                in
                                uu____1405 :: uu____1406
                              in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1402
                            in
                            FStar_Syntax_Syntax.mk_Tm_app uu____1391 uu____1401
                          in
                          uu____1390 FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                        in
                        mk_repr a wp
                      in
                      let expected_k =
                        let uu____1415 =
                          let uu____1422 = FStar_Syntax_Syntax.mk_binder a in
                          let uu____1423 =
                            let uu____1426 =
                              FStar_Syntax_Syntax.mk_binder x_a
                            in
                            [uu____1426]
                          in
                          uu____1422 :: uu____1423
                        in
                        let uu____1427 = FStar_Syntax_Syntax.mk_Total res in
                        FStar_Syntax_Util.arrow uu____1415 uu____1427
                      in
                      let uu____1430 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                          expected_k
                      in
                      match uu____1430
                      with expected_k1, uu____1444, uu____1445 ->
                        let env2 =
                          FStar_TypeChecker_Env.set_range env1
                            (FStar_Pervasives_Native.snd
                               ed2.FStar_Syntax_Syntax.return_repr)
                              .FStar_Syntax_Syntax.pos
                        in
                        let uu____1449 =
                          check_and_gen' env2
                            ed2.FStar_Syntax_Syntax.return_repr expected_k1
                        in
                        match uu____1449 with univs1, repr1 ->
                          match univs1 with
                          | [] -> ([], repr1)
                          | uu____1470 ->
                              FStar_Errors.raise_error
                                ( FStar_Errors.
                                  Fatal_UnexpectedUniversePolymorphicReturn
                                , "Unexpected universe-polymorphic return for effect"
                                ) repr1.FStar_Syntax_Syntax.pos
                    in
                    let actions =
                      let check_action act =
                        let uu____1495 =
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                            act.FStar_Syntax_Syntax.action_typ
                        in
                        match uu____1495 with act_typ, uu____1503, g_t ->
                          let env' =
                            let uu___67_1506 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ
                            in
                            { FStar_TypeChecker_Env.solver=
                                uu___67_1506.FStar_TypeChecker_Env.solver
                            ; FStar_TypeChecker_Env.range=
                                uu___67_1506.FStar_TypeChecker_Env.range
                            ; FStar_TypeChecker_Env.curmodule=
                                uu___67_1506.FStar_TypeChecker_Env.curmodule
                            ; FStar_TypeChecker_Env.gamma=
                                uu___67_1506.FStar_TypeChecker_Env.gamma
                            ; FStar_TypeChecker_Env.gamma_cache=
                                uu___67_1506.FStar_TypeChecker_Env.gamma_cache
                            ; FStar_TypeChecker_Env.modules=
                                uu___67_1506.FStar_TypeChecker_Env.modules
                            ; FStar_TypeChecker_Env.expected_typ=
                                uu___67_1506.FStar_TypeChecker_Env.expected_typ
                            ; FStar_TypeChecker_Env.sigtab=
                                uu___67_1506.FStar_TypeChecker_Env.sigtab
                            ; FStar_TypeChecker_Env.is_pattern=
                                uu___67_1506.FStar_TypeChecker_Env.is_pattern
                            ; FStar_TypeChecker_Env.instantiate_imp= false
                            ; FStar_TypeChecker_Env.effects=
                                uu___67_1506.FStar_TypeChecker_Env.effects
                            ; FStar_TypeChecker_Env.generalize=
                                uu___67_1506.FStar_TypeChecker_Env.generalize
                            ; FStar_TypeChecker_Env.letrecs=
                                uu___67_1506.FStar_TypeChecker_Env.letrecs
                            ; FStar_TypeChecker_Env.top_level=
                                uu___67_1506.FStar_TypeChecker_Env.top_level
                            ; FStar_TypeChecker_Env.check_uvars=
                                uu___67_1506.FStar_TypeChecker_Env.check_uvars
                            ; FStar_TypeChecker_Env.use_eq=
                                uu___67_1506.FStar_TypeChecker_Env.use_eq
                            ; FStar_TypeChecker_Env.is_iface=
                                uu___67_1506.FStar_TypeChecker_Env.is_iface
                            ; FStar_TypeChecker_Env.admit=
                                uu___67_1506.FStar_TypeChecker_Env.admit
                            ; FStar_TypeChecker_Env.lax=
                                uu___67_1506.FStar_TypeChecker_Env.lax
                            ; FStar_TypeChecker_Env.lax_universes=
                                uu___67_1506
                                  .FStar_TypeChecker_Env.lax_universes
                            ; FStar_TypeChecker_Env.failhard=
                                uu___67_1506.FStar_TypeChecker_Env.failhard
                            ; FStar_TypeChecker_Env.nosynth=
                                uu___67_1506.FStar_TypeChecker_Env.nosynth
                            ; FStar_TypeChecker_Env.tc_term=
                                uu___67_1506.FStar_TypeChecker_Env.tc_term
                            ; FStar_TypeChecker_Env.type_of=
                                uu___67_1506.FStar_TypeChecker_Env.type_of
                            ; FStar_TypeChecker_Env.universe_of=
                                uu___67_1506.FStar_TypeChecker_Env.universe_of
                            ; FStar_TypeChecker_Env.check_type_of=
                                uu___67_1506
                                  .FStar_TypeChecker_Env.check_type_of
                            ; FStar_TypeChecker_Env.use_bv_sorts=
                                uu___67_1506.FStar_TypeChecker_Env.use_bv_sorts
                            ; FStar_TypeChecker_Env.qname_and_index=
                                uu___67_1506
                                  .FStar_TypeChecker_Env.qname_and_index
                            ; FStar_TypeChecker_Env.proof_ns=
                                uu___67_1506.FStar_TypeChecker_Env.proof_ns
                            ; FStar_TypeChecker_Env.synth=
                                uu___67_1506.FStar_TypeChecker_Env.synth
                            ; FStar_TypeChecker_Env.is_native_tactic=
                                uu___67_1506
                                  .FStar_TypeChecker_Env.is_native_tactic
                            ; FStar_TypeChecker_Env.identifier_info=
                                uu___67_1506
                                  .FStar_TypeChecker_Env.identifier_info
                            ; FStar_TypeChecker_Env.tc_hooks=
                                uu___67_1506.FStar_TypeChecker_Env.tc_hooks
                            ; FStar_TypeChecker_Env.dsenv=
                                uu___67_1506.FStar_TypeChecker_Env.dsenv
                            ; FStar_TypeChecker_Env.dep_graph=
                                uu___67_1506.FStar_TypeChecker_Env.dep_graph }
                          in
                          (let uu____1508 =
                             FStar_TypeChecker_Env.debug env1
                               (FStar_Options.Other "ED")
                           in
                           if uu____1508 then
                             let uu____1509 =
                               FStar_Syntax_Print.term_to_string
                                 act.FStar_Syntax_Syntax.action_defn
                             in
                             let uu____1510 =
                               FStar_Syntax_Print.term_to_string act_typ
                             in
                             FStar_Util.print3
                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                               (FStar_Ident.text_of_lid
                                  act.FStar_Syntax_Syntax.action_name)
                               uu____1509 uu____1510
                           else ()) ;
                          let uu____1512 =
                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env'
                              act.FStar_Syntax_Syntax.action_defn
                          in
                          match uu____1512 with act_defn, uu____1520, g_a ->
                            let act_defn1 =
                              FStar_TypeChecker_Normalize.normalize
                                [ FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant ] env1
                                act_defn
                            in
                            let act_typ1 =
                              FStar_TypeChecker_Normalize.normalize
                                [ FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant
                                ; FStar_TypeChecker_Normalize.Eager_unfolding
                                ; FStar_TypeChecker_Normalize.Beta ] env1
                                act_typ
                            in
                            let uu____1524 =
                              let act_typ2 =
                                FStar_Syntax_Subst.compress act_typ1
                              in
                              match act_typ2.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, c) -> (
                                  let uu____1552 =
                                    FStar_Syntax_Subst.open_comp bs c
                                  in
                                  match uu____1552 with bs1, uu____1562 ->
                                    let res =
                                      mk_repr' FStar_Syntax_Syntax.tun
                                        FStar_Syntax_Syntax.tun
                                    in
                                    let k =
                                      let uu____1569 =
                                        FStar_Syntax_Syntax.mk_Total res
                                      in
                                      FStar_Syntax_Util.arrow bs1 uu____1569
                                    in
                                    let uu____1572 =
                                      FStar_TypeChecker_TcTerm.
                                      tc_tot_or_gtot_term env1 k
                                    in
                                    match uu____1572
                                    with k1, uu____1584, g -> (k1, g) )
                              | uu____1586 ->
                                  let uu____1587 =
                                    let uu____1592 =
                                      let uu____1593 =
                                        FStar_Syntax_Print.term_to_string
                                          act_typ2
                                      in
                                      let uu____1594 =
                                        FStar_Syntax_Print.tag_of_term act_typ2
                                      in
                                      FStar_Util.format2
                                        "Actions must have function types (not: %s, a.k.a. %s)"
                                        uu____1593 uu____1594
                                    in
                                    ( FStar_Errors.
                                      Fatal_ActionMustHaveFunctionType
                                    , uu____1592 )
                                  in
                                  FStar_Errors.raise_error uu____1587
                                    act_defn1.FStar_Syntax_Syntax.pos
                            in
                            match uu____1524 with expected_k, g_k ->
                              let g =
                                FStar_TypeChecker_Rel.teq env1 act_typ1
                                  expected_k
                              in
                              (let uu____1603 =
                                 let uu____1604 =
                                   let uu____1605 =
                                     FStar_TypeChecker_Rel.conj_guard g_t g
                                   in
                                   FStar_TypeChecker_Rel.conj_guard g_k
                                     uu____1605
                                 in
                                 FStar_TypeChecker_Rel.conj_guard g_a
                                   uu____1604
                               in
                               FStar_TypeChecker_Rel.force_trivial_guard env1
                                 uu____1603) ;
                              let act_typ2 =
                                let uu____1609 =
                                  let uu____1610 =
                                    FStar_Syntax_Subst.compress expected_k
                                  in
                                  uu____1610.FStar_Syntax_Syntax.n
                                in
                                match uu____1609 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs, c) -> (
                                    let uu____1633 =
                                      FStar_Syntax_Subst.open_comp bs c
                                    in
                                    match uu____1633 with bs1, c1 ->
                                      let uu____1642 =
                                        destruct_repr
                                          (FStar_Syntax_Util.comp_result c1)
                                      in
                                      match uu____1642 with a1, wp ->
                                        let c2 =
                                          let uu____1664 =
                                            let uu____1665 =
                                              env1
                                                .FStar_TypeChecker_Env.
                                                 universe_of env1 a1
                                            in
                                            [uu____1665]
                                          in
                                          let uu____1666 =
                                            let uu____1675 =
                                              FStar_Syntax_Syntax.as_arg wp
                                            in
                                            [uu____1675]
                                          in
                                          { FStar_Syntax_Syntax.comp_univs=
                                              uu____1664
                                          ; FStar_Syntax_Syntax.effect_name=
                                              ed2.FStar_Syntax_Syntax.mname
                                          ; FStar_Syntax_Syntax.result_typ= a1
                                          ; FStar_Syntax_Syntax.effect_args=
                                              uu____1666
                                          ; FStar_Syntax_Syntax.flags= [] }
                                        in
                                        let uu____1676 =
                                          FStar_Syntax_Syntax.mk_Comp c2
                                        in
                                        FStar_Syntax_Util.arrow bs1 uu____1676
                                    )
                                | uu____1679 ->
                                    failwith
                                      "Impossible (expected_k is an arrow)"
                              in
                              let uu____1682 =
                                FStar_TypeChecker_Util.generalize_universes
                                  env1 act_defn1
                              in
                              match uu____1682 with univs1, act_defn2 ->
                                let act_typ3 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    act_typ2
                                in
                                let act_typ4 =
                                  FStar_Syntax_Subst.close_univ_vars univs1
                                    act_typ3
                                in
                                let uu___68_1691 = act in
                                { FStar_Syntax_Syntax.action_name=
                                    uu___68_1691
                                      .FStar_Syntax_Syntax.action_name
                                ; FStar_Syntax_Syntax.action_unqualified_name=
                                    uu___68_1691
                                      .FStar_Syntax_Syntax.
                                       action_unqualified_name
                                ; FStar_Syntax_Syntax.action_univs= univs1
                                ; FStar_Syntax_Syntax.action_params=
                                    uu___68_1691
                                      .FStar_Syntax_Syntax.action_params
                                ; FStar_Syntax_Syntax.action_defn= act_defn2
                                ; FStar_Syntax_Syntax.action_typ= act_typ4 }
                      in
                      FStar_All.pipe_right ed2.FStar_Syntax_Syntax.actions
                        (FStar_List.map check_action)
                    in
                    (repr, bind_repr, return_repr, actions)
              in
              match uu____1040 with repr, bind_repr, return_repr, actions ->
                let t0 =
                  let uu____1715 =
                    FStar_Syntax_Syntax.mk_Total
                      ed2.FStar_Syntax_Syntax.signature
                  in
                  FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders
                    uu____1715
                in
                let uu____1718 =
                  let uu____1725 =
                    FStar_TypeChecker_Util.generalize_universes env0 t0
                  in
                  match uu____1725 with gen_univs, t ->
                    match annotated_univ_names with
                    | [] -> (gen_univs, t)
                    | uu____1746 ->
                        let uu____1749 =
                          FStar_List.length gen_univs
                          = FStar_List.length annotated_univ_names
                          && FStar_List.forall2
                               (fun u1 u2 ->
                                 FStar_Syntax_Syntax.order_univ_name u1 u2
                                 = Prims.parse_int "0" )
                               gen_univs annotated_univ_names
                        in
                        if uu____1749 then (gen_univs, t)
                        else
                          let uu____1763 =
                            let uu____1768 =
                              let uu____1769 =
                                FStar_Util.string_of_int
                                  (FStar_List.length annotated_univ_names)
                              in
                              let uu____1770 =
                                FStar_Util.string_of_int
                                  (FStar_List.length gen_univs)
                              in
                              FStar_Util.format2
                                "Expected an effect definition with %s universes; but found %s"
                                uu____1769 uu____1770
                            in
                            ( FStar_Errors.Fatal_UnexpectedNumberOfUniverse
                            , uu____1768 )
                          in
                          FStar_Errors.raise_error uu____1763
                            ed2.FStar_Syntax_Syntax.signature
                              .FStar_Syntax_Syntax.pos
                in
                match uu____1718 with univs1, t ->
                  let signature1 =
                    let uu____1784 =
                      let uu____1789 =
                        let uu____1790 = FStar_Syntax_Subst.compress t in
                        uu____1790.FStar_Syntax_Syntax.n
                      in
                      (effect_params, uu____1789)
                    in
                    match uu____1784 with
                    | [], uu____1793 -> t
                    | uu____1804, FStar_Syntax_Syntax.Tm_arrow (uu____1805, c) ->
                        FStar_Syntax_Util.comp_result c
                    | uu____1823 -> failwith "Impossible : t is an arrow"
                  in
                  let close1 n1 ts =
                    let ts1 =
                      let uu____1836 =
                        FStar_Syntax_Subst.close_tscheme effect_params ts
                      in
                      FStar_Syntax_Subst.close_univ_vars_tscheme univs1
                        uu____1836
                    in
                    let m =
                      FStar_List.length (FStar_Pervasives_Native.fst ts1)
                    in
                    (let uu____1841 =
                       ( n1 >= Prims.parse_int "0"
                       &&
                       let uu____1843 =
                         FStar_Syntax_Util.is_unknown
                           (FStar_Pervasives_Native.snd ts1)
                       in
                       Prims.op_Negation uu____1843 )
                       && m <> n1
                     in
                     if uu____1841 then
                       let error =
                         if m < n1 then "not universe-polymorphic enough"
                         else "too universe-polymorphic"
                       in
                       let err_msg =
                         let uu____1859 = FStar_Util.string_of_int m in
                         let uu____1866 = FStar_Util.string_of_int n1 in
                         let uu____1867 =
                           FStar_Syntax_Print.tscheme_to_string ts1
                         in
                         FStar_Util.format4
                           "The effect combinator is %s (m,n=%s,%s) (%s)" error
                           uu____1859 uu____1866 uu____1867
                       in
                       FStar_Errors.raise_error
                         ( FStar_Errors.Fatal_MismatchUniversePolymorphic
                         , err_msg )
                         (FStar_Pervasives_Native.snd ts1)
                           .FStar_Syntax_Syntax.pos
                     else ()) ;
                    ts1
                  in
                  let close_action act =
                    let uu____1875 =
                      close1
                        (-Prims.parse_int "1")
                        ( act.FStar_Syntax_Syntax.action_univs
                        , act.FStar_Syntax_Syntax.action_defn )
                    in
                    match uu____1875 with univs2, defn ->
                      let uu____1882 =
                        close1
                          (-Prims.parse_int "1")
                          ( act.FStar_Syntax_Syntax.action_univs
                          , act.FStar_Syntax_Syntax.action_typ )
                      in
                      match uu____1882 with univs', typ ->
                        let uu___69_1892 = act in
                        { FStar_Syntax_Syntax.action_name=
                            uu___69_1892.FStar_Syntax_Syntax.action_name
                        ; FStar_Syntax_Syntax.action_unqualified_name=
                            uu___69_1892
                              .FStar_Syntax_Syntax.action_unqualified_name
                        ; FStar_Syntax_Syntax.action_univs= univs2
                        ; FStar_Syntax_Syntax.action_params=
                            uu___69_1892.FStar_Syntax_Syntax.action_params
                        ; FStar_Syntax_Syntax.action_defn= defn
                        ; FStar_Syntax_Syntax.action_typ= typ }
                  in
                  let ed3 =
                    let uu___70_1897 = ed2 in
                    let uu____1898 = close1 (Prims.parse_int "0") return_wp in
                    let uu____1899 = close1 (Prims.parse_int "1") bind_wp in
                    let uu____1900 =
                      close1 (Prims.parse_int "0") if_then_else1
                    in
                    let uu____1901 = close1 (Prims.parse_int "0") ite_wp in
                    let uu____1902 = close1 (Prims.parse_int "0") stronger in
                    let uu____1903 = close1 (Prims.parse_int "1") close_wp in
                    let uu____1904 = close1 (Prims.parse_int "0") assert_p in
                    let uu____1905 = close1 (Prims.parse_int "0") assume_p in
                    let uu____1906 = close1 (Prims.parse_int "0") null_wp in
                    let uu____1907 = close1 (Prims.parse_int "0") trivial_wp in
                    let uu____1908 =
                      let uu____1909 =
                        close1 (Prims.parse_int "0") ([], repr)
                      in
                      FStar_Pervasives_Native.snd uu____1909
                    in
                    let uu____1920 =
                      close1 (Prims.parse_int "0") return_repr
                    in
                    let uu____1921 = close1 (Prims.parse_int "1") bind_repr in
                    let uu____1922 = FStar_List.map close_action actions in
                    { FStar_Syntax_Syntax.cattributes=
                        uu___70_1897.FStar_Syntax_Syntax.cattributes
                    ; FStar_Syntax_Syntax.mname=
                        uu___70_1897.FStar_Syntax_Syntax.mname
                    ; FStar_Syntax_Syntax.univs= univs1
                    ; FStar_Syntax_Syntax.binders= effect_params
                    ; FStar_Syntax_Syntax.signature= signature1
                    ; FStar_Syntax_Syntax.ret_wp= uu____1898
                    ; FStar_Syntax_Syntax.bind_wp= uu____1899
                    ; FStar_Syntax_Syntax.if_then_else= uu____1900
                    ; FStar_Syntax_Syntax.ite_wp= uu____1901
                    ; FStar_Syntax_Syntax.stronger= uu____1902
                    ; FStar_Syntax_Syntax.close_wp= uu____1903
                    ; FStar_Syntax_Syntax.assert_p= uu____1904
                    ; FStar_Syntax_Syntax.assume_p= uu____1905
                    ; FStar_Syntax_Syntax.null_wp= uu____1906
                    ; FStar_Syntax_Syntax.trivial= uu____1907
                    ; FStar_Syntax_Syntax.repr= uu____1908
                    ; FStar_Syntax_Syntax.return_repr= uu____1920
                    ; FStar_Syntax_Syntax.bind_repr= uu____1921
                    ; FStar_Syntax_Syntax.actions= uu____1922 }
                  in
                  (let uu____1926 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low
                     || FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "ED")
                   in
                   if uu____1926 then
                     let uu____1927 =
                       FStar_Syntax_Print.eff_decl_to_string false ed3
                     in
                     FStar_Util.print_string uu____1927
                   else ()) ;
                  ed3


let cps_and_elaborate
    : FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.eff_decl
      -> ( FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_Syntax_Syntax.eff_decl
         , FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option )
         FStar_Pervasives_Native.tuple3 =
  fun env ed ->
    let uu____1945 =
      FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
        ed.FStar_Syntax_Syntax.signature
    in
    match uu____1945 with effect_binders_un, signature_un ->
      let uu____1962 =
        FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un
      in
      match uu____1962 with effect_binders, env1, uu____1981 ->
        let uu____1982 =
          FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
        in
        match uu____1982 with signature, uu____1998 ->
          let raise_error1 a uu____2009 =
            match uu____2009 with e, err_msg ->
              FStar_Errors.raise_error (e, err_msg)
                signature.FStar_Syntax_Syntax.pos
          in
          let effect_binders1 =
            FStar_List.map
              (fun uu____2035 ->
                match uu____2035 with bv, qual ->
                  let uu____2046 =
                    let uu___71_2047 = bv in
                    let uu____2048 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.EraseUniverses] env1
                        bv.FStar_Syntax_Syntax.sort
                    in
                    { FStar_Syntax_Syntax.ppname=
                        uu___71_2047.FStar_Syntax_Syntax.ppname
                    ; FStar_Syntax_Syntax.index=
                        uu___71_2047.FStar_Syntax_Syntax.index
                    ; FStar_Syntax_Syntax.sort= uu____2048 }
                  in
                  (uu____2046, qual) )
              effect_binders
          in
          let uu____2051 =
            let uu____2058 =
              let uu____2059 = FStar_Syntax_Subst.compress signature_un in
              uu____2059.FStar_Syntax_Syntax.n
            in
            Obj.magic
              ( match uu____2058 with
              | FStar_Syntax_Syntax.Tm_arrow ([(a, uu____2069)], effect_marker) ->
                  Obj.repr (a, effect_marker)
              | uu____2091 ->
                  Obj.repr
                    (raise_error1 ()
                       ( FStar_Errors.Fatal_BadSignatureShape
                       , "bad shape for effect-for-free signature" )) )
          in
          match uu____2051 with a, effect_marker ->
            let a1 =
              let uu____2109 = FStar_Syntax_Syntax.is_null_bv a in
              if uu____2109 then
                let uu____2110 =
                  let uu____2113 = FStar_Syntax_Syntax.range_of_bv a in
                  FStar_Pervasives_Native.Some uu____2113
                in
                FStar_Syntax_Syntax.gen_bv "a" uu____2110
                  a.FStar_Syntax_Syntax.sort
              else a
            in
            let open_and_check env2 other_binders t =
              let subst1 =
                FStar_Syntax_Subst.opening_of_binders
                  (FStar_List.append effect_binders1 other_binders)
              in
              let t1 = FStar_Syntax_Subst.subst subst1 t in
              let uu____2147 = FStar_TypeChecker_TcTerm.tc_term env2 t1 in
              match uu____2147 with t2, comp, uu____2160 -> (t2, comp)
            in
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                signature.FStar_Syntax_Syntax.pos
            in
            let uu____2167 =
              open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
            in
            match uu____2167 with repr, _comp ->
              (let uu____2189 =
                 FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED")
               in
               if uu____2189 then
                 let uu____2190 = FStar_Syntax_Print.term_to_string repr in
                 FStar_Util.print1 "Representation is: %s\n" uu____2190
               else ()) ;
              let dmff_env =
                FStar_TypeChecker_DMFF.empty env1
                  (FStar_TypeChecker_TcTerm.tc_constant env1
                     FStar_Range.dummyRange)
              in
              let wp_type = FStar_TypeChecker_DMFF.star_type dmff_env repr in
              let wp_type1 = recheck_debug "*" env1 wp_type in
              let wp_a =
                let uu____2196 =
                  let uu____2197 =
                    let uu____2198 =
                      let uu____2213 =
                        let uu____2220 =
                          let uu____2225 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2226 =
                            FStar_Syntax_Syntax.as_implicit false
                          in
                          (uu____2225, uu____2226)
                        in
                        [uu____2220]
                      in
                      (wp_type1, uu____2213)
                    in
                    FStar_Syntax_Syntax.Tm_app uu____2198
                  in
                  mk1 uu____2197
                in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.Beta] env1 uu____2196
              in
              let effect_signature =
                let binders =
                  let uu____2251 =
                    let uu____2256 = FStar_Syntax_Syntax.as_implicit false in
                    (a1, uu____2256)
                  in
                  let uu____2257 =
                    let uu____2264 =
                      let uu____2265 =
                        FStar_Syntax_Syntax.gen_bv "dijkstra_wp"
                          FStar_Pervasives_Native.None wp_a
                      in
                      FStar_All.pipe_right uu____2265
                        FStar_Syntax_Syntax.mk_binder
                    in
                    [uu____2264]
                  in
                  uu____2251 :: uu____2257
                in
                let binders1 = FStar_Syntax_Subst.close_binders binders in
                mk1 (FStar_Syntax_Syntax.Tm_arrow (binders1, effect_marker))
              in
              let effect_signature1 =
                recheck_debug "turned into the effect signature" env1
                  effect_signature
              in
              let sigelts = FStar_Util.mk_ref [] in
              let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
              let elaborate_and_star dmff_env1 other_binders item =
                let env2 = FStar_TypeChecker_DMFF.get_env dmff_env1 in
                let uu____2328 = item in
                match uu____2328 with u_item, item1 ->
                  let uu____2349 = open_and_check env2 other_binders item1 in
                  match uu____2349 with item2, item_comp ->
                    (let uu____2365 =
                       let uu____2366 =
                         FStar_Syntax_Util.is_total_lcomp item_comp
                       in
                       Prims.op_Negation uu____2366
                     in
                     if uu____2365 then
                       let uu____2367 =
                         let uu____2372 =
                           let uu____2373 =
                             FStar_Syntax_Print.term_to_string item2
                           in
                           let uu____2374 =
                             FStar_Syntax_Print.lcomp_to_string item_comp
                           in
                           FStar_Util.format2
                             "Computation for [%s] is not total : %s !"
                             uu____2373 uu____2374
                         in
                         (FStar_Errors.Fatal_ComputationNotTotal, uu____2372)
                       in
                       FStar_Errors.raise_err uu____2367
                     else ()) ;
                    let uu____2376 =
                      FStar_TypeChecker_DMFF.star_expr dmff_env1 item2
                    in
                    match uu____2376 with item_t, item_wp, item_elab ->
                      let item_wp1 = recheck_debug "*" env2 item_wp in
                      let item_elab1 = recheck_debug "_" env2 item_elab in
                      (dmff_env1, item_t, item_wp1, item_elab1)
              in
              let uu____2396 =
                elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr
              in
              match uu____2396
              with dmff_env1, uu____2420, bind_wp, bind_elab ->
                let uu____2423 =
                  elaborate_and_star dmff_env1 []
                    ed.FStar_Syntax_Syntax.return_repr
                in
                match uu____2423
                with dmff_env2, uu____2447, return_wp, return_elab ->
                  let rc_gtot =
                    { FStar_Syntax_Syntax.residual_effect=
                        FStar_Parser_Const.effect_GTot_lid
                    ; FStar_Syntax_Syntax.residual_typ=
                        FStar_Pervasives_Native.None
                    ; FStar_Syntax_Syntax.residual_flags= [] }
                  in
                  let lift_from_pure_wp =
                    let uu____2454 =
                      let uu____2455 = FStar_Syntax_Subst.compress return_wp in
                      uu____2455.FStar_Syntax_Syntax.n
                    in
                    Obj.magic
                      ( match uu____2454 with
                      | FStar_Syntax_Syntax.Tm_abs (b1 :: b2 :: bs, body, what) ->
                          Obj.repr
                            (let uu____2499 =
                               let uu____2514 =
                                 let uu____2519 =
                                   FStar_Syntax_Util.abs bs body
                                     FStar_Pervasives_Native.None
                                 in
                                 FStar_Syntax_Subst.open_term [b1; b2]
                                   uu____2519
                               in
                               match uu____2514 with
                               | [b11; b21], body1 -> (b11, b21, body1)
                               | uu____2583 ->
                                   failwith
                                     "Impossible : open_term not preserving binders arity"
                             in
                             match uu____2499 with b11, b21, body1 ->
                               let env0 =
                                 let uu____2622 =
                                   FStar_TypeChecker_DMFF.get_env dmff_env2
                                 in
                                 FStar_TypeChecker_Env.push_binders uu____2622
                                   [b11; b21]
                               in
                               let wp_b1 =
                                 let raw_wp_b1 =
                                   let uu____2639 =
                                     let uu____2640 =
                                       let uu____2655 =
                                         let uu____2662 =
                                           let uu____2667 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               (FStar_Pervasives_Native.fst b11)
                                           in
                                           let uu____2668 =
                                             FStar_Syntax_Syntax.as_implicit
                                               false
                                           in
                                           (uu____2667, uu____2668)
                                         in
                                         [uu____2662]
                                       in
                                       (wp_type1, uu____2655)
                                     in
                                     FStar_Syntax_Syntax.Tm_app uu____2640
                                   in
                                   mk1 uu____2639
                                 in
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env0
                                   raw_wp_b1
                               in
                               let uu____2683 =
                                 let uu____2692 =
                                   let uu____2693 =
                                     FStar_Syntax_Util.unascribe wp_b1
                                   in
                                   FStar_TypeChecker_Normalize.
                                   eta_expand_with_type env0 body1 uu____2693
                                 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.abs_formals uu____2692
                               in
                               match uu____2683 with bs1, body2, what' ->
                                 let fail a415 =
                                   (Obj.magic (fun uu____2712 ->
                                        let error_msg =
                                          let uu____2714 =
                                            FStar_Syntax_Print.term_to_string
                                              body2
                                          in
                                          FStar_Util.format2
                                            "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                            uu____2714
                                            ( match what' with
                                            | FStar_Pervasives_Native.None ->
                                                "None"
                                            | FStar_Pervasives_Native.Some rc ->
                                                FStar_Ident.text_of_lid
                                                  rc
                                                    .FStar_Syntax_Syntax.
                                                     residual_effect )
                                        in
                                        raise_error1 ()
                                          ( FStar_Errors.
                                            Fatal_WrongBodyTypeForReturnWP
                                          , error_msg ) ))
                                     a415
                                 in
                                 ( match what' with
                                 | FStar_Pervasives_Native.None -> fail ()
                                 | FStar_Pervasives_Native.Some rc ->
                                     if Prims.op_Negation
                                          (FStar_Syntax_Util.is_pure_effect
                                             rc
                                               .FStar_Syntax_Syntax.
                                                residual_effect)
                                     then fail ()
                                     else () ;
                                     let uu____2720 =
                                       FStar_Util.map_opt
                                         rc.FStar_Syntax_Syntax.residual_typ
                                         (fun rt ->
                                           let g_opt =
                                             FStar_TypeChecker_Rel.try_teq true
                                               env1 rt FStar_Syntax_Util.ktype0
                                           in
                                           match g_opt with
                                           | FStar_Pervasives_Native.Some g' ->
                                               FStar_TypeChecker_Rel.
                                               force_trivial_guard env1 g'
                                           | FStar_Pervasives_Native.None ->
                                               fail () )
                                     in
                                     FStar_All.pipe_right uu____2720
                                       FStar_Pervasives.ignore ) ;
                                 let wp =
                                   let t2 =
                                     (FStar_Pervasives_Native.fst b21)
                                       .FStar_Syntax_Syntax.sort
                                   in
                                   let pure_wp_type =
                                     FStar_TypeChecker_DMFF.double_star t2
                                   in
                                   FStar_Syntax_Syntax.gen_bv "wp"
                                     FStar_Pervasives_Native.None pure_wp_type
                                 in
                                 let body3 =
                                   let uu____2747 =
                                     let uu____2748 =
                                       FStar_Syntax_Syntax.bv_to_name wp
                                     in
                                     let uu____2749 =
                                       let uu____2750 =
                                         let uu____2757 =
                                           FStar_Syntax_Util.abs [b21] body2
                                             what'
                                         in
                                         ( uu____2757
                                         , FStar_Pervasives_Native.None )
                                       in
                                       [uu____2750]
                                     in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____2748
                                       uu____2749
                                   in
                                   uu____2747 FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                 in
                                 let uu____2782 =
                                   let uu____2783 =
                                     let uu____2790 =
                                       FStar_Syntax_Syntax.mk_binder wp
                                     in
                                     [uu____2790]
                                   in
                                   b11 :: uu____2783
                                 in
                                 let uu____2795 =
                                   FStar_Syntax_Util.abs bs1 body3 what
                                 in
                                 FStar_Syntax_Util.abs uu____2782 uu____2795
                                   (FStar_Pervasives_Native.Some rc_gtot))
                      | uu____2796 ->
                          Obj.repr
                            (raise_error1 ()
                               ( FStar_Errors.Fatal_UnexpectedReturnShape
                               , "unexpected shape for return" )) )
                  in
                  let return_wp1 =
                    let uu____2798 =
                      let uu____2799 = FStar_Syntax_Subst.compress return_wp in
                      uu____2799.FStar_Syntax_Syntax.n
                    in
                    Obj.magic
                      ( match uu____2798 with
                      | FStar_Syntax_Syntax.Tm_abs (b1 :: b2 :: bs, body, what) ->
                          Obj.repr
                            (let uu____2843 =
                               FStar_Syntax_Util.abs bs body what
                             in
                             FStar_Syntax_Util.abs [b1; b2] uu____2843
                               (FStar_Pervasives_Native.Some rc_gtot))
                      | uu____2856 ->
                          Obj.repr
                            (raise_error1 ()
                               ( FStar_Errors.Fatal_UnexpectedReturnShape
                               , "unexpected shape for return" )) )
                  in
                  let bind_wp1 =
                    let uu____2858 =
                      let uu____2859 = FStar_Syntax_Subst.compress bind_wp in
                      uu____2859.FStar_Syntax_Syntax.n
                    in
                    Obj.magic
                      ( match uu____2858 with
                      | FStar_Syntax_Syntax.Tm_abs (binders, body, what) ->
                          Obj.repr
                            (let r =
                               FStar_Syntax_Syntax.lid_as_fv
                                 FStar_Parser_Const.range_lid
                                 (FStar_Syntax_Syntax.Delta_defined_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                             in
                             let uu____2886 =
                               let uu____2887 =
                                 let uu____2890 =
                                   let uu____2891 =
                                     mk1 (FStar_Syntax_Syntax.Tm_fvar r)
                                   in
                                   FStar_Syntax_Syntax.null_binder uu____2891
                                 in
                                 [uu____2890]
                               in
                               FStar_List.append uu____2887 binders
                             in
                             FStar_Syntax_Util.abs uu____2886 body what)
                      | uu____2892 ->
                          Obj.repr
                            (raise_error1 ()
                               ( FStar_Errors.Fatal_UnexpectedBindShape
                               , "unexpected shape for bind" )) )
                  in
                  let apply_close t =
                    if FStar_List.length effect_binders1 = Prims.parse_int "0"
                    then t
                    else
                      let uu____2910 =
                        let uu____2911 =
                          let uu____2912 =
                            let uu____2927 =
                              let uu____2928 =
                                FStar_Syntax_Util.args_of_binders
                                  effect_binders1
                              in
                              FStar_Pervasives_Native.snd uu____2928
                            in
                            (t, uu____2927)
                          in
                          FStar_Syntax_Syntax.Tm_app uu____2912
                        in
                        mk1 uu____2911
                      in
                      FStar_Syntax_Subst.close effect_binders1 uu____2910
                  in
                  let rec apply_last1 f l =
                    match l with
                    | [] -> failwith "empty path.."
                    | [a2] ->
                        let uu____2958 = f a2 in
                        [uu____2958]
                    | x :: xs ->
                        let uu____2963 = apply_last1 f xs in
                        x :: uu____2963
                  in
                  let register name item =
                    let p =
                      FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname
                    in
                    let p' =
                      apply_last1
                        (fun s ->
                          Prims.strcat "__"
                            (Prims.strcat s
                               (Prims.strcat "_eff_override_" name)) )
                        p
                    in
                    let l' =
                      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
                    in
                    let uu____2983 =
                      FStar_TypeChecker_Env.try_lookup_lid env1 l'
                    in
                    match uu____2983 with
                    | FStar_Pervasives_Native.Some (_us, _t) ->
                        (let uu____3013 = FStar_Options.debug_any () in
                         if uu____3013 then
                           let uu____3014 = FStar_Ident.string_of_lid l' in
                           FStar_Util.print1 "DM4F: Applying override %s\n"
                             uu____3014
                         else ()) ;
                        let uu____3016 =
                          FStar_Syntax_Syntax.lid_as_fv l'
                            FStar_Syntax_Syntax.Delta_equational
                            FStar_Pervasives_Native.None
                        in
                        FStar_Syntax_Syntax.fv_to_tm uu____3016
                    | FStar_Pervasives_Native.None ->
                        let uu____3025 =
                          let uu____3030 = mk_lid name in
                          let uu____3031 =
                            FStar_Syntax_Util.abs effect_binders1 item
                              FStar_Pervasives_Native.None
                          in
                          FStar_TypeChecker_Util.mk_toplevel_definition env1
                            uu____3030 uu____3031
                        in
                        match uu____3025 with sigelt, fv ->
                          (let uu____3035 =
                             let uu____3038 = FStar_ST.op_Bang sigelts in
                             sigelt :: uu____3038
                           in
                           FStar_ST.op_Colon_Equals sigelts uu____3035) ;
                          fv
                  in
                  let lift_from_pure_wp1 =
                    register "lift_from_pure" lift_from_pure_wp
                  in
                  let return_wp2 = register "return_wp" return_wp1 in
                  FStar_Options.push () ;
                  (let uu____3135 =
                     let uu____3138 =
                       FStar_Syntax_Syntax.mk_sigelt
                         (FStar_Syntax_Syntax.Sig_pragma
                            (FStar_Syntax_Syntax.SetOptions
                               "--admit_smt_queries true"))
                     in
                     let uu____3139 = FStar_ST.op_Bang sigelts in
                     uu____3138 :: uu____3139
                   in
                   FStar_ST.op_Colon_Equals sigelts uu____3135) ;
                  let return_elab1 = register "return_elab" return_elab in
                  FStar_Options.pop () ;
                  let bind_wp2 = register "bind_wp" bind_wp1 in
                  FStar_Options.push () ;
                  (let uu____3237 =
                     let uu____3240 =
                       FStar_Syntax_Syntax.mk_sigelt
                         (FStar_Syntax_Syntax.Sig_pragma
                            (FStar_Syntax_Syntax.SetOptions
                               "--admit_smt_queries true"))
                     in
                     let uu____3241 = FStar_ST.op_Bang sigelts in
                     uu____3240 :: uu____3241
                   in
                   FStar_ST.op_Colon_Equals sigelts uu____3237) ;
                  let bind_elab1 = register "bind_elab" bind_elab in
                  FStar_Options.pop () ;
                  let uu____3336 =
                    FStar_List.fold_left
                      (fun uu____3376 action ->
                        match uu____3376 with dmff_env3, actions ->
                          let params_un =
                            FStar_Syntax_Subst.open_binders
                              action.FStar_Syntax_Syntax.action_params
                          in
                          let uu____3397 =
                            let uu____3404 =
                              FStar_TypeChecker_DMFF.get_env dmff_env3
                            in
                            FStar_TypeChecker_TcTerm.tc_tparams uu____3404
                              params_un
                          in
                          match uu____3397
                          with action_params, env', uu____3413 ->
                            let action_params1 =
                              FStar_List.map
                                (fun uu____3433 ->
                                  match uu____3433 with bv, qual ->
                                    let uu____3444 =
                                      let uu___72_3445 = bv in
                                      let uu____3446 =
                                        FStar_TypeChecker_Normalize.normalize
                                          [ FStar_TypeChecker_Normalize.
                                            EraseUniverses ] env'
                                          bv.FStar_Syntax_Syntax.sort
                                      in
                                      { FStar_Syntax_Syntax.ppname=
                                          uu___72_3445
                                            .FStar_Syntax_Syntax.ppname
                                      ; FStar_Syntax_Syntax.index=
                                          uu___72_3445
                                            .FStar_Syntax_Syntax.index
                                      ; FStar_Syntax_Syntax.sort= uu____3446 }
                                    in
                                    (uu____3444, qual) )
                                action_params
                            in
                            let dmff_env' =
                              FStar_TypeChecker_DMFF.set_env dmff_env3 env'
                            in
                            let uu____3450 =
                              elaborate_and_star dmff_env' action_params1
                                ( action.FStar_Syntax_Syntax.action_univs
                                , action.FStar_Syntax_Syntax.action_defn )
                            in
                            match uu____3450
                            with
                            | dmff_env4, action_t, action_wp, action_elab
                            ->
                              let name =
                                action.FStar_Syntax_Syntax.action_name
                                  .FStar_Ident.ident
                                  .FStar_Ident.idText
                              in
                              let action_typ_with_wp =
                                FStar_TypeChecker_DMFF.trans_F dmff_env'
                                  action_t action_wp
                              in
                              let action_params2 =
                                FStar_Syntax_Subst.close_binders action_params1
                              in
                              let action_elab1 =
                                FStar_Syntax_Subst.close action_params2
                                  action_elab
                              in
                              let action_typ_with_wp1 =
                                FStar_Syntax_Subst.close action_params2
                                  action_typ_with_wp
                              in
                              let action_elab2 =
                                FStar_Syntax_Util.abs action_params2
                                  action_elab1 FStar_Pervasives_Native.None
                              in
                              let action_typ_with_wp2 =
                                match action_params2 with
                                | [] -> action_typ_with_wp1
                                | uu____3480 ->
                                    let uu____3481 =
                                      FStar_Syntax_Syntax.mk_Total
                                        action_typ_with_wp1
                                    in
                                    FStar_Syntax_Util.flat_arrow action_params2
                                      uu____3481
                              in
                              (let uu____3485 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "ED")
                               in
                               if uu____3485 then
                                 let uu____3486 =
                                   FStar_Syntax_Print.binders_to_string ","
                                     params_un
                                 in
                                 let uu____3487 =
                                   FStar_Syntax_Print.binders_to_string ","
                                     action_params2
                                 in
                                 let uu____3488 =
                                   FStar_Syntax_Print.term_to_string
                                     action_typ_with_wp2
                                 in
                                 let uu____3489 =
                                   FStar_Syntax_Print.term_to_string
                                     action_elab2
                                 in
                                 FStar_Util.print4
                                   "original action_params %s, end action_params %s, type %s, term %s\n"
                                   uu____3486 uu____3487 uu____3488 uu____3489
                               else ()) ;
                              let action_elab3 =
                                register
                                  (Prims.strcat name "_elab")
                                  action_elab2
                              in
                              let action_typ_with_wp3 =
                                register
                                  (Prims.strcat name "_complete_type")
                                  action_typ_with_wp2
                              in
                              let uu____3493 =
                                let uu____3496 =
                                  let uu___73_3497 = action in
                                  let uu____3498 = apply_close action_elab3 in
                                  let uu____3499 =
                                    apply_close action_typ_with_wp3
                                  in
                                  { FStar_Syntax_Syntax.action_name=
                                      uu___73_3497
                                        .FStar_Syntax_Syntax.action_name
                                  ; FStar_Syntax_Syntax.action_unqualified_name=
                                      uu___73_3497
                                        .FStar_Syntax_Syntax.
                                         action_unqualified_name
                                  ; FStar_Syntax_Syntax.action_univs=
                                      uu___73_3497
                                        .FStar_Syntax_Syntax.action_univs
                                  ; FStar_Syntax_Syntax.action_params= []
                                  ; FStar_Syntax_Syntax.action_defn= uu____3498
                                  ; FStar_Syntax_Syntax.action_typ= uu____3499
                                  }
                                in
                                uu____3496 :: actions
                              in
                              (dmff_env4, uu____3493) )
                      (dmff_env2, []) ed.FStar_Syntax_Syntax.actions
                  in
                  match uu____3336 with dmff_env3, actions ->
                    let actions1 = FStar_List.rev actions in
                    let repr1 =
                      let wp =
                        FStar_Syntax_Syntax.gen_bv "wp_a"
                          FStar_Pervasives_Native.None wp_a
                      in
                      let binders =
                        let uu____3532 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____3533 =
                          let uu____3536 = FStar_Syntax_Syntax.mk_binder wp in
                          [uu____3536]
                        in
                        uu____3532 :: uu____3533
                      in
                      let uu____3537 =
                        let uu____3538 =
                          let uu____3539 =
                            let uu____3540 =
                              let uu____3555 =
                                let uu____3562 =
                                  let uu____3567 =
                                    FStar_Syntax_Syntax.bv_to_name a1
                                  in
                                  let uu____3568 =
                                    FStar_Syntax_Syntax.as_implicit false
                                  in
                                  (uu____3567, uu____3568)
                                in
                                [uu____3562]
                              in
                              (repr, uu____3555)
                            in
                            FStar_Syntax_Syntax.Tm_app uu____3540
                          in
                          mk1 uu____3539
                        in
                        let uu____3583 = FStar_Syntax_Syntax.bv_to_name wp in
                        FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____3538
                          uu____3583
                      in
                      FStar_Syntax_Util.abs binders uu____3537
                        FStar_Pervasives_Native.None
                    in
                    let repr2 = recheck_debug "FC" env1 repr1 in
                    let repr3 = register "repr" repr2 in
                    let uu____3586 =
                      let uu____3593 =
                        let uu____3594 =
                          let uu____3597 =
                            FStar_Syntax_Subst.compress wp_type1
                          in
                          FStar_All.pipe_left FStar_Syntax_Util.unascribe
                            uu____3597
                        in
                        uu____3594.FStar_Syntax_Syntax.n
                      in
                      Obj.magic
                        ( match uu____3593 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (type_param :: effect_param, arrow1, uu____3607) ->
                            Obj.repr
                              (let uu____3636 =
                                 let uu____3653 =
                                   FStar_Syntax_Subst.open_term
                                     (type_param :: effect_param) arrow1
                                 in
                                 match uu____3653 with
                                 | b :: bs, body -> (b, bs, body)
                                 | uu____3711 ->
                                     failwith
                                       "Impossible : open_term nt preserving binders arity"
                               in
                               match uu____3636
                               with type_param1, effect_param1, arrow2 ->
                                 let uu____3761 =
                                   let uu____3762 =
                                     let uu____3765 =
                                       FStar_Syntax_Subst.compress arrow2
                                     in
                                     FStar_All.pipe_left
                                       FStar_Syntax_Util.unascribe uu____3765
                                   in
                                   uu____3762.FStar_Syntax_Syntax.n
                                 in
                                 Obj.magic
                                   ( match uu____3761 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (wp_binders, c) ->
                                       Obj.repr
                                         (let uu____3790 =
                                            FStar_Syntax_Subst.open_comp
                                              wp_binders c
                                          in
                                          match uu____3790
                                          with wp_binders1, c1 ->
                                            let uu____3803 =
                                              FStar_List.partition
                                                (fun uu____3828 ->
                                                  match uu____3828
                                                  with bv, uu____3834 ->
                                                    let uu____3835 =
                                                      let uu____3836 =
                                                        FStar_Syntax_Free.names
                                                          bv
                                                            .FStar_Syntax_Syntax.
                                                             sort
                                                      in
                                                      FStar_All.pipe_right
                                                        uu____3836
                                                        (FStar_Util.set_mem
                                                           (FStar_Pervasives_Native.
                                                            fst type_param1))
                                                    in
                                                    FStar_All.pipe_right
                                                      uu____3835
                                                      Prims.op_Negation )
                                                wp_binders1
                                            in
                                            match uu____3803
                                            with pre_args, post_args ->
                                              let post =
                                                match post_args with
                                                | [post] -> post
                                                | [] ->
                                                    let err_msg =
                                                      let uu____3900 =
                                                        FStar_Syntax_Print.
                                                        term_to_string arrow2
                                                      in
                                                      FStar_Util.format1
                                                        "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                        uu____3900
                                                    in
                                                    FStar_Errors.raise_err
                                                      ( FStar_Errors.
                                                        Fatal_ImpossibleToGenerateDMEffect
                                                      , err_msg )
                                                | uu____3905 ->
                                                    let err_msg =
                                                      let uu____3913 =
                                                        FStar_Syntax_Print.
                                                        term_to_string arrow2
                                                      in
                                                      FStar_Util.format1
                                                        "Impossible to generate DM effect: multiple post candidates %s"
                                                        uu____3913
                                                    in
                                                    FStar_Errors.raise_err
                                                      ( FStar_Errors.
                                                        Fatal_ImpossibleToGenerateDMEffect
                                                      , err_msg )
                                              in
                                              let uu____3918 =
                                                FStar_Syntax_Util.arrow
                                                  pre_args c1
                                              in
                                              let uu____3921 =
                                                FStar_Syntax_Util.abs
                                                  (type_param1 :: effect_param1)
                                                  (FStar_Pervasives_Native.fst
                                                     post)
                                                    .FStar_Syntax_Syntax.sort
                                                  FStar_Pervasives_Native.None
                                              in
                                              (uu____3918, uu____3921))
                                   | uu____3928 ->
                                       Obj.repr
                                         (let uu____3929 =
                                            let uu____3934 =
                                              let uu____3935 =
                                                FStar_Syntax_Print.
                                                term_to_string arrow2
                                              in
                                              FStar_Util.format1
                                                "Impossible: pre/post arrow %s"
                                                uu____3935
                                            in
                                            ( FStar_Errors.
                                              Fatal_ImpossiblePrePostArrow
                                            , uu____3934 )
                                          in
                                          raise_error1 () uu____3929) ))
                        | uu____3936 ->
                            Obj.repr
                              (let uu____3937 =
                                 let uu____3942 =
                                   let uu____3943 =
                                     FStar_Syntax_Print.term_to_string wp_type1
                                   in
                                   FStar_Util.format1
                                     "Impossible: pre/post abs %s" uu____3943
                                 in
                                 ( FStar_Errors.Fatal_ImpossiblePrePostAbs
                                 , uu____3942 )
                               in
                               raise_error1 () uu____3937) )
                    in
                    match uu____3586 with pre, post ->
                      (let uu____3961 = register "pre" pre in
                       ()) ;
                      (let uu____3963 = register "post" post in
                       ()) ;
                      (let uu____3965 = register "wp" wp_type1 in
                       ()) ;
                      let ed1 =
                        let uu___74_3967 = ed in
                        let uu____3968 =
                          FStar_Syntax_Subst.close_binders effect_binders1
                        in
                        let uu____3969 =
                          FStar_Syntax_Subst.close effect_binders1
                            effect_signature1
                        in
                        let uu____3970 =
                          let uu____3971 = apply_close return_wp2 in
                          ([], uu____3971)
                        in
                        let uu____3978 =
                          let uu____3979 = apply_close bind_wp2 in
                          ([], uu____3979)
                        in
                        let uu____3986 = apply_close repr3 in
                        let uu____3987 =
                          let uu____3988 = apply_close return_elab1 in
                          ([], uu____3988)
                        in
                        let uu____3995 =
                          let uu____3996 = apply_close bind_elab1 in
                          ([], uu____3996)
                        in
                        { FStar_Syntax_Syntax.cattributes=
                            uu___74_3967.FStar_Syntax_Syntax.cattributes
                        ; FStar_Syntax_Syntax.mname=
                            uu___74_3967.FStar_Syntax_Syntax.mname
                        ; FStar_Syntax_Syntax.univs=
                            uu___74_3967.FStar_Syntax_Syntax.univs
                        ; FStar_Syntax_Syntax.binders= uu____3968
                        ; FStar_Syntax_Syntax.signature= uu____3969
                        ; FStar_Syntax_Syntax.ret_wp= uu____3970
                        ; FStar_Syntax_Syntax.bind_wp= uu____3978
                        ; FStar_Syntax_Syntax.if_then_else=
                            uu___74_3967.FStar_Syntax_Syntax.if_then_else
                        ; FStar_Syntax_Syntax.ite_wp=
                            uu___74_3967.FStar_Syntax_Syntax.ite_wp
                        ; FStar_Syntax_Syntax.stronger=
                            uu___74_3967.FStar_Syntax_Syntax.stronger
                        ; FStar_Syntax_Syntax.close_wp=
                            uu___74_3967.FStar_Syntax_Syntax.close_wp
                        ; FStar_Syntax_Syntax.assert_p=
                            uu___74_3967.FStar_Syntax_Syntax.assert_p
                        ; FStar_Syntax_Syntax.assume_p=
                            uu___74_3967.FStar_Syntax_Syntax.assume_p
                        ; FStar_Syntax_Syntax.null_wp=
                            uu___74_3967.FStar_Syntax_Syntax.null_wp
                        ; FStar_Syntax_Syntax.trivial=
                            uu___74_3967.FStar_Syntax_Syntax.trivial
                        ; FStar_Syntax_Syntax.repr= uu____3986
                        ; FStar_Syntax_Syntax.return_repr= uu____3987
                        ; FStar_Syntax_Syntax.bind_repr= uu____3995
                        ; FStar_Syntax_Syntax.actions= actions1 }
                      in
                      let uu____4003 =
                        FStar_TypeChecker_DMFF.gen_wps_for_free env1
                          effect_binders1 a1 wp_a ed1
                      in
                      match uu____4003 with sigelts', ed2 ->
                        (let uu____4021 =
                           FStar_TypeChecker_Env.debug env1
                             (FStar_Options.Other "ED")
                         in
                         if uu____4021 then
                           let uu____4022 =
                             FStar_Syntax_Print.eff_decl_to_string true ed2
                           in
                           FStar_Util.print_string uu____4022
                         else ()) ;
                        let lift_from_pure_opt =
                          if FStar_List.length effect_binders1
                             = Prims.parse_int "0"
                          then
                            let lift_from_pure =
                              let uu____4034 =
                                let uu____4037 =
                                  let uu____4046 =
                                    apply_close lift_from_pure_wp1
                                  in
                                  ([], uu____4046)
                                in
                                FStar_Pervasives_Native.Some uu____4037
                              in
                              { FStar_Syntax_Syntax.source=
                                  FStar_Parser_Const.effect_PURE_lid
                              ; FStar_Syntax_Syntax.target=
                                  ed2.FStar_Syntax_Syntax.mname
                              ; FStar_Syntax_Syntax.lift_wp= uu____4034
                              ; FStar_Syntax_Syntax.lift=
                                  FStar_Pervasives_Native.None }
                            in
                            let uu____4061 =
                              FStar_Syntax_Syntax.mk_sigelt
                                (FStar_Syntax_Syntax.Sig_sub_effect
                                   lift_from_pure)
                            in
                            FStar_Pervasives_Native.Some uu____4061
                          else FStar_Pervasives_Native.None
                        in
                        let uu____4063 =
                          let uu____4066 =
                            let uu____4069 = FStar_ST.op_Bang sigelts in
                            FStar_List.rev uu____4069
                          in
                          FStar_List.append uu____4066 sigelts'
                        in
                        (uu____4063, ed2, lift_from_pure_opt)


let tc_lex_t:
      'Auu____4126. FStar_TypeChecker_Env.env
      -> FStar_Syntax_Syntax.sigelt Prims.list -> 'Auu____4126 Prims.list
      -> FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt =
  fun env ses quals lids ->
    let err_range =
      let uu____4159 = FStar_List.hd ses in
      uu____4159.FStar_Syntax_Syntax.sigrng
    in
    ( match lids with
    | [lex_t1; lex_top1; lex_cons]
      when ( FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid
           && FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid )
           && FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid ->
        ()
    | uu____4164 ->
        FStar_Errors.raise_error
          ( FStar_Errors.Fatal_InvalidRedefinitionOfLexT
          , "Invalid (partial) redefinition of lex_t" ) err_range ) ;
    match ses with
    | [ { FStar_Syntax_Syntax.sigel=
            FStar_Syntax_Syntax.Sig_inductive_typ
              (lex_t1, [], [], t, uu____4169, uu____4170)
        ; FStar_Syntax_Syntax.sigrng= r
        ; FStar_Syntax_Syntax.sigquals= []
        ; FStar_Syntax_Syntax.sigmeta= uu____4172
        ; FStar_Syntax_Syntax.sigattrs= uu____4173; _ }
      ; { FStar_Syntax_Syntax.sigel=
            FStar_Syntax_Syntax.Sig_datacon
              (lex_top1, [], _t_top, _lex_t_top, _0_40, uu____4177)
        ; FStar_Syntax_Syntax.sigrng= r1
        ; FStar_Syntax_Syntax.sigquals= []
        ; FStar_Syntax_Syntax.sigmeta= uu____4179
        ; FStar_Syntax_Syntax.sigattrs= uu____4180; _ }
      ; { FStar_Syntax_Syntax.sigel=
            FStar_Syntax_Syntax.Sig_datacon
              (lex_cons, [], _t_cons, _lex_t_cons, _0_41, uu____4184)
        ; FStar_Syntax_Syntax.sigrng= r2
        ; FStar_Syntax_Syntax.sigquals= []
        ; FStar_Syntax_Syntax.sigmeta= uu____4186
        ; FStar_Syntax_Syntax.sigattrs= uu____4187; _ } ]
      when (_0_40 = Prims.parse_int "0" && _0_41 = Prims.parse_int "0")
           && ( FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid
              && FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid
              )
           && FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid ->
        let u =
          FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r)
        in
        let t1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
            FStar_Pervasives_Native.None r
        in
        let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
        let tc =
          { FStar_Syntax_Syntax.sigel=
              FStar_Syntax_Syntax.Sig_inductive_typ
                ( lex_t1
                , [u]
                , []
                , t2
                , []
                , [ FStar_Parser_Const.lextop_lid
                  ; FStar_Parser_Const.lexcons_lid ] )
          ; FStar_Syntax_Syntax.sigrng= r
          ; FStar_Syntax_Syntax.sigquals= []
          ; FStar_Syntax_Syntax.sigmeta= FStar_Syntax_Syntax.default_sigmeta
          ; FStar_Syntax_Syntax.sigattrs= [] }
        in
        let utop =
          FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r1)
        in
        let lex_top_t =
          let uu____4252 =
            let uu____4255 =
              let uu____4256 =
                let uu____4263 =
                  FStar_Syntax_Syntax.fvar
                    (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1)
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                in
                (uu____4263, [FStar_Syntax_Syntax.U_name utop])
              in
              FStar_Syntax_Syntax.Tm_uinst uu____4256
            in
            FStar_Syntax_Syntax.mk uu____4255
          in
          uu____4252 FStar_Pervasives_Native.None r1
        in
        let lex_top_t1 = FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
        let dc_lextop =
          { FStar_Syntax_Syntax.sigel=
              FStar_Syntax_Syntax.Sig_datacon
                ( lex_top1
                , [utop]
                , lex_top_t1
                , FStar_Parser_Const.lex_t_lid
                , Prims.parse_int "0"
                , [] )
          ; FStar_Syntax_Syntax.sigrng= r1
          ; FStar_Syntax_Syntax.sigquals= []
          ; FStar_Syntax_Syntax.sigmeta= FStar_Syntax_Syntax.default_sigmeta
          ; FStar_Syntax_Syntax.sigattrs= [] }
        in
        let ucons1 =
          FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r2)
        in
        let ucons2 =
          FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r2)
        in
        let lex_cons_t =
          let a =
            let uu____4281 =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_type
                   (FStar_Syntax_Syntax.U_name ucons1))
                FStar_Pervasives_Native.None r2
            in
            FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
              uu____4281
          in
          let hd1 =
            let uu____4283 = FStar_Syntax_Syntax.bv_to_name a in
            FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
              uu____4283
          in
          let tl1 =
            let uu____4285 =
              let uu____4286 =
                let uu____4289 =
                  let uu____4290 =
                    let uu____4297 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid
                           r2)
                        FStar_Syntax_Syntax.Delta_constant
                        FStar_Pervasives_Native.None
                    in
                    (uu____4297, [FStar_Syntax_Syntax.U_name ucons2])
                  in
                  FStar_Syntax_Syntax.Tm_uinst uu____4290
                in
                FStar_Syntax_Syntax.mk uu____4289
              in
              uu____4286 FStar_Pervasives_Native.None r2
            in
            FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
              uu____4285
          in
          let res =
            let uu____4306 =
              let uu____4309 =
                let uu____4310 =
                  let uu____4317 =
                    FStar_Syntax_Syntax.fvar
                      (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid
                         r2)
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                  in
                  ( uu____4317
                  , [ FStar_Syntax_Syntax.U_max
                        [ FStar_Syntax_Syntax.U_name ucons1
                        ; FStar_Syntax_Syntax.U_name ucons2 ] ] )
                in
                FStar_Syntax_Syntax.Tm_uinst uu____4310
              in
              FStar_Syntax_Syntax.mk uu____4309
            in
            uu____4306 FStar_Pervasives_Native.None r2
          in
          let uu____4323 = FStar_Syntax_Syntax.mk_Total res in
          FStar_Syntax_Util.arrow
            [ (a, FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)
            ; (hd1, FStar_Pervasives_Native.None)
            ; (tl1, FStar_Pervasives_Native.None) ] uu____4323
        in
        let lex_cons_t1 =
          FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2] lex_cons_t
        in
        let dc_lexcons =
          { FStar_Syntax_Syntax.sigel=
              FStar_Syntax_Syntax.Sig_datacon
                ( lex_cons
                , [ucons1; ucons2]
                , lex_cons_t1
                , FStar_Parser_Const.lex_t_lid
                , Prims.parse_int "0"
                , [] )
          ; FStar_Syntax_Syntax.sigrng= r2
          ; FStar_Syntax_Syntax.sigquals= []
          ; FStar_Syntax_Syntax.sigmeta= FStar_Syntax_Syntax.default_sigmeta
          ; FStar_Syntax_Syntax.sigattrs= [] }
        in
        let uu____4362 = FStar_TypeChecker_Env.get_range env in
        { FStar_Syntax_Syntax.sigel=
            FStar_Syntax_Syntax.Sig_bundle ([tc; dc_lextop; dc_lexcons], lids)
        ; FStar_Syntax_Syntax.sigrng= uu____4362
        ; FStar_Syntax_Syntax.sigquals= []
        ; FStar_Syntax_Syntax.sigmeta= FStar_Syntax_Syntax.default_sigmeta
        ; FStar_Syntax_Syntax.sigattrs= [] }
    | uu____4367 ->
        let err_msg =
          let uu____4371 =
            let uu____4372 =
              FStar_Syntax_Syntax.mk_sigelt
                (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
            in
            FStar_Syntax_Print.sigelt_to_string uu____4372
          in
          FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n" uu____4371
        in
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg) err_range


let tc_assume
    : FStar_TypeChecker_Env.env -> FStar_Ident.lident
      -> FStar_Syntax_Syntax.formula
      -> FStar_Syntax_Syntax.qualifier Prims.list -> FStar_Range.range
      -> FStar_Syntax_Syntax.sigelt =
  fun env lid phi quals r ->
    let env1 = FStar_TypeChecker_Env.set_range env r in
    let uu____4397 = FStar_Syntax_Util.type_u () in
    match uu____4397 with k, uu____4403 ->
      let phi1 =
        let uu____4405 = tc_check_trivial_guard env1 phi k in
        FStar_All.pipe_right uu____4405
          (FStar_TypeChecker_Normalize.normalize
             [ FStar_TypeChecker_Normalize.Beta
             ; FStar_TypeChecker_Normalize.Eager_unfolding ] env1)
      in
      FStar_TypeChecker_Util.check_uvars r phi1 ;
      let uu____4407 = FStar_TypeChecker_Util.generalize_universes env1 phi1 in
      match uu____4407 with us, phi2 ->
        { FStar_Syntax_Syntax.sigel=
            FStar_Syntax_Syntax.Sig_assume (lid, us, phi2)
        ; FStar_Syntax_Syntax.sigrng= r
        ; FStar_Syntax_Syntax.sigquals= quals
        ; FStar_Syntax_Syntax.sigmeta= FStar_Syntax_Syntax.default_sigmeta
        ; FStar_Syntax_Syntax.sigattrs= [] }


let tc_inductive
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt Prims.list
      -> FStar_Syntax_Syntax.qualifier Prims.list
      -> FStar_Ident.lident Prims.list
      -> ( FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_Syntax_Syntax.sigelt Prims.list )
         FStar_Pervasives_Native.tuple2 =
  fun env ses quals lids ->
    let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
    let uu____4449 =
      FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1 ses
        quals lids
    in
    match uu____4449 with sig_bndle, tcs, datas ->
      let data_ops_ses =
        let uu____4482 =
          FStar_List.map
            (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
            datas
        in
        FStar_All.pipe_right uu____4482 FStar_List.flatten
      in
      (let uu____4496 =
         FStar_Options.no_positivity () || FStar_Options.lax ()
       in
       if uu____4496 then ()
       else
         let env2 = FStar_TypeChecker_Env.push_sigelt env1 sig_bndle in
         FStar_List.iter
           (fun ty ->
             let b = FStar_TypeChecker_TcInductive.check_positivity ty env2 in
             if Prims.op_Negation b then
               let uu____4507 =
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     ( lid
                     , uu____4517
                     , uu____4518
                     , uu____4519
                     , uu____4520
                     , uu____4521 ) ->
                     (lid, ty.FStar_Syntax_Syntax.sigrng)
                 | uu____4530 -> failwith "Impossible!"
               in
               match uu____4507 with lid, r ->
                 FStar_Errors.log_issue r
                   ( FStar_Errors.
                     Error_InductiveTypeNotSatisfyPositivityCondition
                   , Prims.strcat "Inductive type "
                       (Prims.strcat lid.FStar_Ident.str
                          " does not satisfy the positivity condition") )
             else () )
           tcs) ;
      let skip_prims_type uu____4541 =
        let lid =
          let ty = FStar_List.hd tcs in
          match ty.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (lid, uu____4545, uu____4546, uu____4547, uu____4548, uu____4549) ->
              lid
          | uu____4558 -> failwith "Impossible"
        in
        let types_to_skip =
          ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"]
        in
        FStar_List.existsb
          (fun s -> s = lid.FStar_Ident.ident.FStar_Ident.idText)
          types_to_skip
      in
      let is_noeq =
        FStar_List.existsb (fun q -> q = FStar_Syntax_Syntax.Noeq) quals
      in
      let res =
        let uu____4576 =
          ( FStar_List.length tcs = Prims.parse_int "0"
          || FStar_Ident.lid_equals env1.FStar_TypeChecker_Env.curmodule
               FStar_Parser_Const.prims_lid
             && skip_prims_type () )
          || is_noeq
        in
        if uu____4576 then ([sig_bndle], data_ops_ses)
        else
          let is_unopteq =
            FStar_List.existsb (fun q -> q = FStar_Syntax_Syntax.Unopteq) quals
          in
          let ses1 =
            if is_unopteq then
              FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle
                tcs datas env1 tc_assume
            else
              FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle
                tcs datas env1 tc_assume
          in
          let uu____4599 =
            let uu____4602 =
              let uu____4603 = FStar_TypeChecker_Env.get_range env1 in
              { FStar_Syntax_Syntax.sigel=
                  FStar_Syntax_Syntax.Sig_bundle
                    (FStar_List.append tcs datas, lids)
              ; FStar_Syntax_Syntax.sigrng= uu____4603
              ; FStar_Syntax_Syntax.sigquals= quals
              ; FStar_Syntax_Syntax.sigmeta=
                  FStar_Syntax_Syntax.default_sigmeta
              ; FStar_Syntax_Syntax.sigattrs= [] }
            in
            uu____4602 :: ses1
          in
          (uu____4599, data_ops_ses)
      in
      (let uu____4613 = FStar_TypeChecker_Env.pop env1 "tc_inductive" in
       ()) ;
      res


let tc_decl
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt
      -> ( FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_Syntax_Syntax.sigelt Prims.list )
         FStar_Pervasives_Native.tuple2 =
  fun env se ->
    let env1 = set_hint_correlator env se in
    FStar_TypeChecker_Util.check_sigelt_quals env1 se ;
    let r = se.FStar_Syntax_Syntax.sigrng in
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4647 ->
        failwith "Impossible bare data-constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____4672 ->
        failwith "Impossible bare data-constructor"
    | FStar_Syntax_Syntax.Sig_bundle (ses, lids)
      when FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid)) ->
        let env2 = FStar_TypeChecker_Env.set_range env1 r in
        let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids in
        ([se1], [])
    | FStar_Syntax_Syntax.Sig_bundle (ses, lids) -> (
        let env2 = FStar_TypeChecker_Env.set_range env1 r in
        let uu____4724 =
          tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids
        in
        match uu____4724 with ses1, projectors_ses -> (ses1, projectors_ses) )
    | FStar_Syntax_Syntax.Sig_pragma p ->
        FStar_Syntax_Util.process_pragma p r ;
        ([se], [])
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ne -> (
        let uu____4762 = cps_and_elaborate env1 ne in
        match uu____4762 with ses, ne1, lift_from_pure_opt ->
          let effect_and_lift_ses =
            match lift_from_pure_opt with
            | FStar_Pervasives_Native.Some lift ->
                [ (let uu___75_4799 = se in
                   { FStar_Syntax_Syntax.sigel=
                       FStar_Syntax_Syntax.Sig_new_effect ne1
                   ; FStar_Syntax_Syntax.sigrng=
                       uu___75_4799.FStar_Syntax_Syntax.sigrng
                   ; FStar_Syntax_Syntax.sigquals=
                       uu___75_4799.FStar_Syntax_Syntax.sigquals
                   ; FStar_Syntax_Syntax.sigmeta=
                       uu___75_4799.FStar_Syntax_Syntax.sigmeta
                   ; FStar_Syntax_Syntax.sigattrs=
                       uu___75_4799.FStar_Syntax_Syntax.sigattrs })
                ; lift ]
            | FStar_Pervasives_Native.None ->
                [ (let uu___76_4801 = se in
                   { FStar_Syntax_Syntax.sigel=
                       FStar_Syntax_Syntax.Sig_new_effect ne1
                   ; FStar_Syntax_Syntax.sigrng=
                       uu___76_4801.FStar_Syntax_Syntax.sigrng
                   ; FStar_Syntax_Syntax.sigquals=
                       uu___76_4801.FStar_Syntax_Syntax.sigquals
                   ; FStar_Syntax_Syntax.sigmeta=
                       uu___76_4801.FStar_Syntax_Syntax.sigmeta
                   ; FStar_Syntax_Syntax.sigattrs=
                       uu___76_4801.FStar_Syntax_Syntax.sigattrs }) ]
          in
          ([], FStar_List.append ses effect_and_lift_ses) )
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let ne1 = tc_eff_decl env1 ne in
        let se1 =
          let uu___77_4809 = se in
          { FStar_Syntax_Syntax.sigel= FStar_Syntax_Syntax.Sig_new_effect ne1
          ; FStar_Syntax_Syntax.sigrng= uu___77_4809.FStar_Syntax_Syntax.sigrng
          ; FStar_Syntax_Syntax.sigquals=
              uu___77_4809.FStar_Syntax_Syntax.sigquals
          ; FStar_Syntax_Syntax.sigmeta=
              uu___77_4809.FStar_Syntax_Syntax.sigmeta
          ; FStar_Syntax_Syntax.sigattrs=
              uu___77_4809.FStar_Syntax_Syntax.sigattrs }
        in
        ([se1], [])
    | FStar_Syntax_Syntax.Sig_sub_effect sub1 -> (
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env1
            sub1.FStar_Syntax_Syntax.source
        in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env1
            sub1.FStar_Syntax_Syntax.target
        in
        let uu____4817 =
          let uu____4824 =
            FStar_TypeChecker_Env.lookup_effect_lid env1
              sub1.FStar_Syntax_Syntax.source
          in
          monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4824
        in
        match uu____4817 with a, wp_a_src ->
          let uu____4839 =
            let uu____4846 =
              FStar_TypeChecker_Env.lookup_effect_lid env1
                sub1.FStar_Syntax_Syntax.target
            in
            monad_signature env1 sub1.FStar_Syntax_Syntax.target uu____4846
          in
          match uu____4839 with b, wp_b_tgt ->
            let wp_a_tgt =
              let uu____4862 =
                let uu____4865 =
                  let uu____4866 =
                    let uu____4873 = FStar_Syntax_Syntax.bv_to_name a in
                    (b, uu____4873)
                  in
                  FStar_Syntax_Syntax.NT uu____4866
                in
                [uu____4865]
              in
              FStar_Syntax_Subst.subst uu____4862 wp_b_tgt
            in
            let expected_k =
              let uu____4877 =
                let uu____4884 = FStar_Syntax_Syntax.mk_binder a in
                let uu____4885 =
                  let uu____4888 = FStar_Syntax_Syntax.null_binder wp_a_src in
                  [uu____4888]
                in
                uu____4884 :: uu____4885
              in
              let uu____4889 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
              FStar_Syntax_Util.arrow uu____4877 uu____4889
            in
            let repr_type eff_name a1 wp =
              let no_reify l =
                let uu____4910 =
                  let uu____4915 =
                    FStar_Util.format1 "Effect %s cannot be reified"
                      l.FStar_Ident.str
                  in
                  (FStar_Errors.Fatal_EffectCannotBeReified, uu____4915)
                in
                let uu____4916 = FStar_TypeChecker_Env.get_range env1 in
                FStar_Errors.raise_error uu____4910 uu____4916
              in
              let uu____4919 =
                FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
              in
              match uu____4919 with
              | FStar_Pervasives_Native.None -> no_reify eff_name
              | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                  let repr =
                    FStar_TypeChecker_Env.inst_effect_fun_with
                      [FStar_Syntax_Syntax.U_unknown] env1 ed
                      ([], ed.FStar_Syntax_Syntax.repr)
                  in
                  let uu____4951 =
                    let uu____4952 =
                      FStar_All.pipe_right qualifiers
                        (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                    in
                    Prims.op_Negation uu____4952
                  in
                  if uu____4951 then no_reify eff_name
                  else
                    let uu____4958 = FStar_TypeChecker_Env.get_range env1 in
                    let uu____4959 =
                      let uu____4962 =
                        let uu____4963 =
                          let uu____4978 =
                            let uu____4981 = FStar_Syntax_Syntax.as_arg a1 in
                            let uu____4982 =
                              let uu____4985 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____4985]
                            in
                            uu____4981 :: uu____4982
                          in
                          (repr, uu____4978)
                        in
                        FStar_Syntax_Syntax.Tm_app uu____4963
                      in
                      FStar_Syntax_Syntax.mk uu____4962
                    in
                    uu____4959 FStar_Pervasives_Native.None uu____4958
            in
            let uu____4991 =
              match
                ( sub1.FStar_Syntax_Syntax.lift
                , sub1.FStar_Syntax_Syntax.lift_wp )
              with
              | FStar_Pervasives_Native.None, FStar_Pervasives_Native.None ->
                  failwith "Impossible (parser)"
              | lift, FStar_Pervasives_Native.Some (uu____5019, lift_wp) ->
                  let uu____5043 = check_and_gen env1 lift_wp expected_k in
                  (lift, uu____5043)
              | ( FStar_Pervasives_Native.Some (what, lift)
                , FStar_Pervasives_Native.None ) ->
                  (let uu____5069 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "ED")
                   in
                   if uu____5069 then
                     let uu____5070 = FStar_Syntax_Print.term_to_string lift in
                     FStar_Util.print1 "Lift for free : %s\n" uu____5070
                   else ()) ;
                  let dmff_env =
                    FStar_TypeChecker_DMFF.empty env1
                      (FStar_TypeChecker_TcTerm.tc_constant env1
                         FStar_Range.dummyRange)
                  in
                  let uu____5073 =
                    FStar_TypeChecker_TcTerm.tc_term env1 lift
                  in
                  match uu____5073 with lift1, comp, uu____5088 ->
                    let uu____5089 =
                      FStar_TypeChecker_DMFF.star_expr dmff_env lift1
                    in
                    match uu____5089 with uu____5102, lift_wp, lift_elab ->
                      let uu____5105 = recheck_debug "lift-wp" env1 lift_wp in
                      let uu____5106 =
                        recheck_debug "lift-elab" env1 lift_elab
                      in
                      ( FStar_Pervasives_Native.Some ([], lift_elab)
                      , ([], lift_wp) )
            in
            match uu____4991 with lift, lift_wp ->
              let lax1 = env1.FStar_TypeChecker_Env.lax in
              let env2 =
                let uu___78_5147 = env1 in
                { FStar_TypeChecker_Env.solver=
                    uu___78_5147.FStar_TypeChecker_Env.solver
                ; FStar_TypeChecker_Env.range=
                    uu___78_5147.FStar_TypeChecker_Env.range
                ; FStar_TypeChecker_Env.curmodule=
                    uu___78_5147.FStar_TypeChecker_Env.curmodule
                ; FStar_TypeChecker_Env.gamma=
                    uu___78_5147.FStar_TypeChecker_Env.gamma
                ; FStar_TypeChecker_Env.gamma_cache=
                    uu___78_5147.FStar_TypeChecker_Env.gamma_cache
                ; FStar_TypeChecker_Env.modules=
                    uu___78_5147.FStar_TypeChecker_Env.modules
                ; FStar_TypeChecker_Env.expected_typ=
                    uu___78_5147.FStar_TypeChecker_Env.expected_typ
                ; FStar_TypeChecker_Env.sigtab=
                    uu___78_5147.FStar_TypeChecker_Env.sigtab
                ; FStar_TypeChecker_Env.is_pattern=
                    uu___78_5147.FStar_TypeChecker_Env.is_pattern
                ; FStar_TypeChecker_Env.instantiate_imp=
                    uu___78_5147.FStar_TypeChecker_Env.instantiate_imp
                ; FStar_TypeChecker_Env.effects=
                    uu___78_5147.FStar_TypeChecker_Env.effects
                ; FStar_TypeChecker_Env.generalize=
                    uu___78_5147.FStar_TypeChecker_Env.generalize
                ; FStar_TypeChecker_Env.letrecs=
                    uu___78_5147.FStar_TypeChecker_Env.letrecs
                ; FStar_TypeChecker_Env.top_level=
                    uu___78_5147.FStar_TypeChecker_Env.top_level
                ; FStar_TypeChecker_Env.check_uvars=
                    uu___78_5147.FStar_TypeChecker_Env.check_uvars
                ; FStar_TypeChecker_Env.use_eq=
                    uu___78_5147.FStar_TypeChecker_Env.use_eq
                ; FStar_TypeChecker_Env.is_iface=
                    uu___78_5147.FStar_TypeChecker_Env.is_iface
                ; FStar_TypeChecker_Env.admit=
                    uu___78_5147.FStar_TypeChecker_Env.admit
                ; FStar_TypeChecker_Env.lax= true
                ; FStar_TypeChecker_Env.lax_universes=
                    uu___78_5147.FStar_TypeChecker_Env.lax_universes
                ; FStar_TypeChecker_Env.failhard=
                    uu___78_5147.FStar_TypeChecker_Env.failhard
                ; FStar_TypeChecker_Env.nosynth=
                    uu___78_5147.FStar_TypeChecker_Env.nosynth
                ; FStar_TypeChecker_Env.tc_term=
                    uu___78_5147.FStar_TypeChecker_Env.tc_term
                ; FStar_TypeChecker_Env.type_of=
                    uu___78_5147.FStar_TypeChecker_Env.type_of
                ; FStar_TypeChecker_Env.universe_of=
                    uu___78_5147.FStar_TypeChecker_Env.universe_of
                ; FStar_TypeChecker_Env.check_type_of=
                    uu___78_5147.FStar_TypeChecker_Env.check_type_of
                ; FStar_TypeChecker_Env.use_bv_sorts=
                    uu___78_5147.FStar_TypeChecker_Env.use_bv_sorts
                ; FStar_TypeChecker_Env.qname_and_index=
                    uu___78_5147.FStar_TypeChecker_Env.qname_and_index
                ; FStar_TypeChecker_Env.proof_ns=
                    uu___78_5147.FStar_TypeChecker_Env.proof_ns
                ; FStar_TypeChecker_Env.synth=
                    uu___78_5147.FStar_TypeChecker_Env.synth
                ; FStar_TypeChecker_Env.is_native_tactic=
                    uu___78_5147.FStar_TypeChecker_Env.is_native_tactic
                ; FStar_TypeChecker_Env.identifier_info=
                    uu___78_5147.FStar_TypeChecker_Env.identifier_info
                ; FStar_TypeChecker_Env.tc_hooks=
                    uu___78_5147.FStar_TypeChecker_Env.tc_hooks
                ; FStar_TypeChecker_Env.dsenv=
                    uu___78_5147.FStar_TypeChecker_Env.dsenv
                ; FStar_TypeChecker_Env.dep_graph=
                    uu___78_5147.FStar_TypeChecker_Env.dep_graph }
              in
              let lift1 =
                match lift with
                | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (uu____5153, lift1) ->
                    let uu____5165 =
                      let uu____5172 =
                        FStar_TypeChecker_Env.lookup_effect_lid env2
                          sub1.FStar_Syntax_Syntax.source
                      in
                      monad_signature env2 sub1.FStar_Syntax_Syntax.source
                        uu____5172
                    in
                    match uu____5165 with a1, wp_a_src1 ->
                      let wp_a =
                        FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                          wp_a_src1
                      in
                      let a_typ = FStar_Syntax_Syntax.bv_to_name a1 in
                      let wp_a_typ = FStar_Syntax_Syntax.bv_to_name wp_a in
                      let repr_f =
                        repr_type sub1.FStar_Syntax_Syntax.source a_typ
                          wp_a_typ
                      in
                      let repr_result =
                        let lift_wp1 =
                          FStar_TypeChecker_Normalize.normalize
                            [ FStar_TypeChecker_Normalize.EraseUniverses
                            ; FStar_TypeChecker_Normalize.AllowUnboundUniverses
                            ] env2
                            (FStar_Pervasives_Native.snd lift_wp)
                        in
                        let lift_wp_a =
                          let uu____5196 =
                            FStar_TypeChecker_Env.get_range env2
                          in
                          let uu____5197 =
                            let uu____5200 =
                              let uu____5201 =
                                let uu____5216 =
                                  let uu____5219 =
                                    FStar_Syntax_Syntax.as_arg a_typ
                                  in
                                  let uu____5220 =
                                    let uu____5223 =
                                      FStar_Syntax_Syntax.as_arg wp_a_typ
                                    in
                                    [uu____5223]
                                  in
                                  uu____5219 :: uu____5220
                                in
                                (lift_wp1, uu____5216)
                              in
                              FStar_Syntax_Syntax.Tm_app uu____5201
                            in
                            FStar_Syntax_Syntax.mk uu____5200
                          in
                          uu____5197 FStar_Pervasives_Native.None uu____5196
                        in
                        repr_type sub1.FStar_Syntax_Syntax.target a_typ
                          lift_wp_a
                      in
                      let expected_k1 =
                        let uu____5232 =
                          let uu____5239 = FStar_Syntax_Syntax.mk_binder a1 in
                          let uu____5240 =
                            let uu____5243 =
                              FStar_Syntax_Syntax.mk_binder wp_a
                            in
                            let uu____5244 =
                              let uu____5247 =
                                FStar_Syntax_Syntax.null_binder repr_f
                              in
                              [uu____5247]
                            in
                            uu____5243 :: uu____5244
                          in
                          uu____5239 :: uu____5240
                        in
                        let uu____5248 =
                          FStar_Syntax_Syntax.mk_Total repr_result
                        in
                        FStar_Syntax_Util.arrow uu____5232 uu____5248
                      in
                      let uu____5251 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2
                          expected_k1
                      in
                      match uu____5251
                      with expected_k2, uu____5261, uu____5262 ->
                        let lift2 = check_and_gen env2 lift1 expected_k2 in
                        FStar_Pervasives_Native.Some lift2
              in
              let sub2 =
                let uu___79_5265 = sub1 in
                { FStar_Syntax_Syntax.source=
                    uu___79_5265.FStar_Syntax_Syntax.source
                ; FStar_Syntax_Syntax.target=
                    uu___79_5265.FStar_Syntax_Syntax.target
                ; FStar_Syntax_Syntax.lift_wp=
                    FStar_Pervasives_Native.Some lift_wp
                ; FStar_Syntax_Syntax.lift= lift1 }
              in
              let se1 =
                let uu___80_5267 = se in
                { FStar_Syntax_Syntax.sigel=
                    FStar_Syntax_Syntax.Sig_sub_effect sub2
                ; FStar_Syntax_Syntax.sigrng=
                    uu___80_5267.FStar_Syntax_Syntax.sigrng
                ; FStar_Syntax_Syntax.sigquals=
                    uu___80_5267.FStar_Syntax_Syntax.sigquals
                ; FStar_Syntax_Syntax.sigmeta=
                    uu___80_5267.FStar_Syntax_Syntax.sigmeta
                ; FStar_Syntax_Syntax.sigattrs=
                    uu___80_5267.FStar_Syntax_Syntax.sigattrs }
              in
              ([se1], []) )
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags1) -> (
        let env0 = env1 in
        let env2 = FStar_TypeChecker_Env.set_range env1 r in
        let uu____5286 = FStar_Syntax_Subst.open_comp tps c in
        match uu____5286 with tps1, c1 ->
          let uu____5301 = FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
          match uu____5301 with tps2, env3, us ->
            let uu____5319 = FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
            match uu____5319 with c2, u, g ->
              FStar_TypeChecker_Rel.force_trivial_guard env3 g ;
              let tps3 = FStar_Syntax_Subst.close_binders tps2 in
              let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
              let uu____5340 =
                let uu____5341 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                    FStar_Pervasives_Native.None r
                in
                FStar_TypeChecker_Util.generalize_universes env0 uu____5341
              in
              match uu____5340 with uvs1, t ->
                let uu____5356 =
                  let uu____5369 =
                    let uu____5374 =
                      let uu____5375 = FStar_Syntax_Subst.compress t in
                      uu____5375.FStar_Syntax_Syntax.n
                    in
                    (tps3, uu____5374)
                  in
                  match uu____5369 with
                  | [], FStar_Syntax_Syntax.Tm_arrow (uu____5390, c4) ->
                      ([], c4)
                  | uu____5430, FStar_Syntax_Syntax.Tm_arrow (tps4, c4) ->
                      (tps4, c4)
                  | uu____5457 -> failwith "Impossible (t is an arrow)"
                in
                match uu____5356 with tps4, c4 ->
                  if FStar_List.length uvs1 <> Prims.parse_int "1" then
                    let uu____5501 =
                      FStar_Syntax_Subst.open_univ_vars uvs1 t
                    in
                    match uu____5501 with uu____5506, t1 ->
                      let uu____5508 =
                        let uu____5513 =
                          let uu____5514 =
                            FStar_Syntax_Print.lid_to_string lid
                          in
                          let uu____5515 =
                            FStar_All.pipe_right (FStar_List.length uvs1)
                              FStar_Util.string_of_int
                          in
                          let uu____5516 =
                            FStar_Syntax_Print.term_to_string t1
                          in
                          FStar_Util.format3
                            "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                            uu____5514 uu____5515 uu____5516
                        in
                        (FStar_Errors.Fatal_TooManyUniverse, uu____5513)
                      in
                      FStar_Errors.raise_error uu____5508 r
                  else () ;
                  let se1 =
                    let uu___81_5519 = se in
                    { FStar_Syntax_Syntax.sigel=
                        FStar_Syntax_Syntax.Sig_effect_abbrev
                          (lid, uvs1, tps4, c4, flags1)
                    ; FStar_Syntax_Syntax.sigrng=
                        uu___81_5519.FStar_Syntax_Syntax.sigrng
                    ; FStar_Syntax_Syntax.sigquals=
                        uu___81_5519.FStar_Syntax_Syntax.sigquals
                    ; FStar_Syntax_Syntax.sigmeta=
                        uu___81_5519.FStar_Syntax_Syntax.sigmeta
                    ; FStar_Syntax_Syntax.sigattrs=
                        uu___81_5519.FStar_Syntax_Syntax.sigattrs }
                  in
                  ([se1], []) )
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____5536, uu____5537, uu____5538)
      when FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some (fun uu___56_5542 ->
                  match uu___56_5542 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____5543 -> false )) ->
        ([], [])
    | FStar_Syntax_Syntax.Sig_let (uu____5548, uu____5549)
      when FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some (fun uu___56_5557 ->
                  match uu___56_5557 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____5558 -> false )) ->
        ([], [])
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> (
        let env2 = FStar_TypeChecker_Env.set_range env1 r in
        (let uu____5568 = FStar_TypeChecker_Env.lid_exists env2 lid in
         if uu____5568 then
           let uu____5569 =
             let uu____5574 =
               FStar_Util.format1
                 "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                 (FStar_Ident.text_of_lid lid)
             in
             (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration, uu____5574)
           in
           FStar_Errors.raise_error uu____5569 r
         else ()) ;
        let uu____5576 =
          if uvs = [] then
            let uu____5577 =
              let uu____5578 = FStar_Syntax_Util.type_u () in
              FStar_Pervasives_Native.fst uu____5578
            in
            check_and_gen env2 t uu____5577
          else
            let uu____5584 = FStar_Syntax_Subst.open_univ_vars uvs t in
            match uu____5584 with uvs1, t1 ->
              let t2 =
                let uu____5592 =
                  let uu____5593 = FStar_Syntax_Util.type_u () in
                  FStar_Pervasives_Native.fst uu____5593
                in
                tc_check_trivial_guard env2 t1 uu____5592
              in
              let t3 =
                FStar_TypeChecker_Normalize.normalize
                  [ FStar_TypeChecker_Normalize.NoFullNorm
                  ; FStar_TypeChecker_Normalize.Beta ] env2 t2
              in
              let uu____5599 = FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
              (uvs1, uu____5599)
        in
        match uu____5576 with uvs1, t1 ->
          let se1 =
            let uu___82_5615 = se in
            { FStar_Syntax_Syntax.sigel=
                FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1)
            ; FStar_Syntax_Syntax.sigrng=
                uu___82_5615.FStar_Syntax_Syntax.sigrng
            ; FStar_Syntax_Syntax.sigquals=
                uu___82_5615.FStar_Syntax_Syntax.sigquals
            ; FStar_Syntax_Syntax.sigmeta=
                uu___82_5615.FStar_Syntax_Syntax.sigmeta
            ; FStar_Syntax_Syntax.sigattrs=
                uu___82_5615.FStar_Syntax_Syntax.sigattrs }
          in
          ([se1], []) )
    | FStar_Syntax_Syntax.Sig_assume (lid, us, phi) -> (
        let uu____5625 = FStar_Syntax_Subst.open_univ_vars us phi in
        match uu____5625 with uu____5638, phi1 ->
          let se1 =
            tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r
          in
          ([se1], []) )
    | FStar_Syntax_Syntax.Sig_main e -> (
        let env2 = FStar_TypeChecker_Env.set_range env1 r in
        let env3 =
          FStar_TypeChecker_Env.set_expected_typ env2
            FStar_Syntax_Syntax.t_unit
        in
        let uu____5648 = FStar_TypeChecker_TcTerm.tc_term env3 e in
        match uu____5648 with e1, c, g1 ->
          let uu____5666 =
            let uu____5673 =
              let uu____5676 =
                FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
              in
              FStar_Pervasives_Native.Some uu____5676
            in
            let uu____5677 =
              let uu____5682 = FStar_Syntax_Syntax.lcomp_comp c in
              (e1, uu____5682)
            in
            FStar_TypeChecker_TcTerm.check_expected_effect env3 uu____5673
              uu____5677
          in
          match uu____5666 with e2, uu____5692, g ->
            (let uu____5695 = FStar_TypeChecker_Rel.conj_guard g1 g in
             FStar_TypeChecker_Rel.force_trivial_guard env3 uu____5695) ;
            let se1 =
              let uu___83_5697 = se in
              { FStar_Syntax_Syntax.sigel= FStar_Syntax_Syntax.Sig_main e2
              ; FStar_Syntax_Syntax.sigrng=
                  uu___83_5697.FStar_Syntax_Syntax.sigrng
              ; FStar_Syntax_Syntax.sigquals=
                  uu___83_5697.FStar_Syntax_Syntax.sigquals
              ; FStar_Syntax_Syntax.sigmeta=
                  uu___83_5697.FStar_Syntax_Syntax.sigmeta
              ; FStar_Syntax_Syntax.sigattrs=
                  uu___83_5697.FStar_Syntax_Syntax.sigattrs }
            in
            ([se1], []) )
    | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
        let env2 = FStar_TypeChecker_Env.set_range env1 r in
        let check_quals_eq l qopt q =
          match qopt with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some q
          | FStar_Pervasives_Native.Some q' ->
              let uu____5748 =
                FStar_List.length q = FStar_List.length q'
                && FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'
              in
              if uu____5748 then FStar_Pervasives_Native.Some q
              else
                let uu____5756 =
                  let uu____5761 =
                    let uu____5762 = FStar_Syntax_Print.lid_to_string l in
                    let uu____5763 = FStar_Syntax_Print.quals_to_string q in
                    let uu____5764 = FStar_Syntax_Print.quals_to_string q' in
                    FStar_Util.format3
                      "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                      uu____5762 uu____5763 uu____5764
                  in
                  ( FStar_Errors.Fatal_InconsistentQualifierAnnotation
                  , uu____5761 )
                in
                FStar_Errors.raise_error uu____5756 r
        in
        let rename_parameters lb =
          let rename_in_typ def typ =
            let typ1 = FStar_Syntax_Subst.compress typ in
            let def_bs =
              let uu____5790 =
                let uu____5791 = FStar_Syntax_Subst.compress def in
                uu____5791.FStar_Syntax_Syntax.n
              in
              match uu____5790 with
              | FStar_Syntax_Syntax.Tm_abs (binders, uu____5801, uu____5802) ->
                  binders
              | uu____5823 -> []
            in
            match typ1 with
            | { FStar_Syntax_Syntax.n= FStar_Syntax_Syntax.Tm_arrow (val_bs, c)
              ; FStar_Syntax_Syntax.pos= r1
              ; FStar_Syntax_Syntax.vars= uu____5833; _ } ->
                let has_auto_name bv =
                  FStar_Util.starts_with
                    bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
                    FStar_Ident.reserved_prefix
                in
                let rec rename_binders1 def_bs1 val_bs1 =
                  match (def_bs1, val_bs1) with
                  | [], uu____5911 -> val_bs1
                  | uu____5934, [] -> val_bs1
                  | (body_bv, uu____5958) :: bt, (val_bv, aqual) :: vt ->
                      let uu____5995 = rename_binders1 bt vt in
                      ( match (has_auto_name body_bv, has_auto_name val_bv) with
                      | true, uu____6011 -> (val_bv, aqual)
                      | false, true ->
                          ( (let uu___84_6013 = val_bv in
                             { FStar_Syntax_Syntax.ppname=
                                 (let uu___85_6016 =
                                    val_bv.FStar_Syntax_Syntax.ppname
                                  in
                                  { FStar_Ident.idText=
                                      body_bv.FStar_Syntax_Syntax.ppname
                                        .FStar_Ident.idText
                                  ; FStar_Ident.idRange=
                                      uu___85_6016.FStar_Ident.idRange })
                             ; FStar_Syntax_Syntax.index=
                                 uu___84_6013.FStar_Syntax_Syntax.index
                             ; FStar_Syntax_Syntax.sort=
                                 uu___84_6013.FStar_Syntax_Syntax.sort })
                          , aqual )
                      | false, false -> (val_bv, aqual) )
                      :: uu____5995
                in
                let uu____6017 =
                  let uu____6020 =
                    let uu____6021 =
                      let uu____6034 = rename_binders1 def_bs val_bs in
                      (uu____6034, c)
                    in
                    FStar_Syntax_Syntax.Tm_arrow uu____6021
                  in
                  FStar_Syntax_Syntax.mk uu____6020
                in
                uu____6017 FStar_Pervasives_Native.None r1
            | uu____6052 -> typ1
          in
          let uu___86_6053 = lb in
          let uu____6054 =
            rename_in_typ lb.FStar_Syntax_Syntax.lbdef
              lb.FStar_Syntax_Syntax.lbtyp
          in
          { FStar_Syntax_Syntax.lbname= uu___86_6053.FStar_Syntax_Syntax.lbname
          ; FStar_Syntax_Syntax.lbunivs=
              uu___86_6053.FStar_Syntax_Syntax.lbunivs
          ; FStar_Syntax_Syntax.lbtyp= uu____6054
          ; FStar_Syntax_Syntax.lbeff= uu___86_6053.FStar_Syntax_Syntax.lbeff
          ; FStar_Syntax_Syntax.lbdef= uu___86_6053.FStar_Syntax_Syntax.lbdef
          ; FStar_Syntax_Syntax.lbattrs=
              uu___86_6053.FStar_Syntax_Syntax.lbattrs }
        in
        let uu____6057 =
          FStar_All.pipe_right
            (FStar_Pervasives_Native.snd lbs)
            (FStar_List.fold_left
               (fun uu____6108 lb ->
                 match uu____6108 with gen1, lbs1, quals_opt ->
                   let lbname =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                   in
                   let uu____6150 =
                     let uu____6161 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env2
                         lbname.FStar_Syntax_Syntax.fv_name
                           .FStar_Syntax_Syntax.v
                     in
                     match uu____6161 with
                     | FStar_Pervasives_Native.None ->
                         if lb.FStar_Syntax_Syntax.lbunivs <> [] then
                           (false, lb, quals_opt)
                         else (gen1, lb, quals_opt)
                     | FStar_Pervasives_Native.Some ((uvs, tval), quals) ->
                         let quals_opt1 =
                           check_quals_eq
                             lbname.FStar_Syntax_Syntax.fv_name
                               .FStar_Syntax_Syntax.v quals_opt quals
                         in
                         let def =
                           match
                             lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n
                           with
                           | FStar_Syntax_Syntax.Tm_unknown ->
                               lb.FStar_Syntax_Syntax.lbdef
                           | uu____6246 ->
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ( lb.FStar_Syntax_Syntax.lbdef
                                    , ( FStar_Util.Inl
                                          lb.FStar_Syntax_Syntax.lbtyp
                                      , FStar_Pervasives_Native.None )
                                    , FStar_Pervasives_Native.None ))
                                 FStar_Pervasives_Native.None
                                 lb.FStar_Syntax_Syntax.lbdef
                                   .FStar_Syntax_Syntax.pos
                         in
                         if lb.FStar_Syntax_Syntax.lbunivs <> []
                            && FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
                               <> FStar_List.length uvs
                         then
                           FStar_Errors.raise_error
                             ( FStar_Errors.Fatal_IncoherentInlineUniverse
                             , "Inline universes are incoherent with annotation from val declaration"
                             ) r
                         else () ;
                         let uu____6289 =
                           FStar_Syntax_Syntax.mk_lb
                             ( FStar_Util.Inr lbname
                             , uvs
                             , FStar_Parser_Const.effect_ALL_lid
                             , tval
                             , def )
                         in
                         (false, uu____6289, quals_opt1)
                   in
                   match uu____6150 with gen2, lb1, quals_opt1 ->
                     (gen2, lb1 :: lbs1, quals_opt1) )
               ( true
               , []
               , if se.FStar_Syntax_Syntax.sigquals = [] then
                   FStar_Pervasives_Native.None
                 else
                   FStar_Pervasives_Native.Some se.FStar_Syntax_Syntax.sigquals
               ))
        in
        match uu____6057 with should_generalize, lbs', quals_opt ->
          let quals =
            match quals_opt with
            | FStar_Pervasives_Native.None ->
                [FStar_Syntax_Syntax.Visible_default]
            | FStar_Pervasives_Native.Some q ->
                let uu____6383 =
                  FStar_All.pipe_right q
                    (FStar_Util.for_some (fun uu___57_6387 ->
                         match uu___57_6387 with
                         | FStar_Syntax_Syntax.Irreducible -> true
                         | FStar_Syntax_Syntax.Visible_default -> true
                         | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
                             true
                         | uu____6388 -> false ))
                in
                if uu____6383 then q
                else FStar_Syntax_Syntax.Visible_default :: q
          in
          let lbs'1 = FStar_List.rev lbs' in
          let e =
            let uu____6398 =
              let uu____6401 =
                let uu____6402 =
                  let uu____6415 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
                      FStar_Pervasives_Native.None r
                  in
                  ((FStar_Pervasives_Native.fst lbs, lbs'1), uu____6415)
                in
                FStar_Syntax_Syntax.Tm_let uu____6402
              in
              FStar_Syntax_Syntax.mk uu____6401
            in
            uu____6398 FStar_Pervasives_Native.None r
          in
          let uu____6433 =
            let uu____6444 =
              FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                (let uu___87_6453 = env2 in
                 { FStar_TypeChecker_Env.solver=
                     uu___87_6453.FStar_TypeChecker_Env.solver
                 ; FStar_TypeChecker_Env.range=
                     uu___87_6453.FStar_TypeChecker_Env.range
                 ; FStar_TypeChecker_Env.curmodule=
                     uu___87_6453.FStar_TypeChecker_Env.curmodule
                 ; FStar_TypeChecker_Env.gamma=
                     uu___87_6453.FStar_TypeChecker_Env.gamma
                 ; FStar_TypeChecker_Env.gamma_cache=
                     uu___87_6453.FStar_TypeChecker_Env.gamma_cache
                 ; FStar_TypeChecker_Env.modules=
                     uu___87_6453.FStar_TypeChecker_Env.modules
                 ; FStar_TypeChecker_Env.expected_typ=
                     uu___87_6453.FStar_TypeChecker_Env.expected_typ
                 ; FStar_TypeChecker_Env.sigtab=
                     uu___87_6453.FStar_TypeChecker_Env.sigtab
                 ; FStar_TypeChecker_Env.is_pattern=
                     uu___87_6453.FStar_TypeChecker_Env.is_pattern
                 ; FStar_TypeChecker_Env.instantiate_imp=
                     uu___87_6453.FStar_TypeChecker_Env.instantiate_imp
                 ; FStar_TypeChecker_Env.effects=
                     uu___87_6453.FStar_TypeChecker_Env.effects
                 ; FStar_TypeChecker_Env.generalize= should_generalize
                 ; FStar_TypeChecker_Env.letrecs=
                     uu___87_6453.FStar_TypeChecker_Env.letrecs
                 ; FStar_TypeChecker_Env.top_level= true
                 ; FStar_TypeChecker_Env.check_uvars=
                     uu___87_6453.FStar_TypeChecker_Env.check_uvars
                 ; FStar_TypeChecker_Env.use_eq=
                     uu___87_6453.FStar_TypeChecker_Env.use_eq
                 ; FStar_TypeChecker_Env.is_iface=
                     uu___87_6453.FStar_TypeChecker_Env.is_iface
                 ; FStar_TypeChecker_Env.admit=
                     uu___87_6453.FStar_TypeChecker_Env.admit
                 ; FStar_TypeChecker_Env.lax=
                     uu___87_6453.FStar_TypeChecker_Env.lax
                 ; FStar_TypeChecker_Env.lax_universes=
                     uu___87_6453.FStar_TypeChecker_Env.lax_universes
                 ; FStar_TypeChecker_Env.failhard=
                     uu___87_6453.FStar_TypeChecker_Env.failhard
                 ; FStar_TypeChecker_Env.nosynth=
                     uu___87_6453.FStar_TypeChecker_Env.nosynth
                 ; FStar_TypeChecker_Env.tc_term=
                     uu___87_6453.FStar_TypeChecker_Env.tc_term
                 ; FStar_TypeChecker_Env.type_of=
                     uu___87_6453.FStar_TypeChecker_Env.type_of
                 ; FStar_TypeChecker_Env.universe_of=
                     uu___87_6453.FStar_TypeChecker_Env.universe_of
                 ; FStar_TypeChecker_Env.check_type_of=
                     uu___87_6453.FStar_TypeChecker_Env.check_type_of
                 ; FStar_TypeChecker_Env.use_bv_sorts=
                     uu___87_6453.FStar_TypeChecker_Env.use_bv_sorts
                 ; FStar_TypeChecker_Env.qname_and_index=
                     uu___87_6453.FStar_TypeChecker_Env.qname_and_index
                 ; FStar_TypeChecker_Env.proof_ns=
                     uu___87_6453.FStar_TypeChecker_Env.proof_ns
                 ; FStar_TypeChecker_Env.synth=
                     uu___87_6453.FStar_TypeChecker_Env.synth
                 ; FStar_TypeChecker_Env.is_native_tactic=
                     uu___87_6453.FStar_TypeChecker_Env.is_native_tactic
                 ; FStar_TypeChecker_Env.identifier_info=
                     uu___87_6453.FStar_TypeChecker_Env.identifier_info
                 ; FStar_TypeChecker_Env.tc_hooks=
                     uu___87_6453.FStar_TypeChecker_Env.tc_hooks
                 ; FStar_TypeChecker_Env.dsenv=
                     uu___87_6453.FStar_TypeChecker_Env.dsenv
                 ; FStar_TypeChecker_Env.dep_graph=
                     uu___87_6453.FStar_TypeChecker_Env.dep_graph })
                e
            in
            match uu____6444 with
            | ( { FStar_Syntax_Syntax.n= FStar_Syntax_Syntax.Tm_let (lbs1, e1)
                ; FStar_Syntax_Syntax.pos= uu____6466
                ; FStar_Syntax_Syntax.vars= uu____6467; _ }
              , uu____6468
              , g )
              when FStar_TypeChecker_Rel.is_trivial g ->
                let lbs2 =
                  let uu____6497 =
                    FStar_All.pipe_right
                      (FStar_Pervasives_Native.snd lbs1)
                      (FStar_List.map rename_parameters)
                  in
                  (FStar_Pervasives_Native.fst lbs1, uu____6497)
                in
                let quals1 =
                  match e1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_meta
                      ( uu____6515
                      , FStar_Syntax_Syntax.Meta_desugared
                          FStar_Syntax_Syntax.Masked_effect ) ->
                      FStar_Syntax_Syntax.HasMaskedEffect :: quals
                  | uu____6520 -> quals
                in
                ( (let uu___88_6528 = se in
                   { FStar_Syntax_Syntax.sigel=
                       FStar_Syntax_Syntax.Sig_let (lbs2, lids)
                   ; FStar_Syntax_Syntax.sigrng=
                       uu___88_6528.FStar_Syntax_Syntax.sigrng
                   ; FStar_Syntax_Syntax.sigquals= quals1
                   ; FStar_Syntax_Syntax.sigmeta=
                       uu___88_6528.FStar_Syntax_Syntax.sigmeta
                   ; FStar_Syntax_Syntax.sigattrs=
                       uu___88_6528.FStar_Syntax_Syntax.sigattrs })
                , lbs2 )
            | uu____6537 ->
                failwith "impossible (typechecking should preserve Tm_let)"
          in
          match uu____6433 with se1, lbs1 ->
            FStar_All.pipe_right
              (FStar_Pervasives_Native.snd lbs1)
              (FStar_List.iter (fun lb ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   FStar_TypeChecker_Env.insert_fv_info env2 fv
                     lb.FStar_Syntax_Syntax.lbtyp )) ;
            (let uu____6586 = log env2 in
             if uu____6586 then
               let uu____6587 =
                 let uu____6588 =
                   FStar_All.pipe_right
                     (FStar_Pervasives_Native.snd lbs1)
                     (FStar_List.map (fun lb ->
                          let should_log =
                            let uu____6603 =
                              let uu____6612 =
                                let uu____6613 =
                                  let uu____6616 =
                                    FStar_Util.right
                                      lb.FStar_Syntax_Syntax.lbname
                                  in
                                  uu____6616.FStar_Syntax_Syntax.fv_name
                                in
                                uu____6613.FStar_Syntax_Syntax.v
                              in
                              FStar_TypeChecker_Env.try_lookup_val_decl env2
                                uu____6612
                            in
                            match uu____6603 with
                            | FStar_Pervasives_Native.None -> true
                            | uu____6623 -> false
                          in
                          if should_log then
                            let uu____6632 =
                              FStar_Syntax_Print.lbname_to_string
                                lb.FStar_Syntax_Syntax.lbname
                            in
                            let uu____6633 =
                              FStar_Syntax_Print.term_to_string
                                lb.FStar_Syntax_Syntax.lbtyp
                            in
                            FStar_Util.format2 "let %s : %s" uu____6632
                              uu____6633
                          else "" ))
                 in
                 FStar_All.pipe_right uu____6588 (FStar_String.concat "\n")
               in
               FStar_Util.print1 "%s\n" uu____6587
             else ()) ;
            let reified_tactic_type l t =
              let t1 = FStar_Syntax_Subst.compress t in
              match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs, c) -> (
                  let uu____6664 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____6664 with bs1, c1 ->
                    let uu____6671 = FStar_Syntax_Util.is_total_comp c1 in
                    if uu____6671 then
                      let c' =
                        match c1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t', u) -> (
                            let uu____6683 =
                              let uu____6684 =
                                FStar_Syntax_Subst.compress t'
                              in
                              uu____6684.FStar_Syntax_Syntax.n
                            in
                            match uu____6683 with
                            | FStar_Syntax_Syntax.Tm_app (h, args) -> (
                                let uu____6709 =
                                  let uu____6710 =
                                    FStar_Syntax_Subst.compress h
                                  in
                                  uu____6710.FStar_Syntax_Syntax.n
                                in
                                match uu____6709 with
                                | FStar_Syntax_Syntax.Tm_uinst (h', u') ->
                                    let h'' =
                                      let uu____6720 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          FStar_Parser_Const.u_tac_lid
                                          FStar_Syntax_Syntax.Delta_constant
                                          FStar_Pervasives_Native.None
                                      in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Syntax.fv_to_tm uu____6720
                                    in
                                    let uu____6721 =
                                      let uu____6722 =
                                        let uu____6723 =
                                          FStar_Syntax_Syntax.mk_Tm_uinst h''
                                            u'
                                        in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____6723 args
                                      in
                                      uu____6722 FStar_Pervasives_Native.None
                                        t'.FStar_Syntax_Syntax.pos
                                    in
                                    FStar_Syntax_Syntax.mk_Total' uu____6721 u
                                | uu____6726 -> c1 )
                            | uu____6727 -> c1 )
                        | uu____6728 -> c1
                      in
                      let uu___89_6729 = t1 in
                      let uu____6730 =
                        let uu____6731 =
                          let uu____6744 =
                            FStar_Syntax_Subst.close_comp bs1 c'
                          in
                          (bs1, uu____6744)
                        in
                        FStar_Syntax_Syntax.Tm_arrow uu____6731
                      in
                      { FStar_Syntax_Syntax.n= uu____6730
                      ; FStar_Syntax_Syntax.pos=
                          uu___89_6729.FStar_Syntax_Syntax.pos
                      ; FStar_Syntax_Syntax.vars=
                          uu___89_6729.FStar_Syntax_Syntax.vars }
                    else t1 )
              | FStar_Syntax_Syntax.Tm_app (h, args) -> (
                  let uu____6768 =
                    let uu____6769 = FStar_Syntax_Subst.compress h in
                    uu____6769.FStar_Syntax_Syntax.n
                  in
                  match uu____6768 with
                  | FStar_Syntax_Syntax.Tm_uinst (h', u') ->
                      let h'' =
                        let uu____6779 =
                          FStar_Syntax_Syntax.lid_as_fv
                            FStar_Parser_Const.u_tac_lid
                            FStar_Syntax_Syntax.Delta_constant
                            FStar_Pervasives_Native.None
                        in
                        FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                          uu____6779
                      in
                      let uu____6780 =
                        let uu____6781 =
                          FStar_Syntax_Syntax.mk_Tm_uinst h'' u'
                        in
                        FStar_Syntax_Syntax.mk_Tm_app uu____6781 args
                      in
                      uu____6780 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                  | uu____6784 -> t1 )
              | uu____6785 -> t1
            in
            let reified_tactic_decl assm_lid lb =
              let t =
                reified_tactic_type assm_lid lb.FStar_Syntax_Syntax.lbtyp
              in
              { FStar_Syntax_Syntax.sigel=
                  FStar_Syntax_Syntax.Sig_declare_typ
                    (assm_lid, lb.FStar_Syntax_Syntax.lbunivs, t)
              ; FStar_Syntax_Syntax.sigrng= FStar_Ident.range_of_lid assm_lid
              ; FStar_Syntax_Syntax.sigquals= [FStar_Syntax_Syntax.Assumption]
              ; FStar_Syntax_Syntax.sigmeta=
                  FStar_Syntax_Syntax.default_sigmeta
              ; FStar_Syntax_Syntax.sigattrs= [] }
            in
            let reflected_tactic_decl b lb bs assm_lid comp =
              let reified_tac =
                let uu____6813 =
                  FStar_Syntax_Syntax.lid_as_fv assm_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                in
                FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____6813
              in
              let tac_args =
                FStar_List.map
                  (fun x ->
                    let uu____6830 =
                      FStar_Syntax_Syntax.bv_to_name
                        (FStar_Pervasives_Native.fst x)
                    in
                    (uu____6830, FStar_Pervasives_Native.snd x) )
                  bs
              in
              let reflect_head =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_reflect
                        FStar_Parser_Const.tac_effect_lid))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
              let refl_arg =
                FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
              let app =
                FStar_Syntax_Syntax.mk_Tm_app reflect_head
                  [(refl_arg, FStar_Pervasives_Native.None)]
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
              let unit_binder =
                let uu____6861 =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    FStar_Syntax_Syntax.t_unit
                in
                FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____6861
              in
              let body =
                FStar_All.pipe_left
                  (FStar_Syntax_Util.abs [unit_binder] app)
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.residual_comp_of_comp comp))
              in
              let func =
                FStar_All.pipe_left
                  (FStar_Syntax_Util.abs bs body)
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.residual_comp_of_comp comp))
              in
              let uu___90_6868 = se1 in
              { FStar_Syntax_Syntax.sigel=
                  FStar_Syntax_Syntax.Sig_let
                    ( ( b
                      , [ (let uu___91_6880 = lb in
                           { FStar_Syntax_Syntax.lbname=
                               uu___91_6880.FStar_Syntax_Syntax.lbname
                           ; FStar_Syntax_Syntax.lbunivs=
                               uu___91_6880.FStar_Syntax_Syntax.lbunivs
                           ; FStar_Syntax_Syntax.lbtyp=
                               uu___91_6880.FStar_Syntax_Syntax.lbtyp
                           ; FStar_Syntax_Syntax.lbeff=
                               uu___91_6880.FStar_Syntax_Syntax.lbeff
                           ; FStar_Syntax_Syntax.lbdef= func
                           ; FStar_Syntax_Syntax.lbattrs=
                               uu___91_6880.FStar_Syntax_Syntax.lbattrs }) ] )
                    , lids )
              ; FStar_Syntax_Syntax.sigrng=
                  uu___90_6868.FStar_Syntax_Syntax.sigrng
              ; FStar_Syntax_Syntax.sigquals=
                  uu___90_6868.FStar_Syntax_Syntax.sigquals
              ; FStar_Syntax_Syntax.sigmeta=
                  uu___90_6868.FStar_Syntax_Syntax.sigmeta
              ; FStar_Syntax_Syntax.sigattrs=
                  uu___90_6868.FStar_Syntax_Syntax.sigattrs }
            in
            let tactic_decls =
              match FStar_Pervasives_Native.snd lbs1 with
              | [hd1] -> (
                  let uu____6897 =
                    FStar_Syntax_Util.arrow_formals_comp
                      hd1.FStar_Syntax_Syntax.lbtyp
                  in
                  match uu____6897 with bs, comp ->
                    let t = FStar_Syntax_Util.comp_result comp in
                    let uu____6931 =
                      let uu____6932 = FStar_Syntax_Subst.compress t in
                      uu____6932.FStar_Syntax_Syntax.n
                    in
                    match uu____6931 with
                    | FStar_Syntax_Syntax.Tm_app (h, args) -> (
                        let h1 = FStar_Syntax_Subst.compress h in
                        let tac_lid =
                          let uu____6965 =
                            let uu____6968 =
                              FStar_Util.right hd1.FStar_Syntax_Syntax.lbname
                            in
                            uu____6968.FStar_Syntax_Syntax.fv_name
                          in
                          uu____6965.FStar_Syntax_Syntax.v
                        in
                        let assm_lid =
                          let uu____6970 =
                            FStar_All.pipe_left FStar_Ident.id_of_text
                              (Prims.strcat "__"
                                 tac_lid.FStar_Ident.ident.FStar_Ident.idText)
                          in
                          FStar_Ident.lid_of_ns_and_id tac_lid.FStar_Ident.ns
                            uu____6970
                        in
                        let uu____6971 = get_tactic_fv env2 assm_lid h1 in
                        match uu____6971 with
                        | FStar_Pervasives_Native.Some fv ->
                            let uu____6981 =
                              let uu____6982 =
                                let uu____6983 =
                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                    env2 tac_lid
                                in
                                FStar_All.pipe_left FStar_Util.is_some
                                  uu____6983
                              in
                              Prims.op_Negation uu____6982
                            in
                            if uu____6981 then (
                              (let uu____7013 =
                                 let uu____7014 =
                                   FStar_Syntax_Util.is_builtin_tactic
                                     env2.FStar_TypeChecker_Env.curmodule
                                 in
                                 Prims.op_Negation uu____7014
                               in
                               if uu____7013 then
                                 let added_modules =
                                   FStar_ST.op_Bang user_tactics_modules
                                 in
                                 let module_name =
                                   FStar_Ident.ml_path_of_lid
                                     env2.FStar_TypeChecker_Env.curmodule
                                 in
                                 if Prims.op_Negation
                                      (FStar_List.contains module_name
                                         added_modules)
                                 then
                                   FStar_ST.op_Colon_Equals
                                     user_tactics_modules
                                     (FStar_List.append added_modules
                                        [module_name])
                                 else ()
                               else ()) ;
                              let uu____7067 =
                                env2.FStar_TypeChecker_Env.is_native_tactic
                                  assm_lid
                              in
                              if uu____7067 then
                                let se_assm =
                                  reified_tactic_decl assm_lid hd1
                                in
                                let se_refl =
                                  reflected_tactic_decl
                                    (FStar_Pervasives_Native.fst lbs1)
                                    hd1 bs assm_lid comp
                                in
                                FStar_Pervasives_Native.Some (se_assm, se_refl)
                              else FStar_Pervasives_Native.None )
                            else FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None )
                    | uu____7096 -> FStar_Pervasives_Native.None )
              | uu____7101 -> FStar_Pervasives_Native.None
            in
            match tactic_decls with
            | FStar_Pervasives_Native.Some (se_assm, se_refl) ->
                (let uu____7123 =
                   FStar_TypeChecker_Env.debug env2
                     (FStar_Options.Other "NativeTactics")
                 in
                 if uu____7123 then
                   let uu____7124 =
                     FStar_Syntax_Print.sigelt_to_string se_assm
                   in
                   let uu____7125 =
                     FStar_Syntax_Print.sigelt_to_string se_refl
                   in
                   FStar_Util.print2 "Native tactic declarations: \n%s\n%s\n"
                     uu____7124 uu____7125
                 else ()) ;
                ([se_assm; se_refl], [])
            | FStar_Pervasives_Native.None -> ([se1], [])


let for_export
    : FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
      -> ( FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_Ident.lident Prims.list )
         FStar_Pervasives_Native.tuple2 =
  fun hidden se ->
    let is_abstract quals =
      FStar_All.pipe_right quals
        (FStar_Util.for_some (fun uu___58_7176 ->
             match uu___58_7176 with
             | FStar_Syntax_Syntax.Abstract -> true
             | uu____7177 -> false ))
    in
    let is_hidden_proj_or_disc q =
      match q with
      | FStar_Syntax_Syntax.Projector (l, uu____7183) ->
          FStar_All.pipe_right hidden
            (FStar_Util.for_some (FStar_Ident.lid_equals l))
      | FStar_Syntax_Syntax.Discriminator l ->
          FStar_All.pipe_right hidden
            (FStar_Util.for_some (FStar_Ident.lid_equals l))
      | uu____7189 -> false
    in
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_pragma uu____7198 -> ([], hidden)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7203 ->
        failwith "Impossible (Already handled)"
    | FStar_Syntax_Syntax.Sig_datacon uu____7228 ->
        failwith "Impossible (Already handled)"
    | FStar_Syntax_Syntax.Sig_bundle (ses, uu____7252) ->
        let uu____7261 = is_abstract se.FStar_Syntax_Syntax.sigquals in
        if uu____7261 then
          let for_export_bundle se1 uu____7292 =
            match uu____7292 with out, hidden1 ->
              match se1.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (l, us, bs, t, uu____7331, uu____7332) ->
                  let dec =
                    let uu___92_7342 = se1 in
                    let uu____7343 =
                      let uu____7344 =
                        let uu____7351 =
                          let uu____7354 = FStar_Syntax_Syntax.mk_Total t in
                          FStar_Syntax_Util.arrow bs uu____7354
                        in
                        (l, us, uu____7351)
                      in
                      FStar_Syntax_Syntax.Sig_declare_typ uu____7344
                    in
                    { FStar_Syntax_Syntax.sigel= uu____7343
                    ; FStar_Syntax_Syntax.sigrng=
                        uu___92_7342.FStar_Syntax_Syntax.sigrng
                    ; FStar_Syntax_Syntax.sigquals=
                        FStar_Syntax_Syntax.Assumption
                        :: FStar_Syntax_Syntax.New
                        :: se1.FStar_Syntax_Syntax.sigquals
                    ; FStar_Syntax_Syntax.sigmeta=
                        uu___92_7342.FStar_Syntax_Syntax.sigmeta
                    ; FStar_Syntax_Syntax.sigattrs=
                        uu___92_7342.FStar_Syntax_Syntax.sigattrs }
                  in
                  (dec :: out, hidden1)
              | FStar_Syntax_Syntax.Sig_datacon
                  (l, us, t, uu____7366, uu____7367, uu____7368) ->
                  let dec =
                    let uu___93_7374 = se1 in
                    { FStar_Syntax_Syntax.sigel=
                        FStar_Syntax_Syntax.Sig_declare_typ (l, us, t)
                    ; FStar_Syntax_Syntax.sigrng=
                        uu___93_7374.FStar_Syntax_Syntax.sigrng
                    ; FStar_Syntax_Syntax.sigquals=
                        [FStar_Syntax_Syntax.Assumption]
                    ; FStar_Syntax_Syntax.sigmeta=
                        uu___93_7374.FStar_Syntax_Syntax.sigmeta
                    ; FStar_Syntax_Syntax.sigattrs=
                        uu___93_7374.FStar_Syntax_Syntax.sigattrs }
                  in
                  (dec :: out, l :: hidden1)
              | uu____7379 -> (out, hidden1)
          in
          FStar_List.fold_right for_export_bundle ses ([], hidden)
        else ([se], hidden)
    | FStar_Syntax_Syntax.Sig_assume (uu____7401, uu____7402, uu____7403) ->
        let uu____7404 = is_abstract se.FStar_Syntax_Syntax.sigquals in
        if uu____7404 then ([], hidden) else ([se], hidden)
    | FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) ->
        let uu____7425 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
        in
        if uu____7425 then
          ( [ (let uu___94_7441 = se in
               { FStar_Syntax_Syntax.sigel=
                   FStar_Syntax_Syntax.Sig_declare_typ (l, us, t)
               ; FStar_Syntax_Syntax.sigrng=
                   uu___94_7441.FStar_Syntax_Syntax.sigrng
               ; FStar_Syntax_Syntax.sigquals= [FStar_Syntax_Syntax.Assumption]
               ; FStar_Syntax_Syntax.sigmeta=
                   uu___94_7441.FStar_Syntax_Syntax.sigmeta
               ; FStar_Syntax_Syntax.sigattrs=
                   uu___94_7441.FStar_Syntax_Syntax.sigattrs }) ]
          , l :: hidden )
        else
          let uu____7443 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some (fun uu___59_7447 ->
                   match uu___59_7447 with
                   | FStar_Syntax_Syntax.Assumption -> true
                   | FStar_Syntax_Syntax.Projector uu____7448 -> true
                   | FStar_Syntax_Syntax.Discriminator uu____7453 -> true
                   | uu____7454 -> false ))
          in
          if uu____7443 then ([se], hidden) else ([], hidden)
    | FStar_Syntax_Syntax.Sig_main uu____7472 -> ([], hidden)
    | FStar_Syntax_Syntax.Sig_new_effect uu____7477 -> ([se], hidden)
    | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7482 -> ([se], hidden)
    | FStar_Syntax_Syntax.Sig_sub_effect uu____7487 -> ([se], hidden)
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7492 -> ([se], hidden)
    | FStar_Syntax_Syntax.Sig_let ((false, [lb]), uu____7510)
      when FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some is_hidden_proj_or_disc) ->
        let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
        let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v in
        let uu____7527 =
          FStar_All.pipe_right hidden
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
        in
        if uu____7527 then ([], hidden)
        else
          let dec =
            { FStar_Syntax_Syntax.sigel=
                FStar_Syntax_Syntax.Sig_declare_typ
                  ( fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
                  , lb.FStar_Syntax_Syntax.lbunivs
                  , lb.FStar_Syntax_Syntax.lbtyp )
            ; FStar_Syntax_Syntax.sigrng= FStar_Ident.range_of_lid lid
            ; FStar_Syntax_Syntax.sigquals= [FStar_Syntax_Syntax.Assumption]
            ; FStar_Syntax_Syntax.sigmeta= FStar_Syntax_Syntax.default_sigmeta
            ; FStar_Syntax_Syntax.sigattrs= [] }
          in
          ([dec], lid :: hidden)
    | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
        let uu____7558 = is_abstract se.FStar_Syntax_Syntax.sigquals in
        if uu____7558 then
          let uu____7567 =
            FStar_All.pipe_right
              (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map (fun lb ->
                   let uu___95_7580 = se in
                   let uu____7581 =
                     let uu____7582 =
                       let uu____7589 =
                         let uu____7590 =
                           let uu____7593 =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                           in
                           uu____7593.FStar_Syntax_Syntax.fv_name
                         in
                         uu____7590.FStar_Syntax_Syntax.v
                       in
                       ( uu____7589
                       , lb.FStar_Syntax_Syntax.lbunivs
                       , lb.FStar_Syntax_Syntax.lbtyp )
                     in
                     FStar_Syntax_Syntax.Sig_declare_typ uu____7582
                   in
                   { FStar_Syntax_Syntax.sigel= uu____7581
                   ; FStar_Syntax_Syntax.sigrng=
                       uu___95_7580.FStar_Syntax_Syntax.sigrng
                   ; FStar_Syntax_Syntax.sigquals=
                       FStar_Syntax_Syntax.Assumption
                       :: se.FStar_Syntax_Syntax.sigquals
                   ; FStar_Syntax_Syntax.sigmeta=
                       uu___95_7580.FStar_Syntax_Syntax.sigmeta
                   ; FStar_Syntax_Syntax.sigattrs=
                       uu___95_7580.FStar_Syntax_Syntax.sigattrs } ))
          in
          (uu____7567, hidden)
        else ([se], hidden)


let add_sigelt_to_env
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt
      -> FStar_TypeChecker_Env.env =
  fun env se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7613 ->
        failwith "add_sigelt_to_env: Impossible, bare data constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____7630 ->
        failwith "add_sigelt_to_env: Impossible, bare data constructor"
    | FStar_Syntax_Syntax.Sig_pragma
        FStar_Syntax_Syntax.ResetOptions uu____7645 ->
        let env1 =
          let uu____7649 = FStar_Options.using_facts_from () in
          FStar_TypeChecker_Env.set_proof_ns uu____7649 env
        in
        env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh () ;
        env1
    | FStar_Syntax_Syntax.Sig_pragma uu____7651 -> env
    | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7652 -> env
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let env1 = FStar_TypeChecker_Env.push_sigelt env se in
        FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
          (FStar_List.fold_left
             (fun env2 a ->
               let uu____7662 =
                 FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a
               in
               FStar_TypeChecker_Env.push_sigelt env2 uu____7662 )
             env1)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____7663, uu____7664, uu____7665)
      when FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some (fun uu___60_7669 ->
                  match uu___60_7669 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____7670 -> false )) ->
        env
    | FStar_Syntax_Syntax.Sig_let (uu____7671, uu____7672)
      when FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some (fun uu___60_7680 ->
                  match uu___60_7680 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____7681 -> false )) ->
        env
    | uu____7682 -> FStar_TypeChecker_Env.push_sigelt env se


let tc_decls
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt Prims.list
      -> ( FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_TypeChecker_Env.env )
         FStar_Pervasives_Native.tuple3 =
  fun env ses ->
    let rec process_one_decl uu____7742 se =
      match uu____7742 with ses1, exports, env1, hidden ->
        (let uu____7795 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
         if uu____7795 then
           let uu____7796 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n"
             uu____7796
         else ()) ;
        let uu____7798 = tc_decl env1 se in
        match uu____7798 with ses', ses_elaborated ->
          let ses'1 =
            FStar_All.pipe_right ses'
              (FStar_List.map (fun se1 ->
                   (let uu____7848 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "UF")
                    in
                    if uu____7848 then
                      let uu____7849 =
                        FStar_Syntax_Print.sigelt_to_string se1
                      in
                      FStar_Util.print1 "About to elim vars from %s" uu____7849
                    else ()) ;
                   FStar_TypeChecker_Normalize.elim_uvars env1 se1 ))
          in
          let ses_elaborated1 =
            FStar_All.pipe_right ses_elaborated
              (FStar_List.map (fun se1 ->
                   FStar_TypeChecker_Normalize.elim_uvars env1 se1 ))
          in
          FStar_TypeChecker_Env.promote_id_info env1 (fun t ->
              FStar_TypeChecker_Normalize.normalize
                [ FStar_TypeChecker_Normalize.AllowUnboundUniverses
                ; FStar_TypeChecker_Normalize.CheckNoUvars
                ; FStar_TypeChecker_Normalize.Beta
                ; FStar_TypeChecker_Normalize.NoDeltaSteps
                ; FStar_TypeChecker_Normalize.CompressUvars
                ; FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta
                ; FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Iota
                ; FStar_TypeChecker_Normalize.NoFullNorm ] env1 t ) ;
          let env2 =
            FStar_All.pipe_right ses'1
              (FStar_List.fold_left
                 (fun env2 se1 -> add_sigelt_to_env env2 se1)
                 env1)
          in
          FStar_Syntax_Unionfind.reset () ;
          (let uu____7872 =
             FStar_Options.log_types ()
             || FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug env2)
                  (FStar_Options.Other "LogTypes")
           in
           if uu____7872 then
             let uu____7873 =
               FStar_List.fold_left
                 (fun s se1 ->
                   let uu____7879 =
                     let uu____7880 =
                       FStar_Syntax_Print.sigelt_to_string se1
                     in
                     Prims.strcat uu____7880 "\n"
                   in
                   Prims.strcat s uu____7879 )
                 "" ses'1
             in
             FStar_Util.print1 "Checked: %s\n" uu____7873
           else ()) ;
          FStar_List.iter
            (fun se1 ->
              env2.FStar_TypeChecker_Env.solver
                .FStar_TypeChecker_Env.encode_sig env2 se1 )
            ses'1 ;
          let uu____7885 =
            let accum_exports_hidden uu____7915 se1 =
              match uu____7915 with exports1, hidden1 ->
                let uu____7943 = for_export hidden1 se1 in
                match uu____7943 with se_exported, hidden2 ->
                  (FStar_List.rev_append se_exported exports1, hidden2)
            in
            FStar_List.fold_left accum_exports_hidden (exports, hidden) ses'1
          in
          match uu____7885 with exports1, hidden1 ->
            let ses'2 =
              FStar_List.map
                (fun s ->
                  let uu___96_8022 = s in
                  { FStar_Syntax_Syntax.sigel=
                      uu___96_8022.FStar_Syntax_Syntax.sigel
                  ; FStar_Syntax_Syntax.sigrng=
                      uu___96_8022.FStar_Syntax_Syntax.sigrng
                  ; FStar_Syntax_Syntax.sigquals=
                      uu___96_8022.FStar_Syntax_Syntax.sigquals
                  ; FStar_Syntax_Syntax.sigmeta=
                      uu___96_8022.FStar_Syntax_Syntax.sigmeta
                  ; FStar_Syntax_Syntax.sigattrs=
                      se.FStar_Syntax_Syntax.sigattrs } )
                ses'1
            in
            ( (FStar_List.rev_append ses'2 ses1, exports1, env2, hidden1)
            , ses_elaborated1 )
    in
    let process_one_decl_timed acc se =
      let uu____8100 = acc in
      match uu____8100 with uu____8135, uu____8136, env1, uu____8138 ->
        let uu____8151 =
          FStar_Util.record_time (fun uu____8197 -> process_one_decl acc se)
        in
        match uu____8151 with r, ms_elapsed ->
          (let uu____8261 =
             FStar_TypeChecker_Env.debug env1
               (FStar_Options.Other "TCDeclTime")
           in
           if uu____8261 then
             let uu____8262 = FStar_Syntax_Print.sigelt_to_string_short se in
             let uu____8263 = FStar_Util.string_of_int ms_elapsed in
             FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____8262
               uu____8263
           else ()) ;
          r
    in
    let uu____8265 =
      FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
    in
    match uu____8265 with ses1, exports, env1, uu____8313 ->
      (FStar_List.rev_append ses1 [], FStar_List.rev_append exports [], env1)


let tc_partial_modul
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.bool
      -> ( FStar_Syntax_Syntax.modul
         , FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_TypeChecker_Env.env )
         FStar_Pervasives_Native.tuple3 =
  fun env modul push_before_typechecking ->
    let verify =
      FStar_Options.should_verify
        modul.FStar_Syntax_Syntax.name.FStar_Ident.str
    in
    let action = if verify then "Verifying" else "Lax-checking" in
    let label1 =
      if modul.FStar_Syntax_Syntax.is_interface then "interface"
      else "implementation"
    in
    (let uu____8353 = FStar_Options.debug_any () in
     if uu____8353 then
       FStar_Util.print3 "%s %s of %s\n" action label1
         modul.FStar_Syntax_Syntax.name.FStar_Ident.str
     else ()) ;
    let name =
      FStar_Util.format2 "%s %s"
        ( if modul.FStar_Syntax_Syntax.is_interface then "interface"
        else "module" )
        modul.FStar_Syntax_Syntax.name.FStar_Ident.str
    in
    let msg = Prims.strcat "Internals for " name in
    let env1 =
      let uu___97_8359 = env in
      { FStar_TypeChecker_Env.solver= uu___97_8359.FStar_TypeChecker_Env.solver
      ; FStar_TypeChecker_Env.range= uu___97_8359.FStar_TypeChecker_Env.range
      ; FStar_TypeChecker_Env.curmodule=
          uu___97_8359.FStar_TypeChecker_Env.curmodule
      ; FStar_TypeChecker_Env.gamma= uu___97_8359.FStar_TypeChecker_Env.gamma
      ; FStar_TypeChecker_Env.gamma_cache=
          uu___97_8359.FStar_TypeChecker_Env.gamma_cache
      ; FStar_TypeChecker_Env.modules=
          uu___97_8359.FStar_TypeChecker_Env.modules
      ; FStar_TypeChecker_Env.expected_typ=
          uu___97_8359.FStar_TypeChecker_Env.expected_typ
      ; FStar_TypeChecker_Env.sigtab= uu___97_8359.FStar_TypeChecker_Env.sigtab
      ; FStar_TypeChecker_Env.is_pattern=
          uu___97_8359.FStar_TypeChecker_Env.is_pattern
      ; FStar_TypeChecker_Env.instantiate_imp=
          uu___97_8359.FStar_TypeChecker_Env.instantiate_imp
      ; FStar_TypeChecker_Env.effects=
          uu___97_8359.FStar_TypeChecker_Env.effects
      ; FStar_TypeChecker_Env.generalize=
          uu___97_8359.FStar_TypeChecker_Env.generalize
      ; FStar_TypeChecker_Env.letrecs=
          uu___97_8359.FStar_TypeChecker_Env.letrecs
      ; FStar_TypeChecker_Env.top_level=
          uu___97_8359.FStar_TypeChecker_Env.top_level
      ; FStar_TypeChecker_Env.check_uvars=
          uu___97_8359.FStar_TypeChecker_Env.check_uvars
      ; FStar_TypeChecker_Env.use_eq= uu___97_8359.FStar_TypeChecker_Env.use_eq
      ; FStar_TypeChecker_Env.is_iface= modul.FStar_Syntax_Syntax.is_interface
      ; FStar_TypeChecker_Env.admit= Prims.op_Negation verify
      ; FStar_TypeChecker_Env.lax= uu___97_8359.FStar_TypeChecker_Env.lax
      ; FStar_TypeChecker_Env.lax_universes=
          uu___97_8359.FStar_TypeChecker_Env.lax_universes
      ; FStar_TypeChecker_Env.failhard=
          uu___97_8359.FStar_TypeChecker_Env.failhard
      ; FStar_TypeChecker_Env.nosynth=
          uu___97_8359.FStar_TypeChecker_Env.nosynth
      ; FStar_TypeChecker_Env.tc_term=
          uu___97_8359.FStar_TypeChecker_Env.tc_term
      ; FStar_TypeChecker_Env.type_of=
          uu___97_8359.FStar_TypeChecker_Env.type_of
      ; FStar_TypeChecker_Env.universe_of=
          uu___97_8359.FStar_TypeChecker_Env.universe_of
      ; FStar_TypeChecker_Env.check_type_of=
          uu___97_8359.FStar_TypeChecker_Env.check_type_of
      ; FStar_TypeChecker_Env.use_bv_sorts=
          uu___97_8359.FStar_TypeChecker_Env.use_bv_sorts
      ; FStar_TypeChecker_Env.qname_and_index=
          uu___97_8359.FStar_TypeChecker_Env.qname_and_index
      ; FStar_TypeChecker_Env.proof_ns=
          uu___97_8359.FStar_TypeChecker_Env.proof_ns
      ; FStar_TypeChecker_Env.synth= uu___97_8359.FStar_TypeChecker_Env.synth
      ; FStar_TypeChecker_Env.is_native_tactic=
          uu___97_8359.FStar_TypeChecker_Env.is_native_tactic
      ; FStar_TypeChecker_Env.identifier_info=
          uu___97_8359.FStar_TypeChecker_Env.identifier_info
      ; FStar_TypeChecker_Env.tc_hooks=
          uu___97_8359.FStar_TypeChecker_Env.tc_hooks
      ; FStar_TypeChecker_Env.dsenv= uu___97_8359.FStar_TypeChecker_Env.dsenv
      ; FStar_TypeChecker_Env.dep_graph=
          uu___97_8359.FStar_TypeChecker_Env.dep_graph }
    in
    if push_before_typechecking then
      env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg
    else () ;
    let env2 =
      FStar_TypeChecker_Env.set_current_module env1
        modul.FStar_Syntax_Syntax.name
    in
    let uu____8363 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
    match uu____8363 with ses, exports, env3 ->
      ( (let uu___98_8396 = modul in
         { FStar_Syntax_Syntax.name= uu___98_8396.FStar_Syntax_Syntax.name
         ; FStar_Syntax_Syntax.declarations= ses
         ; FStar_Syntax_Syntax.exports=
             uu___98_8396.FStar_Syntax_Syntax.exports
         ; FStar_Syntax_Syntax.is_interface=
             uu___98_8396.FStar_Syntax_Syntax.is_interface })
      , exports
      , env3 )


let tc_more_partial_modul
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul
      -> FStar_Syntax_Syntax.sigelt Prims.list
      -> ( FStar_Syntax_Syntax.modul
         , FStar_Syntax_Syntax.sigelt Prims.list
         , FStar_TypeChecker_Env.env )
         FStar_Pervasives_Native.tuple3 =
  fun env modul decls ->
    let uu____8418 = tc_decls env decls in
    match uu____8418 with ses, exports, env1 ->
      let modul1 =
        let uu___99_8449 = modul in
        { FStar_Syntax_Syntax.name= uu___99_8449.FStar_Syntax_Syntax.name
        ; FStar_Syntax_Syntax.declarations=
            FStar_List.append modul.FStar_Syntax_Syntax.declarations ses
        ; FStar_Syntax_Syntax.exports= uu___99_8449.FStar_Syntax_Syntax.exports
        ; FStar_Syntax_Syntax.is_interface=
            uu___99_8449.FStar_Syntax_Syntax.is_interface }
      in
      (modul1, exports, env1)


let check_exports
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul
      -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env modul exports ->
    let env1 =
      let uu___100_8466 = env in
      { FStar_TypeChecker_Env.solver= uu___100_8466.FStar_TypeChecker_Env.solver
      ; FStar_TypeChecker_Env.range= uu___100_8466.FStar_TypeChecker_Env.range
      ; FStar_TypeChecker_Env.curmodule=
          uu___100_8466.FStar_TypeChecker_Env.curmodule
      ; FStar_TypeChecker_Env.gamma= uu___100_8466.FStar_TypeChecker_Env.gamma
      ; FStar_TypeChecker_Env.gamma_cache=
          uu___100_8466.FStar_TypeChecker_Env.gamma_cache
      ; FStar_TypeChecker_Env.modules=
          uu___100_8466.FStar_TypeChecker_Env.modules
      ; FStar_TypeChecker_Env.expected_typ=
          uu___100_8466.FStar_TypeChecker_Env.expected_typ
      ; FStar_TypeChecker_Env.sigtab=
          uu___100_8466.FStar_TypeChecker_Env.sigtab
      ; FStar_TypeChecker_Env.is_pattern=
          uu___100_8466.FStar_TypeChecker_Env.is_pattern
      ; FStar_TypeChecker_Env.instantiate_imp=
          uu___100_8466.FStar_TypeChecker_Env.instantiate_imp
      ; FStar_TypeChecker_Env.effects=
          uu___100_8466.FStar_TypeChecker_Env.effects
      ; FStar_TypeChecker_Env.generalize=
          uu___100_8466.FStar_TypeChecker_Env.generalize
      ; FStar_TypeChecker_Env.letrecs=
          uu___100_8466.FStar_TypeChecker_Env.letrecs
      ; FStar_TypeChecker_Env.top_level= true
      ; FStar_TypeChecker_Env.check_uvars=
          uu___100_8466.FStar_TypeChecker_Env.check_uvars
      ; FStar_TypeChecker_Env.use_eq=
          uu___100_8466.FStar_TypeChecker_Env.use_eq
      ; FStar_TypeChecker_Env.is_iface=
          uu___100_8466.FStar_TypeChecker_Env.is_iface
      ; FStar_TypeChecker_Env.admit= uu___100_8466.FStar_TypeChecker_Env.admit
      ; FStar_TypeChecker_Env.lax= true
      ; FStar_TypeChecker_Env.lax_universes= true
      ; FStar_TypeChecker_Env.failhard=
          uu___100_8466.FStar_TypeChecker_Env.failhard
      ; FStar_TypeChecker_Env.nosynth=
          uu___100_8466.FStar_TypeChecker_Env.nosynth
      ; FStar_TypeChecker_Env.tc_term=
          uu___100_8466.FStar_TypeChecker_Env.tc_term
      ; FStar_TypeChecker_Env.type_of=
          uu___100_8466.FStar_TypeChecker_Env.type_of
      ; FStar_TypeChecker_Env.universe_of=
          uu___100_8466.FStar_TypeChecker_Env.universe_of
      ; FStar_TypeChecker_Env.check_type_of=
          uu___100_8466.FStar_TypeChecker_Env.check_type_of
      ; FStar_TypeChecker_Env.use_bv_sorts=
          uu___100_8466.FStar_TypeChecker_Env.use_bv_sorts
      ; FStar_TypeChecker_Env.qname_and_index=
          uu___100_8466.FStar_TypeChecker_Env.qname_and_index
      ; FStar_TypeChecker_Env.proof_ns=
          uu___100_8466.FStar_TypeChecker_Env.proof_ns
      ; FStar_TypeChecker_Env.synth= uu___100_8466.FStar_TypeChecker_Env.synth
      ; FStar_TypeChecker_Env.is_native_tactic=
          uu___100_8466.FStar_TypeChecker_Env.is_native_tactic
      ; FStar_TypeChecker_Env.identifier_info=
          uu___100_8466.FStar_TypeChecker_Env.identifier_info
      ; FStar_TypeChecker_Env.tc_hooks=
          uu___100_8466.FStar_TypeChecker_Env.tc_hooks
      ; FStar_TypeChecker_Env.dsenv= uu___100_8466.FStar_TypeChecker_Env.dsenv
      ; FStar_TypeChecker_Env.dep_graph=
          uu___100_8466.FStar_TypeChecker_Env.dep_graph }
    in
    let check_term1 lid univs1 t =
      let uu____8477 = FStar_Syntax_Subst.open_univ_vars univs1 t in
      match uu____8477 with univs2, t1 ->
        (let uu____8485 =
           let uu____8486 =
             let uu____8489 =
               FStar_TypeChecker_Env.set_current_module env1
                 modul.FStar_Syntax_Syntax.name
             in
             FStar_TypeChecker_Env.debug uu____8489
           in
           FStar_All.pipe_left uu____8486 (FStar_Options.Other "Exports")
         in
         if uu____8485 then
           let uu____8490 = FStar_Syntax_Print.lid_to_string lid in
           let uu____8491 =
             let uu____8492 =
               FStar_All.pipe_right univs2
                 (FStar_List.map (fun x ->
                      FStar_Syntax_Print.univ_to_string
                        (FStar_Syntax_Syntax.U_name x) ))
             in
             FStar_All.pipe_right uu____8492 (FStar_String.concat ", ")
           in
           let uu____8501 = FStar_Syntax_Print.term_to_string t1 in
           FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____8490
             uu____8491 uu____8501
         else ()) ;
        let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
        let uu____8504 = FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
        FStar_All.pipe_right uu____8504 FStar_Pervasives.ignore
    in
    let check_term2 lid univs1 t =
      (let uu____8528 =
         let uu____8529 =
           FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name
         in
         let uu____8530 = FStar_Syntax_Print.lid_to_string lid in
         FStar_Util.format2
           "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
           uu____8529 uu____8530
       in
       FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8528) ;
      check_term1 lid univs1 t ;
      FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()
    in
    let rec check_sigelt se =
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____8537) ->
          let uu____8546 =
            let uu____8547 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Private)
            in
            Prims.op_Negation uu____8547
          in
          if uu____8546 then
            FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
          else ()
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (l, univs1, binders, typ, uu____8557, uu____8558) ->
          let t =
            let uu____8570 =
              let uu____8573 =
                let uu____8574 =
                  let uu____8587 = FStar_Syntax_Syntax.mk_Total typ in
                  (binders, uu____8587)
                in
                FStar_Syntax_Syntax.Tm_arrow uu____8574
              in
              FStar_Syntax_Syntax.mk uu____8573
            in
            uu____8570 FStar_Pervasives_Native.None
              se.FStar_Syntax_Syntax.sigrng
          in
          check_term2 l univs1 t
      | FStar_Syntax_Syntax.Sig_datacon
          (l, univs1, t, uu____8594, uu____8595, uu____8596) ->
          check_term2 l univs1 t
      | FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) ->
          let uu____8604 =
            let uu____8605 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Private)
            in
            Prims.op_Negation uu____8605
          in
          if uu____8604 then check_term2 l univs1 t else ()
      | FStar_Syntax_Syntax.Sig_let ((uu____8609, lbs), uu____8611) ->
          let uu____8626 =
            let uu____8627 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Private)
            in
            Prims.op_Negation uu____8627
          in
          if uu____8626 then
            FStar_All.pipe_right lbs
              (FStar_List.iter (fun lb ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   check_term2
                     fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
                     lb.FStar_Syntax_Syntax.lbunivs
                     lb.FStar_Syntax_Syntax.lbtyp ))
          else ()
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags1) ->
          let uu____8646 =
            let uu____8647 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Private)
            in
            Prims.op_Negation uu____8647
          in
          if uu____8646 then
            let arrow1 =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
            in
            check_term2 l univs1 arrow1
          else ()
      | FStar_Syntax_Syntax.Sig_main uu____8654 -> ()
      | FStar_Syntax_Syntax.Sig_assume uu____8655 -> ()
      | FStar_Syntax_Syntax.Sig_new_effect uu____8662 -> ()
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8663 -> ()
      | FStar_Syntax_Syntax.Sig_sub_effect uu____8664 -> ()
      | FStar_Syntax_Syntax.Sig_pragma uu____8665 -> ()
    in
    if FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
         FStar_Parser_Const.prims_lid
    then ()
    else FStar_List.iter check_sigelt exports


let finish_partial_modul
    : Prims.bool -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul
      -> FStar_Syntax_Syntax.sigelts
      -> ( FStar_Syntax_Syntax.modul
         , FStar_TypeChecker_Env.env )
         FStar_Pervasives_Native.tuple2 =
  fun must_check_exports env modul exports ->
    let modul1 =
      let uu___101_8684 = modul in
      { FStar_Syntax_Syntax.name= uu___101_8684.FStar_Syntax_Syntax.name
      ; FStar_Syntax_Syntax.declarations=
          uu___101_8684.FStar_Syntax_Syntax.declarations
      ; FStar_Syntax_Syntax.exports
      ; FStar_Syntax_Syntax.is_interface=
          modul.FStar_Syntax_Syntax.is_interface }
    in
    let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
    (let uu____8687 =
       (let uu____8690 = FStar_Options.lax () in
        Prims.op_Negation uu____8690)
       && must_check_exports
     in
     if uu____8687 then check_exports env1 modul1 exports else ()) ;
    env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop
      (Prims.strcat "Ending modul "
         modul1.FStar_Syntax_Syntax.name.FStar_Ident.str) ;
    env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env1
      modul1 ;
    env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh () ;
    (let uu____8696 =
       let uu____8697 = FStar_Options.interactive () in
       Prims.op_Negation uu____8697
     in
     if uu____8696 then
       let uu____8698 = FStar_Options.restore_cmd_line_options true in
       FStar_All.pipe_right uu____8698 FStar_Pervasives.ignore
     else ()) ;
    (modul1, env1)


let load_checked_module
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul
      -> FStar_TypeChecker_Env.env =
  fun env modul ->
    let env1 =
      FStar_TypeChecker_Env.set_current_module env
        modul.FStar_Syntax_Syntax.name
    in
    (let uu____8708 =
       let uu____8709 =
         FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name
       in
       Prims.strcat "Internals for " uu____8709
     in
     env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push uu____8708) ;
    let env2 =
      FStar_List.fold_left
        (fun env2 se ->
          let env3 = FStar_TypeChecker_Env.push_sigelt env2 se in
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          FStar_All.pipe_right lids
            (FStar_List.iter (fun lid ->
                 let uu____8728 =
                   FStar_TypeChecker_Env.try_lookup_lid env3 lid
                 in
                 () )) ;
          env3 )
        env1 modul.FStar_Syntax_Syntax.declarations
    in
    let uu____8749 =
      finish_partial_modul false env2 modul modul.FStar_Syntax_Syntax.exports
    in
    FStar_Pervasives_Native.snd uu____8749


let tc_modul
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul
      -> ( FStar_Syntax_Syntax.modul
         , FStar_TypeChecker_Env.env )
         FStar_Pervasives_Native.tuple2 =
  fun env modul ->
    let uu____8764 = tc_partial_modul env modul true in
    match uu____8764 with modul1, non_private_decls, env1 ->
      finish_partial_modul true env1 modul1 non_private_decls


let check_module
    : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul
      -> ( FStar_Syntax_Syntax.modul
         , FStar_TypeChecker_Env.env )
         FStar_Pervasives_Native.tuple2 =
  fun env m ->
    (let uu____8795 = FStar_Options.debug_any () in
     if uu____8795 then
       let uu____8796 =
         FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
       in
       FStar_Util.print2 "Checking %s: %s\n"
         (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
         uu____8796
     else ()) ;
    let env1 =
      let uu___102_8800 = env in
      let uu____8801 =
        let uu____8802 =
          FStar_Options.should_verify
            m.FStar_Syntax_Syntax.name.FStar_Ident.str
        in
        Prims.op_Negation uu____8802
      in
      { FStar_TypeChecker_Env.solver= uu___102_8800.FStar_TypeChecker_Env.solver
      ; FStar_TypeChecker_Env.range= uu___102_8800.FStar_TypeChecker_Env.range
      ; FStar_TypeChecker_Env.curmodule=
          uu___102_8800.FStar_TypeChecker_Env.curmodule
      ; FStar_TypeChecker_Env.gamma= uu___102_8800.FStar_TypeChecker_Env.gamma
      ; FStar_TypeChecker_Env.gamma_cache=
          uu___102_8800.FStar_TypeChecker_Env.gamma_cache
      ; FStar_TypeChecker_Env.modules=
          uu___102_8800.FStar_TypeChecker_Env.modules
      ; FStar_TypeChecker_Env.expected_typ=
          uu___102_8800.FStar_TypeChecker_Env.expected_typ
      ; FStar_TypeChecker_Env.sigtab=
          uu___102_8800.FStar_TypeChecker_Env.sigtab
      ; FStar_TypeChecker_Env.is_pattern=
          uu___102_8800.FStar_TypeChecker_Env.is_pattern
      ; FStar_TypeChecker_Env.instantiate_imp=
          uu___102_8800.FStar_TypeChecker_Env.instantiate_imp
      ; FStar_TypeChecker_Env.effects=
          uu___102_8800.FStar_TypeChecker_Env.effects
      ; FStar_TypeChecker_Env.generalize=
          uu___102_8800.FStar_TypeChecker_Env.generalize
      ; FStar_TypeChecker_Env.letrecs=
          uu___102_8800.FStar_TypeChecker_Env.letrecs
      ; FStar_TypeChecker_Env.top_level=
          uu___102_8800.FStar_TypeChecker_Env.top_level
      ; FStar_TypeChecker_Env.check_uvars=
          uu___102_8800.FStar_TypeChecker_Env.check_uvars
      ; FStar_TypeChecker_Env.use_eq=
          uu___102_8800.FStar_TypeChecker_Env.use_eq
      ; FStar_TypeChecker_Env.is_iface=
          uu___102_8800.FStar_TypeChecker_Env.is_iface
      ; FStar_TypeChecker_Env.admit= uu___102_8800.FStar_TypeChecker_Env.admit
      ; FStar_TypeChecker_Env.lax= uu____8801
      ; FStar_TypeChecker_Env.lax_universes=
          uu___102_8800.FStar_TypeChecker_Env.lax_universes
      ; FStar_TypeChecker_Env.failhard=
          uu___102_8800.FStar_TypeChecker_Env.failhard
      ; FStar_TypeChecker_Env.nosynth=
          uu___102_8800.FStar_TypeChecker_Env.nosynth
      ; FStar_TypeChecker_Env.tc_term=
          uu___102_8800.FStar_TypeChecker_Env.tc_term
      ; FStar_TypeChecker_Env.type_of=
          uu___102_8800.FStar_TypeChecker_Env.type_of
      ; FStar_TypeChecker_Env.universe_of=
          uu___102_8800.FStar_TypeChecker_Env.universe_of
      ; FStar_TypeChecker_Env.check_type_of=
          uu___102_8800.FStar_TypeChecker_Env.check_type_of
      ; FStar_TypeChecker_Env.use_bv_sorts=
          uu___102_8800.FStar_TypeChecker_Env.use_bv_sorts
      ; FStar_TypeChecker_Env.qname_and_index=
          uu___102_8800.FStar_TypeChecker_Env.qname_and_index
      ; FStar_TypeChecker_Env.proof_ns=
          uu___102_8800.FStar_TypeChecker_Env.proof_ns
      ; FStar_TypeChecker_Env.synth= uu___102_8800.FStar_TypeChecker_Env.synth
      ; FStar_TypeChecker_Env.is_native_tactic=
          uu___102_8800.FStar_TypeChecker_Env.is_native_tactic
      ; FStar_TypeChecker_Env.identifier_info=
          uu___102_8800.FStar_TypeChecker_Env.identifier_info
      ; FStar_TypeChecker_Env.tc_hooks=
          uu___102_8800.FStar_TypeChecker_Env.tc_hooks
      ; FStar_TypeChecker_Env.dsenv= uu___102_8800.FStar_TypeChecker_Env.dsenv
      ; FStar_TypeChecker_Env.dep_graph=
          uu___102_8800.FStar_TypeChecker_Env.dep_graph }
    in
    let uu____8803 = tc_modul env1 m in
    match uu____8803 with m1, env2 ->
      (let uu____8815 =
         FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str
       in
       if uu____8815 then
         let uu____8816 = FStar_Syntax_Print.modul_to_string m1 in
         FStar_Util.print1 "%s\n" uu____8816
       else ()) ;
      (let uu____8819 =
         FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str
         && FStar_Options.debug_at_level
              m1.FStar_Syntax_Syntax.name.FStar_Ident.str
              (FStar_Options.Other "Normalize")
       in
       if uu____8819 then
         let normalize_toplevel_lets se =
           match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_let ((b, lbs), ids) ->
               let n1 =
                 FStar_TypeChecker_Normalize.normalize
                   [ FStar_TypeChecker_Normalize.Beta
                   ; FStar_TypeChecker_Normalize.Eager_unfolding
                   ; FStar_TypeChecker_Normalize.Reify
                   ; FStar_TypeChecker_Normalize.Inlining
                   ; FStar_TypeChecker_Normalize.Primops
                   ; FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant
                   ; FStar_TypeChecker_Normalize.AllowUnboundUniverses ]
               in
               let update lb =
                 let uu____8850 =
                   FStar_Syntax_Subst.open_univ_vars
                     lb.FStar_Syntax_Syntax.lbunivs
                     lb.FStar_Syntax_Syntax.lbdef
                 in
                 match uu____8850 with univnames1, e ->
                   let uu___103_8857 = lb in
                   let uu____8858 =
                     let uu____8861 =
                       FStar_TypeChecker_Env.push_univ_vars env2 univnames1
                     in
                     n1 uu____8861 e
                   in
                   { FStar_Syntax_Syntax.lbname=
                       uu___103_8857.FStar_Syntax_Syntax.lbname
                   ; FStar_Syntax_Syntax.lbunivs=
                       uu___103_8857.FStar_Syntax_Syntax.lbunivs
                   ; FStar_Syntax_Syntax.lbtyp=
                       uu___103_8857.FStar_Syntax_Syntax.lbtyp
                   ; FStar_Syntax_Syntax.lbeff=
                       uu___103_8857.FStar_Syntax_Syntax.lbeff
                   ; FStar_Syntax_Syntax.lbdef= uu____8858
                   ; FStar_Syntax_Syntax.lbattrs=
                       uu___103_8857.FStar_Syntax_Syntax.lbattrs }
               in
               let uu___104_8862 = se in
               let uu____8863 =
                 let uu____8864 =
                   let uu____8871 =
                     let uu____8878 = FStar_List.map update lbs in
                     (b, uu____8878)
                   in
                   (uu____8871, ids)
                 in
                 FStar_Syntax_Syntax.Sig_let uu____8864
               in
               { FStar_Syntax_Syntax.sigel= uu____8863
               ; FStar_Syntax_Syntax.sigrng=
                   uu___104_8862.FStar_Syntax_Syntax.sigrng
               ; FStar_Syntax_Syntax.sigquals=
                   uu___104_8862.FStar_Syntax_Syntax.sigquals
               ; FStar_Syntax_Syntax.sigmeta=
                   uu___104_8862.FStar_Syntax_Syntax.sigmeta
               ; FStar_Syntax_Syntax.sigattrs=
                   uu___104_8862.FStar_Syntax_Syntax.sigattrs }
           | uu____8891 -> se
         in
         let normalized_module =
           let uu___105_8893 = m1 in
           let uu____8894 =
             FStar_List.map normalize_toplevel_lets
               m1.FStar_Syntax_Syntax.declarations
           in
           { FStar_Syntax_Syntax.name= uu___105_8893.FStar_Syntax_Syntax.name
           ; FStar_Syntax_Syntax.declarations= uu____8894
           ; FStar_Syntax_Syntax.exports=
               uu___105_8893.FStar_Syntax_Syntax.exports
           ; FStar_Syntax_Syntax.is_interface=
               uu___105_8893.FStar_Syntax_Syntax.is_interface }
         in
         let uu____8895 =
           FStar_Syntax_Print.modul_to_string normalized_module
         in
         FStar_Util.print1 "%s\n" uu____8895
       else ()) ;
      (m1, env2)
