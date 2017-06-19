open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____9 = FStar_Options.reuse_hint_for () in
      match uu____9 with
      | Some l ->
          let lid =
            let uu____13 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____13 l in
          let uu___120_14 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___120_14.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___120_14.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___120_14.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___120_14.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___120_14.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___120_14.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___120_14.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___120_14.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___120_14.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___120_14.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___120_14.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___120_14.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___120_14.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___120_14.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___120_14.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___120_14.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___120_14.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___120_14.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___120_14.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___120_14.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___120_14.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___120_14.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___120_14.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___120_14.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___120_14.FStar_TypeChecker_Env.synth)
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____20 = FStar_TypeChecker_Env.current_module env in
                let uu____21 =
                  let uu____22 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____22 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____20 uu____21
            | l::uu____24 -> l in
          let uu___121_26 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___121_26.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___121_26.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___121_26.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___121_26.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___121_26.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___121_26.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___121_26.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___121_26.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___121_26.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___121_26.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___121_26.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___121_26.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___121_26.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___121_26.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___121_26.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___121_26.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___121_26.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___121_26.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___121_26.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___121_26.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___121_26.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___121_26.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___121_26.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___121_26.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___121_26.FStar_TypeChecker_Env.synth)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____33 =
         let uu____34 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____34 in
       Prims.op_Negation uu____33)
let is_native_tactic:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun tac_lid  ->
    fun h  ->
      match h.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_uinst (h',uu____44) ->
          let uu____49 =
            let uu____50 = FStar_Syntax_Subst.compress h' in
            uu____50.FStar_Syntax_Syntax.n in
          (match uu____49 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.tactic_lid
               -> FStar_Tactics_Native.is_native_tactic tac_lid
           | uu____54 -> false)
      | uu____55 -> false
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____68 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____68 with
        | (t1,c,g) ->
            (FStar_ST.write t1.FStar_Syntax_Syntax.tk
               (Some ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____93 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____93
         then
           let uu____94 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____94
         else ());
        (let uu____96 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____96 with
         | (t',uu____101,uu____102) ->
             ((let uu____104 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____104
               then
                 let uu____105 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____105
               else ());
              t))
let check_and_gen:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____119 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____119
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____145 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____145)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv*
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail4 uu____170 =
          let uu____171 =
            let uu____172 =
              let uu____175 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____175, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____172 in
          raise uu____171 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____203)::(wp,uu____205)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____214 -> fail4 ())
        | uu____215 -> fail4 ()
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____277 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____277 with
      | (effect_params_un,signature_un,opening) ->
          let uu____284 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____284 with
           | (effect_params,env,uu____290) ->
               let uu____291 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____291 with
                | (signature,uu____295) ->
                    let ed1 =
                      let uu___122_297 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___122_297.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___122_297.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___122_297.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___122_297.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___122_297.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___122_297.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___122_297.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___122_297.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___122_297.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___122_297.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___122_297.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___122_297.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___122_297.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___122_297.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___122_297.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___122_297.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___122_297.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____301 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
                          let uu___123_319 = ed1 in
                          let uu____320 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____321 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____322 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____323 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____324 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____325 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____326 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____327 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____328 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____329 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____330 =
                            let uu____331 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____331 in
                          let uu____337 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____338 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____339 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___124_342 = a in
                                 let uu____343 =
                                   let uu____344 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____344 in
                                 let uu____350 =
                                   let uu____351 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____351 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___124_342.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___124_342.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___124_342.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___124_342.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____343;
                                   FStar_Syntax_Syntax.action_typ = uu____350
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___123_319.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___123_319.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___123_319.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___123_319.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___123_319.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____320;
                            FStar_Syntax_Syntax.bind_wp = uu____321;
                            FStar_Syntax_Syntax.if_then_else = uu____322;
                            FStar_Syntax_Syntax.ite_wp = uu____323;
                            FStar_Syntax_Syntax.stronger = uu____324;
                            FStar_Syntax_Syntax.close_wp = uu____325;
                            FStar_Syntax_Syntax.assert_p = uu____326;
                            FStar_Syntax_Syntax.assume_p = uu____327;
                            FStar_Syntax_Syntax.null_wp = uu____328;
                            FStar_Syntax_Syntax.trivial = uu____329;
                            FStar_Syntax_Syntax.repr = uu____330;
                            FStar_Syntax_Syntax.return_repr = uu____337;
                            FStar_Syntax_Syntax.bind_repr = uu____338;
                            FStar_Syntax_Syntax.actions = uu____339
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail4 t =
                        let uu____379 =
                          let uu____380 =
                            let uu____383 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____383, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____380 in
                        raise uu____379 in
                      let uu____388 =
                        let uu____389 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____389.FStar_Syntax_Syntax.n in
                      match uu____388 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____414)::(wp,uu____416)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____425 -> fail4 signature1)
                      | uu____426 -> fail4 signature1 in
                    let uu____427 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____427 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____445 =
                           let uu____446 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____446 with
                           | (signature1,uu____454) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____456 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____456 in
                         ((let uu____458 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____458
                           then
                             let uu____459 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____460 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____461 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____462 =
                               let uu____463 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____463 in
                             let uu____464 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____459 uu____460 uu____461 uu____462
                               uu____464
                           else ());
                          (let check_and_gen' env2 uu____477 k =
                             match uu____477 with
                             | (uu____482,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____490 =
                                 let uu____494 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____495 =
                                   let uu____497 =
                                     let uu____498 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____498 in
                                   [uu____497] in
                                 uu____494 :: uu____495 in
                               let uu____499 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____490 uu____499 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____503 = fresh_effect_signature () in
                             match uu____503 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____517 =
                                     let uu____521 =
                                       let uu____522 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____522 in
                                     [uu____521] in
                                   let uu____523 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____517
                                     uu____523 in
                                 let expected_k =
                                   let uu____529 =
                                     let uu____533 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____534 =
                                       let uu____536 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____537 =
                                         let uu____539 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____540 =
                                           let uu____542 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____543 =
                                             let uu____545 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____545] in
                                           uu____542 :: uu____543 in
                                         uu____539 :: uu____540 in
                                       uu____536 :: uu____537 in
                                     uu____533 :: uu____534 in
                                   let uu____546 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____529
                                     uu____546 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____551 =
                                 let uu____552 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____552
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____551 in
                             let expected_k =
                               let uu____560 =
                                 let uu____564 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____565 =
                                   let uu____567 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____568 =
                                     let uu____570 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____571 =
                                       let uu____573 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____573] in
                                     uu____570 :: uu____571 in
                                   uu____567 :: uu____568 in
                                 uu____564 :: uu____565 in
                               let uu____574 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____560 uu____574 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____581 =
                                 let uu____585 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____586 =
                                   let uu____588 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____588] in
                                 uu____585 :: uu____586 in
                               let uu____589 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____581 uu____589 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____593 = FStar_Syntax_Util.type_u () in
                             match uu____593 with
                             | (t,uu____597) ->
                                 let expected_k =
                                   let uu____601 =
                                     let uu____605 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____606 =
                                       let uu____608 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____609 =
                                         let uu____611 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____611] in
                                       uu____608 :: uu____609 in
                                     uu____605 :: uu____606 in
                                   let uu____612 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____601
                                     uu____612 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____617 =
                                 let uu____618 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____618
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____617 in
                             let b_wp_a =
                               let uu____626 =
                                 let uu____630 =
                                   let uu____631 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____631 in
                                 [uu____630] in
                               let uu____632 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____626 uu____632 in
                             let expected_k =
                               let uu____638 =
                                 let uu____642 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____643 =
                                   let uu____645 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____646 =
                                     let uu____648 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____648] in
                                   uu____645 :: uu____646 in
                                 uu____642 :: uu____643 in
                               let uu____649 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____638 uu____649 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____656 =
                                 let uu____660 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____661 =
                                   let uu____663 =
                                     let uu____664 =
                                       let uu____665 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____665
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____664 in
                                   let uu____670 =
                                     let uu____672 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____672] in
                                   uu____663 :: uu____670 in
                                 uu____660 :: uu____661 in
                               let uu____673 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____656 uu____673 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____680 =
                                 let uu____684 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____685 =
                                   let uu____687 =
                                     let uu____688 =
                                       let uu____689 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____689
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____688 in
                                   let uu____694 =
                                     let uu____696 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____696] in
                                   uu____687 :: uu____694 in
                                 uu____684 :: uu____685 in
                               let uu____697 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____680 uu____697 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____704 =
                                 let uu____708 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____708] in
                               let uu____709 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____704 uu____709 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____713 = FStar_Syntax_Util.type_u () in
                             match uu____713 with
                             | (t,uu____717) ->
                                 let expected_k =
                                   let uu____721 =
                                     let uu____725 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____726 =
                                       let uu____728 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____728] in
                                     uu____725 :: uu____726 in
                                   let uu____729 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____721
                                     uu____729 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____732 =
                             let uu____738 =
                               let uu____739 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____739.FStar_Syntax_Syntax.n in
                             match uu____738 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____748 ->
                                 let repr =
                                   let uu____750 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____750 with
                                   | (t,uu____754) ->
                                       let expected_k =
                                         let uu____758 =
                                           let uu____762 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____763 =
                                             let uu____765 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____765] in
                                           uu____762 :: uu____763 in
                                         let uu____766 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____758
                                           uu____766 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____779 =
                                     let uu____782 =
                                       let uu____783 =
                                         let uu____793 =
                                           let uu____795 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____796 =
                                             let uu____798 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____798] in
                                           uu____795 :: uu____796 in
                                         (repr1, uu____793) in
                                       FStar_Syntax_Syntax.Tm_app uu____783 in
                                     FStar_Syntax_Syntax.mk uu____782 in
                                   uu____779 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____817 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____817 wp in
                                 let destruct_repr t =
                                   let uu____828 =
                                     let uu____829 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____829.FStar_Syntax_Syntax.n in
                                   match uu____828 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____838,(t1,uu____840)::(wp,uu____842)::[])
                                       -> (t1, wp)
                                   | uu____876 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____885 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____885
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____886 = fresh_effect_signature () in
                                   match uu____886 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____900 =
                                           let uu____904 =
                                             let uu____905 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____905 in
                                           [uu____904] in
                                         let uu____906 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____900
                                           uu____906 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____912 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____912 in
                                       let wp_g_x =
                                         let uu____916 =
                                           let uu____917 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____918 =
                                             let uu____919 =
                                               let uu____920 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____920 in
                                             [uu____919] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____917 uu____918 in
                                         uu____916 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____931 =
                                             let uu____932 =
                                               let uu____933 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____933
                                                 FStar_Pervasives.snd in
                                             let uu____938 =
                                               let uu____939 =
                                                 let uu____941 =
                                                   let uu____943 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____944 =
                                                     let uu____946 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____947 =
                                                       let uu____949 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____950 =
                                                         let uu____952 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____952] in
                                                       uu____949 :: uu____950 in
                                                     uu____946 :: uu____947 in
                                                   uu____943 :: uu____944 in
                                                 r :: uu____941 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____939 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____932 uu____938 in
                                           uu____931 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____960 =
                                           let uu____964 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____965 =
                                             let uu____967 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____968 =
                                               let uu____970 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____971 =
                                                 let uu____973 =
                                                   let uu____974 =
                                                     let uu____975 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____975 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____974 in
                                                 let uu____976 =
                                                   let uu____978 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____979 =
                                                     let uu____981 =
                                                       let uu____982 =
                                                         let uu____983 =
                                                           let uu____987 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____987] in
                                                         let uu____988 =
                                                           let uu____991 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____991 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____983
                                                           uu____988 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____982 in
                                                     [uu____981] in
                                                   uu____978 :: uu____979 in
                                                 uu____973 :: uu____976 in
                                               uu____970 :: uu____971 in
                                             uu____967 :: uu____968 in
                                           uu____964 :: uu____965 in
                                         let uu____992 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____960
                                           uu____992 in
                                       let uu____995 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____995 with
                                        | (expected_k1,uu____1000,uu____1001)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___125_1005 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___125_1005.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___125_1005.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___125_1005.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___125_1005.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___125_1005.FStar_TypeChecker_Env.synth)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1012 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____1012 in
                                   let res =
                                     let wp =
                                       let uu____1019 =
                                         let uu____1020 =
                                           let uu____1021 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1021
                                             FStar_Pervasives.snd in
                                         let uu____1026 =
                                           let uu____1027 =
                                             let uu____1029 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1030 =
                                               let uu____1032 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1032] in
                                             uu____1029 :: uu____1030 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1027 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1020 uu____1026 in
                                       uu____1019 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1040 =
                                       let uu____1044 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1045 =
                                         let uu____1047 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1047] in
                                       uu____1044 :: uu____1045 in
                                     let uu____1048 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1040
                                       uu____1048 in
                                   let uu____1051 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1051 with
                                   | (expected_k1,uu____1059,uu____1060) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1063 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1063 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1075 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1089 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1089 with
                                     | (act_typ,uu____1094,g_t) ->
                                         let env' =
                                           let uu___126_1097 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___126_1097.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___126_1097.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___126_1097.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___126_1097.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___126_1097.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___126_1097.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___126_1097.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___126_1097.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___126_1097.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___126_1097.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___126_1097.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___126_1097.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___126_1097.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___126_1097.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___126_1097.FStar_TypeChecker_Env.synth)
                                           } in
                                         ((let uu____1099 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1099
                                           then
                                             let uu____1100 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1101 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1100 uu____1101
                                           else ());
                                          (let uu____1103 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1103 with
                                           | (act_defn,uu____1108,g_a) ->
                                               let act_defn1 =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant]
                                                   env1 act_defn in
                                               let act_typ1 =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant;
                                                   FStar_TypeChecker_Normalize.Eager_unfolding;
                                                   FStar_TypeChecker_Normalize.Beta]
                                                   env1 act_typ in
                                               let uu____1112 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1130 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1130 with
                                                      | (bs1,uu____1136) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1143 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1143 in
                                                          let uu____1146 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1146
                                                           with
                                                           | (k1,uu____1153,g)
                                                               -> (k1, g)))
                                                 | uu____1155 ->
                                                     let uu____1156 =
                                                       let uu____1157 =
                                                         let uu____1160 =
                                                           let uu____1161 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1162 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1161
                                                             uu____1162 in
                                                         (uu____1160,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1157 in
                                                     raise uu____1156 in
                                               (match uu____1112 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1169 =
                                                        let uu____1170 =
                                                          let uu____1171 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1171 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1170 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1169);
                                                     (let act_typ2 =
                                                        let uu____1175 =
                                                          let uu____1176 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1176.FStar_Syntax_Syntax.n in
                                                        match uu____1175 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1193 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1193
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1200
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1200
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1220
                                                                    =
                                                                    let uu____1221
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1221] in
                                                                    let uu____1222
                                                                    =
                                                                    let uu____1228
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1228] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1220;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1222;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1229
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1229))
                                                        | uu____1232 ->
                                                            failwith "" in
                                                      let uu____1235 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1235 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___127_1241 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___127_1241.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___127_1241.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___127_1241.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____732 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1257 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1257 in
                               let uu____1260 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1260 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1266 =
                                        let uu____1269 =
                                          let uu____1270 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1270.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1269) in
                                      match uu____1266 with
                                      | ([],uu____1273) -> t1
                                      | (uu____1279,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1280,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1292 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1303 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1303 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1309 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1310 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1310))
                                           && (m <> n1) in
                                       if uu____1309
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1324 =
                                           let uu____1325 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1326 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1325 uu____1326 in
                                         failwith uu____1324
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1332 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1332 with
                                      | (univs2,defn) ->
                                          let uu____1337 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1337 with
                                           | (univs',typ) ->
                                               let uu___128_1343 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___128_1343.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___128_1343.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___128_1343.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___129_1346 = ed2 in
                                      let uu____1347 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1348 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1349 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1350 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1351 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1352 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1353 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1354 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1355 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1356 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1357 =
                                        let uu____1358 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1358 in
                                      let uu____1364 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1365 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1366 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___129_1346.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___129_1346.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1347;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1348;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1349;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1350;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1351;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1352;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1353;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1354;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1355;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1356;
                                        FStar_Syntax_Syntax.repr = uu____1357;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1364;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1365;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1366
                                      } in
                                    ((let uu____1369 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1369
                                      then
                                        let uu____1370 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1370
                                      else ());
                                     ed3)))))))
and cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.eff_decl*
        FStar_Syntax_Syntax.sigelt option)
  =
  fun env  ->
    fun ed  ->
      let uu____1374 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1374 with
      | (effect_binders_un,signature_un) ->
          let uu____1384 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1384 with
           | (effect_binders,env1,uu____1395) ->
               let uu____1396 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1396 with
                | (signature,uu____1405) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1414  ->
                           match uu____1414 with
                           | (bv,qual) ->
                               let uu____1421 =
                                 let uu___130_1422 = bv in
                                 let uu____1423 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___130_1422.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___130_1422.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1423
                                 } in
                               (uu____1421, qual)) effect_binders in
                    let uu____1426 =
                      let uu____1431 =
                        let uu____1432 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1432.FStar_Syntax_Syntax.n in
                      match uu____1431 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1440)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1455 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1426 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1472 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1472
                           then
                             let uu____1473 =
                               let uu____1475 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1475 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1473
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1499 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1499 with
                           | (t2,comp,uu____1507) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1518 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1518 with
                          | (repr,_comp) ->
                              ((let uu____1531 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1531
                                then
                                  let uu____1532 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1532
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type1 = recheck_debug "*" env1 wp_type in
                                let wp_a =
                                  let uu____1538 =
                                    let uu____1539 =
                                      let uu____1540 =
                                        let uu____1550 =
                                          let uu____1554 =
                                            let uu____1557 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1558 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1557, uu____1558) in
                                          [uu____1554] in
                                        (wp_type1, uu____1550) in
                                      FStar_Syntax_Syntax.Tm_app uu____1540 in
                                    mk1 uu____1539 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1538 in
                                let effect_signature =
                                  let binders =
                                    let uu____1573 =
                                      let uu____1576 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1576) in
                                    let uu____1577 =
                                      let uu____1581 =
                                        let uu____1582 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1582
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1581] in
                                    uu____1573 :: uu____1577 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let effect_signature1 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1 in
                                  let uu____1625 = item in
                                  match uu____1625 with
                                  | (u_item,item1) ->
                                      let uu____1637 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1637 with
                                       | (item2,item_comp) ->
                                           ((let uu____1647 =
                                               let uu____1648 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1648 in
                                             if uu____1647
                                             then
                                               let uu____1649 =
                                                 let uu____1650 =
                                                   let uu____1651 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1652 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1651 uu____1652 in
                                                 FStar_Errors.Err uu____1650 in
                                               raise uu____1649
                                             else ());
                                            (let uu____1654 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1654 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1667 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1667 with
                                | (dmff_env1,uu____1680,bind_wp,bind_elab) ->
                                    let uu____1683 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1683 with
                                     | (dmff_env2,uu____1696,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1700 =
                                             let uu____1701 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1701.FStar_Syntax_Syntax.n in
                                           match uu____1700 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1739 =
                                                 let uu____1747 =
                                                   let uu____1750 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1750 in
                                                 match uu____1747 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1789 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1739 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1811 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1811 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1822 =
                                                          let uu____1823 =
                                                            let uu____1833 =
                                                              let uu____1837
                                                                =
                                                                let uu____1840
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1841
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1840,
                                                                  uu____1841) in
                                                              [uu____1837] in
                                                            (wp_type1,
                                                              uu____1833) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1823 in
                                                        mk1 uu____1822 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1849 =
                                                      let uu____1859 =
                                                        let uu____1860 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1860 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1859 in
                                                    (match uu____1849 with
                                                     | (bs1,body2,what') ->
                                                         let fail4 uu____1888
                                                           =
                                                           let error_msg =
                                                             let uu____1890 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1891 =
                                                               match what'
                                                               with
                                                               | None  ->
                                                                   "None"
                                                               | Some
                                                                   (FStar_Util.Inl
                                                                   lc) ->
                                                                   FStar_Syntax_Print.lcomp_to_string
                                                                    lc
                                                               | Some
                                                                   (FStar_Util.Inr
                                                                   (lid,uu____1907))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1890
                                                               uu____1891 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  ->
                                                               fail4 ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1933
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1933
                                                               then
                                                                 let g_opt =
                                                                   FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    lc.FStar_Syntax_Syntax.res_typ
                                                                    FStar_Syntax_Util.ktype0 in
                                                                 (match g_opt
                                                                  with
                                                                  | Some g'
                                                                    ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                  | None  ->
                                                                    fail4 ())
                                                               else fail4 ()
                                                           | Some
                                                               (FStar_Util.Inr
                                                               (lid,uu____1939))
                                                               ->
                                                               if
                                                                 Prims.op_Negation
                                                                   (FStar_Syntax_Util.is_pure_effect
                                                                    lid)
                                                               then fail4 ()
                                                               else ());
                                                          (let wp =
                                                             let t2 =
                                                               (fst b21).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp" None
                                                               pure_wp_type in
                                                           let body3 =
                                                             let uu____1959 =
                                                               let uu____1960
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1961
                                                                 =
                                                                 let uu____1962
                                                                   =
                                                                   let uu____1966
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1966,
                                                                    None) in
                                                                 [uu____1962] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1960
                                                                 uu____1961 in
                                                             uu____1959 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1982 =
                                                             let uu____1983 =
                                                               let uu____1987
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1987] in
                                                             b11 ::
                                                               uu____1983 in
                                                           let uu____1990 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1982
                                                             uu____1990
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____2000 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2002 =
                                             let uu____2003 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2003.FStar_Syntax_Syntax.n in
                                           match uu____2002 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2041 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2041
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2057 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2059 =
                                             let uu____2060 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2060.FStar_Syntax_Syntax.n in
                                           match uu____2059 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2089 =
                                                 let uu____2090 =
                                                   let uu____2092 =
                                                     let uu____2093 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2093 in
                                                   [uu____2092] in
                                                 FStar_List.append uu____2090
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2089 body what
                                           | uu____2094 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2114 =
                                                let uu____2115 =
                                                  let uu____2116 =
                                                    let uu____2126 =
                                                      let uu____2127 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2127 in
                                                    (t, uu____2126) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2116 in
                                                mk1 uu____2115 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2114) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2150 = f a2 in
                                               [uu____2150]
                                           | x::xs ->
                                               let uu____2154 =
                                                 apply_last1 f xs in
                                               x :: uu____2154 in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange in
                                           let uu____2169 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2169 with
                                           | Some (_us,_t) ->
                                               ((let uu____2186 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2186
                                                 then
                                                   let uu____2187 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2187
                                                 else ());
                                                (let uu____2189 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2189))
                                           | None  ->
                                               let uu____2194 =
                                                 let uu____2197 = mk_lid name in
                                                 let uu____2198 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2197 uu____2198 in
                                               (match uu____2194 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2207 =
                                                        let uu____2209 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2209 in
                                                      FStar_ST.write sigelts
                                                        uu____2207);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2220 =
                                             let uu____2222 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2223 =
                                               FStar_ST.read sigelts in
                                             uu____2222 :: uu____2223 in
                                           FStar_ST.write sigelts uu____2220);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2233 =
                                              let uu____2235 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2236 =
                                                FStar_ST.read sigelts in
                                              uu____2235 :: uu____2236 in
                                            FStar_ST.write sigelts uu____2233);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2246 =
                                               let uu____2248 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2249 =
                                                 FStar_ST.read sigelts in
                                               uu____2248 :: uu____2249 in
                                             FStar_ST.write sigelts
                                               uu____2246);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2259 =
                                                let uu____2261 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2262 =
                                                  FStar_ST.read sigelts in
                                                uu____2261 :: uu____2262 in
                                              FStar_ST.write sigelts
                                                uu____2259);
                                             (let uu____2270 =
                                                FStar_List.fold_left
                                                  (fun uu____2277  ->
                                                     fun action  ->
                                                       match uu____2277 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2290 =
                                                             let uu____2294 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2294
                                                               params_un in
                                                           (match uu____2290
                                                            with
                                                            | (action_params,env',uu____2300)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2309
                                                                     ->
                                                                    match uu____2309
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2316
                                                                    =
                                                                    let uu___131_2317
                                                                    = bv in
                                                                    let uu____2318
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___131_2317.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___131_2317.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2318
                                                                    } in
                                                                    (uu____2316,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2322
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2322
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    None in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____2348
                                                                    ->
                                                                    let uu____2349
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2349 in
                                                                    ((
                                                                    let uu____2353
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2353
                                                                    then
                                                                    let uu____2354
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2355
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2356
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2357
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2354
                                                                    uu____2355
                                                                    uu____2356
                                                                    uu____2357
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                    let uu____2361
                                                                    =
                                                                    let uu____2363
                                                                    =
                                                                    let uu___132_2364
                                                                    = action in
                                                                    let uu____2365
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2366
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___132_2364.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___132_2364.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___132_2364.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2365;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2366
                                                                    } in
                                                                    uu____2363
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2361))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2270 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2386 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2387 =
                                                        let uu____2389 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2389] in
                                                      uu____2386 ::
                                                        uu____2387 in
                                                    let uu____2390 =
                                                      let uu____2391 =
                                                        let uu____2392 =
                                                          let uu____2393 =
                                                            let uu____2403 =
                                                              let uu____2407
                                                                =
                                                                let uu____2410
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2411
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2410,
                                                                  uu____2411) in
                                                              [uu____2407] in
                                                            (repr,
                                                              uu____2403) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2393 in
                                                        mk1 uu____2392 in
                                                      let uu____2419 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2391
                                                        uu____2419 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2390 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2427 =
                                                    let uu____2432 =
                                                      let uu____2433 =
                                                        let uu____2436 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2436 in
                                                      uu____2433.FStar_Syntax_Syntax.n in
                                                    match uu____2432 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2444)
                                                        ->
                                                        let uu____2471 =
                                                          let uu____2480 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2480
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2511 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2471
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2539 =
                                                               let uu____2540
                                                                 =
                                                                 let uu____2543
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2543 in
                                                               uu____2540.FStar_Syntax_Syntax.n in
                                                             (match uu____2539
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2560
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2560
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2569
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2580
                                                                     ->
                                                                    match uu____2580
                                                                    with
                                                                    | 
                                                                    (bv,uu____2584)
                                                                    ->
                                                                    let uu____2585
                                                                    =
                                                                    let uu____2586
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2586
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2585
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2569
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    uu____2619
                                                                    ->
                                                                    let uu____2623
                                                                    =
                                                                    let uu____2624
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2624 in
                                                                    failwith
                                                                    uu____2623 in
                                                                    let uu____2627
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2630
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2627,
                                                                    uu____2630)))
                                                              | uu____2640 ->
                                                                  let uu____2641
                                                                    =
                                                                    let uu____2642
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2642 in
                                                                  failwith
                                                                    uu____2641))
                                                    | uu____2647 ->
                                                        let uu____2648 =
                                                          let uu____2649 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2649 in
                                                        failwith uu____2648 in
                                                  (match uu____2427 with
                                                   | (pre,post) ->
                                                       ((let uu____2666 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2668 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2670 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___133_2672
                                                             = ed in
                                                           let uu____2673 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2674 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2675 =
                                                             let uu____2676 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2676) in
                                                           let uu____2682 =
                                                             let uu____2683 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2683) in
                                                           let uu____2689 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2690 =
                                                             let uu____2691 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2691) in
                                                           let uu____2697 =
                                                             let uu____2698 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2698) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2673;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2674;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2675;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2682;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___133_2672.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2689;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2690;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2697;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2704 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2704
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2715
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2715
                                                               then
                                                                 let uu____2716
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2716
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int
                                                                    "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____2728
                                                                    =
                                                                    let uu____2730
                                                                    =
                                                                    let uu____2736
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2736) in
                                                                    Some
                                                                    uu____2730 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2728;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2747
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2747
                                                                 else None in
                                                               let uu____2749
                                                                 =
                                                                 let uu____2751
                                                                   =
                                                                   let uu____2753
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2753 in
                                                                 FStar_List.append
                                                                   uu____2751
                                                                   sigelts' in
                                                               (uu____2749,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
and tc_lex_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          match ses with
          | {
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (lex_t1,[],[],t,uu____2776,uu____2777);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2779;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2783);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2785;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2789);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2791;_}::[]
              when
              ((_0_39 = (Prims.parse_int "0")) &&
                 (_0_40 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t1 FStar_Syntax_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top1
                       FStar_Syntax_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Syntax_Const.lexcons_lid))
              ->
              let u = FStar_Syntax_Syntax.new_univ_name (Some r) in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r in
              let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
              let tc =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_inductive_typ
                       (lex_t1, [u], [], t2, [],
                         [FStar_Syntax_Const.lextop_lid;
                         FStar_Syntax_Const.lexcons_lid]));
                  FStar_Syntax_Syntax.sigrng = r;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
              let lex_top_t =
                let uu____2830 =
                  let uu____2833 =
                    let uu____2834 =
                      let uu____2839 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2839, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2834 in
                  FStar_Syntax_Syntax.mk uu____2833 in
                uu____2830 None r1 in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_top1, [utop], lex_top_t1,
                         FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
                  FStar_Syntax_Syntax.sigrng = r1;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let lex_cons_t =
                let a =
                  let uu____2859 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2859 in
                let hd1 =
                  let uu____2865 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2865 in
                let tl1 =
                  let uu____2867 =
                    let uu____2868 =
                      let uu____2871 =
                        let uu____2872 =
                          let uu____2877 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2877, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2872 in
                      FStar_Syntax_Syntax.mk uu____2871 in
                    uu____2868 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2867 in
                let res =
                  let uu____2890 =
                    let uu____2893 =
                      let uu____2894 =
                        let uu____2899 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2899,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2894 in
                    FStar_Syntax_Syntax.mk uu____2893 in
                  uu____2890 None r2 in
                let uu____2909 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2909 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_cons, [ucons1; ucons2], lex_cons_t1,
                         FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
                  FStar_Syntax_Syntax.sigrng = r2;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let uu____2931 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2931;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2934 ->
              let uu____2936 =
                let uu____2937 =
                  let uu____2938 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2938 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2937 in
              failwith uu____2936
and tc_assume:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.formula ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun lid  ->
      fun phi  ->
        fun quals  ->
          fun r  ->
            let env1 = FStar_TypeChecker_Env.set_range env r in
            let uu____2948 = FStar_Syntax_Util.type_u () in
            match uu____2948 with
            | (k,uu____2952) ->
                let phi1 =
                  let uu____2954 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2954
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_assume (lid, phi1));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = quals;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta
                 })
and tc_inductive:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env0 = env in
          let uu____2964 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2964 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2983 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2983 FStar_List.flatten in
              ((let uu____2991 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2991
                then ()
                else
                  (let env1 =
                     FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env1 in
                        if Prims.op_Negation b
                        then
                          let uu____2997 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____3003,uu____3004,uu____3005,uu____3006,uu____3007)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____3012 -> failwith "Impossible!" in
                          match uu____2997 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____3021 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____3025,uu____3026,uu____3027,uu____3028,uu____3029)
                        -> lid
                    | uu____3034 -> failwith "Impossible" in
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"] in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals in
                let uu____3040 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____3040
                then ([sig_bndle], data_ops_ses)
                else
                  (let is_unopteq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                   let ses1 =
                     if is_unopteq
                     then
                       FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                     else
                       FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume in
                   let uu____3058 =
                     let uu____3060 =
                       let uu____3061 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____3061;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____3060 :: ses1 in
                   (uu____3058, data_ops_ses))))
and tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list)
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3079 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3092 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3122 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3122 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3147 = FStar_Options.set_options t s in
             match uu____3147 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s1 ->
                 raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s1), r)) in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____3164 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3164 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3170 = cps_and_elaborate env1 ne in
           (match uu____3170 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___134_3191 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___134_3191.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___134_3191.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___134_3191.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___135_3192 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___135_3192.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___135_3192.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___135_3192.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___136_3198 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___136_3198.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___136_3198.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___136_3198.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3204 =
             let uu____3209 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3209 in
           (match uu____3204 with
            | (a,wp_a_src) ->
                let uu____3220 =
                  let uu____3225 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3225 in
                (match uu____3220 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3237 =
                         let uu____3239 =
                           let uu____3240 =
                             let uu____3245 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3245) in
                           FStar_Syntax_Syntax.NT uu____3240 in
                         [uu____3239] in
                       FStar_Syntax_Subst.subst uu____3237 wp_b_tgt in
                     let expected_k =
                       let uu____3249 =
                         let uu____3253 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3254 =
                           let uu____3256 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3256] in
                         uu____3253 :: uu____3254 in
                       let uu____3257 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3249 uu____3257 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3278 =
                           let uu____3279 =
                             let uu____3282 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3283 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3282, uu____3283) in
                           FStar_Errors.Error uu____3279 in
                         raise uu____3278 in
                       let uu____3286 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3286 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3305 =
                             let uu____3306 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3306 in
                           if uu____3305
                           then no_reify eff_name
                           else
                             (let uu____3311 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3312 =
                                let uu____3315 =
                                  let uu____3316 =
                                    let uu____3326 =
                                      let uu____3328 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3329 =
                                        let uu____3331 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3331] in
                                      uu____3328 :: uu____3329 in
                                    (repr, uu____3326) in
                                  FStar_Syntax_Syntax.Tm_app uu____3316 in
                                FStar_Syntax_Syntax.mk uu____3315 in
                              uu____3312 None uu____3311) in
                     let uu____3341 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3356,lift_wp)) ->
                           let uu____3369 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3369)
                       | (Some (what,lift),None ) ->
                           ((let uu____3384 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3384
                             then
                               let uu____3385 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3385
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3388 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3388 with
                             | (lift1,comp,uu____3397) ->
                                 let uu____3398 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3398 with
                                  | (uu____3405,lift_wp,lift_elab) ->
                                      let uu____3408 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3409 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3341 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___137_3432 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___137_3432.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___137_3432.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___137_3432.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___137_3432.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___137_3432.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___137_3432.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___137_3432.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___137_3432.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___137_3432.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___137_3432.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___137_3432.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___137_3432.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___137_3432.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___137_3432.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___137_3432.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___137_3432.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___137_3432.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___137_3432.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___137_3432.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___137_3432.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___137_3432.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___137_3432.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___137_3432.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___137_3432.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___137_3432.FStar_TypeChecker_Env.synth)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3436,lift1) ->
                                let uu____3443 =
                                  let uu____3448 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3448 in
                                (match uu____3443 with
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src1 in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a1 in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.source
                                         a_typ wp_a_typ in
                                     let repr_result =
                                       let lift_wp1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env2 (snd lift_wp) in
                                       let lift_wp_a =
                                         let uu____3470 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3471 =
                                           let uu____3474 =
                                             let uu____3475 =
                                               let uu____3485 =
                                                 let uu____3487 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3488 =
                                                   let uu____3490 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3490] in
                                                 uu____3487 :: uu____3488 in
                                               (lift_wp1, uu____3485) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3475 in
                                           FStar_Syntax_Syntax.mk uu____3474 in
                                         uu____3471 None uu____3470 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3503 =
                                         let uu____3507 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3508 =
                                           let uu____3510 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3511 =
                                             let uu____3513 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3513] in
                                           uu____3510 :: uu____3511 in
                                         uu____3507 :: uu____3508 in
                                       let uu____3514 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3503
                                         uu____3514 in
                                     let uu____3517 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3517 with
                                      | (expected_k2,uu____3523,uu____3524)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___138_3527 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___138_3527.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___138_3527.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___139_3529 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___139_3529.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___139_3529.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___139_3529.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3542 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3542 with
            | (tps1,c1) ->
                let uu____3551 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3551 with
                 | (tps2,env3,us) ->
                     let uu____3562 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3562 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3576 =
                              let uu____3577 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3577 in
                            match uu____3576 with
                            | (uvs1,t) ->
                                let uu____3590 =
                                  let uu____3598 =
                                    let uu____3601 =
                                      let uu____3602 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3602.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3601) in
                                  match uu____3598 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3612,c4)) -> ([], c4)
                                  | (uu____3636,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3654 -> failwith "Impossible" in
                                (match uu____3590 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3685 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3685 with
                                         | (uu____3688,t1) ->
                                             let uu____3690 =
                                               let uu____3691 =
                                                 let uu____3694 =
                                                   let uu____3695 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3696 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3701 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3695 uu____3696
                                                     uu____3701 in
                                                 (uu____3694, r) in
                                               FStar_Errors.Error uu____3691 in
                                             raise uu____3690)
                                      else ();
                                      (let se1 =
                                         let uu___140_3704 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___140_3704.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___140_3704.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___140_3704.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3714,uu____3715,uu____3716) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___114_3718  ->
                   match uu___114_3718 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3719 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3722,uu____3723,uu____3724) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___114_3730  ->
                   match uu___114_3730 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3731 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3738 =
             if uvs = []
             then
               let uu____3739 =
                 let uu____3740 = FStar_Syntax_Util.type_u () in
                 fst uu____3740 in
               check_and_gen env2 t uu____3739
             else
               (let uu____3744 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3744 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3750 =
                        let uu____3751 = FStar_Syntax_Util.type_u () in
                        fst uu____3751 in
                      tc_check_trivial_guard env2 t1 uu____3750 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3755 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3755)) in
           (match uu____3738 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___141_3765 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_3765.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_3765.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_3765.FStar_Syntax_Syntax.sigmeta)
                  } in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi) ->
           let se1 = tc_assume env1 lid phi se.FStar_Syntax_Syntax.sigquals r in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit in
           let uu____3777 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3777 with
            | (e1,c,g1) ->
                let uu____3788 =
                  let uu____3792 =
                    let uu____3794 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3794 in
                  let uu____3795 =
                    let uu____3798 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3798) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3792 uu____3795 in
                (match uu____3788 with
                 | (e2,uu____3808,g) ->
                     ((let uu____3811 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3811);
                      (let se1 =
                         let uu___142_3813 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___142_3813.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___142_3813.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___142_3813.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3849 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3849
                 then Some q
                 else
                   (let uu____3862 =
                      let uu____3863 =
                        let uu____3866 =
                          let uu____3867 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3868 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3869 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3867 uu____3868 uu____3869 in
                        (uu____3866, r) in
                      FStar_Errors.Error uu____3863 in
                    raise uu____3862) in
           let uu____3872 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3893  ->
                     fun lb  ->
                       match uu____3893 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3917 =
                             let uu____3923 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3923 with
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | Some ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____3975 ->
                                       FStar_Errors.warn r
                                         "Annotation from val declaration overrides inline type annotation");
                                  if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inline universes are incoherent with annotation from val declaration",
                                           r))
                                  else ();
                                  (let uu____3987 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3987, quals_opt1))) in
                           (match uu____3917 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3872 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____4040 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___115_4042  ->
                                match uu___115_4042 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____4043 -> false)) in
                      if uu____4040
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____4051 =
                    let uu____4054 =
                      let uu____4055 =
                        let uu____4063 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____4063) in
                      FStar_Syntax_Syntax.Tm_let uu____4055 in
                    FStar_Syntax_Syntax.mk uu____4054 in
                  uu____4051 None r in
                let uu____4085 =
                  let uu____4091 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___143_4095 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___143_4095.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___143_4095.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___143_4095.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___143_4095.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___143_4095.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___143_4095.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___143_4095.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___143_4095.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___143_4095.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___143_4095.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___143_4095.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___143_4095.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___143_4095.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___143_4095.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___143_4095.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___143_4095.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___143_4095.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___143_4095.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___143_4095.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___143_4095.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___143_4095.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___143_4095.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___143_4095.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___143_4095.FStar_TypeChecker_Env.synth)
                       }) e in
                  match uu____4091 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4103;
                       FStar_Syntax_Syntax.pos = uu____4104;
                       FStar_Syntax_Syntax.vars = uu____4105;_},uu____4106,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4125,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4130 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___116_4133  ->
                             match uu___116_4133 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4135 =
                                   let uu____4136 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4140 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4140)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4136 in
                                 if uu____4135
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___144_4149 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___144_4149.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___144_4149.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4155 -> failwith "impossible" in
                (match uu____4085 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4182 = log env2 in
                       if uu____4182
                       then
                         let uu____4183 =
                           let uu____4184 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4191 =
                                         let uu____4196 =
                                           let uu____4197 =
                                             let uu____4202 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4202.FStar_Syntax_Syntax.fv_name in
                                           uu____4197.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4196 in
                                       match uu____4191 with
                                       | None  -> true
                                       | uu____4209 -> false in
                                     if should_log
                                     then
                                       let uu____4214 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4215 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4214 uu____4215
                                     else "")) in
                           FStar_All.pipe_right uu____4184
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4183
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4239 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____4239 with
                              | (bs1,c1) ->
                                  let uu____4244 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____4244
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4254 =
                                            let uu____4255 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____4255.FStar_Syntax_Syntax.n in
                                          (match uu____4254 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4274 =
                                                 let uu____4275 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____4275.FStar_Syntax_Syntax.n in
                                               (match uu____4274 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4285 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4285 in
                                                    let uu____4286 =
                                                      let uu____4287 =
                                                        let uu____4288 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4288 args in
                                                      uu____4287 None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4286 u
                                                | uu____4293 -> c1)
                                           | uu____4294 -> c1)
                                      | uu____4295 -> c1 in
                                    let uu___145_4296 = t1 in
                                    let uu____4297 =
                                      let uu____4298 =
                                        let uu____4306 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4306) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4298 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4297;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___145_4296.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___145_4296.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___145_4296.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4328 =
                               let uu____4329 = FStar_Syntax_Subst.compress h in
                               uu____4329.FStar_Syntax_Syntax.n in
                             (match uu____4328 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4339 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4339 in
                                  let uu____4340 =
                                    let uu____4341 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4341
                                      args in
                                  uu____4340 None t1.FStar_Syntax_Syntax.pos
                              | uu____4346 -> t1)
                         | uu____4347 -> t1 in
                       let reified_tactic_decl assm_lid lb =
                         let t =
                           reified_tactic_type assm_lid
                             lb.FStar_Syntax_Syntax.lbtyp in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (assm_lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                  t));
                           FStar_Syntax_Syntax.sigrng =
                             (FStar_Ident.range_of_lid assm_lid);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta
                         } in
                       let reflected_tactic_decl b lb bs assm_lid comp =
                         let reified_tac =
                           let uu____4378 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4378 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4387 =
                                  FStar_Syntax_Syntax.bv_to_name (fst x) in
                                (uu____4387, (snd x))) bs in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Syntax_Const.tac_effect_lid)) None
                             FStar_Range.dummyRange in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             None FStar_Range.dummyRange in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, None)] None FStar_Range.dummyRange in
                         let unit_binder =
                           let uu____4419 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4419 in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (Some
                                (FStar_Util.Inl
                                   (FStar_Syntax_Util.lcomp_of_comp comp))) in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (Some
                                (FStar_Util.Inl
                                   (FStar_Syntax_Util.lcomp_of_comp comp))) in
                         let uu___146_4450 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___147_4457 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___147_4457.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___147_4457.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___147_4457.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___147_4457.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids, attrs));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___146_4450.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___146_4450.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___146_4450.FStar_Syntax_Syntax.sigmeta)
                         } in
                       let tactic_decls =
                         match snd lbs1 with
                         | hd1::[] ->
                             let uu____4467 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4467 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4487 =
                                    let uu____4488 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4488.FStar_Syntax_Syntax.n in
                                  (match uu____4487 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4512 =
                                           let uu____4517 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4517.FStar_Syntax_Syntax.fv_name in
                                         uu____4512.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4522 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4522 in
                                       let uu____4523 =
                                         (is_native_tactic assm_lid h1) &&
                                           (let uu____4524 =
                                              let uu____4525 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4525 in
                                            Prims.op_Negation uu____4524) in
                                       if uu____4523
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl (fst lbs1)
                                             hd1 bs assm_lid comp in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4548 -> None))
                         | uu____4551 -> None in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4564 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4564
                             then
                               let uu____4565 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4566 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4565 uu____4566
                             else ());
                            ([se_assm; se_refl], []))
                       | None  -> ([se1], []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Ident.lident Prims.list)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___117_4599  ->
                match uu___117_4599 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4600 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4606) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4610 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4615 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4618 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4631 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4644) ->
          let uu____4649 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4649
          then
            let for_export_bundle se1 uu____4668 =
              match uu____4668 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4691,uu____4692) ->
                       let dec =
                         let uu___148_4698 = se1 in
                         let uu____4699 =
                           let uu____4700 =
                             let uu____4704 =
                               let uu____4707 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4707 in
                             (l, us, uu____4704) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4700 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4699;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___148_4698.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___148_4698.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4717,uu____4718,uu____4719) ->
                       let dec =
                         let uu___149_4723 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___149_4723.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___149_4723.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4726 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4738,uu____4739) ->
          let uu____4740 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4740 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4753 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4753
          then
            ([(let uu___150_4761 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___150_4761.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___150_4761.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4763 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___118_4765  ->
                       match uu___118_4765 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4766 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4769 -> true
                       | uu____4770 -> false)) in
             if uu____4763 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4780 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4783 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4786 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4789 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4792 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4802,uu____4803)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4819 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4819
          then ([], hidden)
          else
            (let dec =
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta
               } in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4840) ->
          let uu____4845 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4845
          then
            let uu____4850 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___151_4856 = se in
                      let uu____4857 =
                        let uu____4858 =
                          let uu____4862 =
                            let uu____4863 =
                              let uu____4868 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4868.FStar_Syntax_Syntax.fv_name in
                            uu____4863.FStar_Syntax_Syntax.v in
                          (uu____4862, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4858 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4857;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___151_4856.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___151_4856.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4850, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4888 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4897 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4906 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4909 = FStar_Options.using_facts_from () in
                 match uu____4909 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4921 =
                         let uu____4926 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4926 [([], false)] in
                       [uu____4921] in
                     let uu___152_4954 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___152_4954.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___152_4954.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___152_4954.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___152_4954.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___152_4954.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___152_4954.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___152_4954.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___152_4954.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___152_4954.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___152_4954.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___152_4954.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___152_4954.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___152_4954.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___152_4954.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___152_4954.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___152_4954.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___152_4954.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___152_4954.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___152_4954.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___152_4954.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___152_4954.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___152_4954.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___152_4954.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___152_4954.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___152_4954.FStar_TypeChecker_Env.synth)
                     }
                 | None  -> env))
           | uu____4956 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4957 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4963 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4963) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4964,uu____4965,uu____4966) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_4968  ->
                  match uu___119_4968 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4969 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4970,uu____4971,uu____4972) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_4978  ->
                  match uu___119_4978 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4979 -> false))
          -> env
      | uu____4980 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____5018 se =
        match uu____5018 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5048 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____5048
              then
                let uu____5049 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5049
              else ());
             (let uu____5051 = tc_decl env1 se in
              match uu____5051 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____5077 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____5077
                    then
                      let uu____5078 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____5081 =
                                 let uu____5082 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____5082 "\n" in
                               Prims.strcat s uu____5081) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____5078
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____5086 =
                      let accum_exports_hidden uu____5104 se1 =
                        match uu____5104 with
                        | (exports1,hidden1) ->
                            let uu____5120 = for_export hidden1 se1 in
                            (match uu____5120 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____5086 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____5170 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____5170 with
      | (ses1,exports,env1,uu____5196) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
        FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____5223 = FStar_Options.debug_any () in
       if uu____5223
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
       let msg = Prims.strcat "Internals for " name in
       let env1 =
         let uu___153_5229 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___153_5229.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___153_5229.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___153_5229.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___153_5229.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___153_5229.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___153_5229.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___153_5229.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___153_5229.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___153_5229.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___153_5229.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___153_5229.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___153_5229.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___153_5229.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___153_5229.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___153_5229.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___153_5229.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___153_5229.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___153_5229.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___153_5229.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___153_5229.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___153_5229.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___153_5229.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___153_5229.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___153_5229.FStar_TypeChecker_Env.synth)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____5232 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5232 with
        | (ses,exports,env3) ->
            ((let uu___154_5250 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___154_5250.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___154_5250.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___154_5250.FStar_Syntax_Syntax.is_interface)
              }), exports, env3)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
          FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____5269 = tc_decls env decls in
        match uu____5269 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___155_5287 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___155_5287.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___155_5287.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___155_5287.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, exports, env1)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___156_5304 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___156_5304.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___156_5304.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___156_5304.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___156_5304.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___156_5304.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___156_5304.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___156_5304.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___156_5304.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___156_5304.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___156_5304.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___156_5304.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___156_5304.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___156_5304.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___156_5304.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___156_5304.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___156_5304.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___156_5304.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___156_5304.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___156_5304.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___156_5304.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___156_5304.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___156_5304.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___156_5304.FStar_TypeChecker_Env.synth)
          } in
        let check_term lid univs1 t =
          let uu____5315 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5315 with
          | (univs2,t1) ->
              ((let uu____5321 =
                  let uu____5322 =
                    let uu____5325 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5325 in
                  FStar_All.pipe_left uu____5322
                    (FStar_Options.Other "Exports") in
                if uu____5321
                then
                  let uu____5326 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5327 =
                    let uu____5328 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5328
                      (FStar_String.concat ", ") in
                  let uu____5333 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5326 uu____5327 uu____5333
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5336 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5336 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5354 =
             let uu____5355 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5356 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5355 uu____5356 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5354);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5363) ->
              let uu____5368 =
                let uu____5369 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5369 in
              if uu____5368
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5377,uu____5378) ->
              let t =
                let uu____5386 =
                  let uu____5389 =
                    let uu____5390 =
                      let uu____5398 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5398) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5390 in
                  FStar_Syntax_Syntax.mk uu____5389 in
                uu____5386 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5410,uu____5411,uu____5412) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5418 =
                let uu____5419 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5419 in
              if uu____5418 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5422,lbs),uu____5424,uu____5425) ->
              let uu____5435 =
                let uu____5436 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5436 in
              if uu____5435
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags) ->
              let uu____5453 =
                let uu____5454 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5454 in
              if uu____5453
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5468 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5469 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5472 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5473 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5474 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5475 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let finish_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul1 =
          let uu___157_5492 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___157_5492.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___157_5492.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5495 =
           let uu____5496 = FStar_Options.lax () in
           Prims.op_Negation uu____5496 in
         if uu____5495 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5502 =
           let uu____5503 = FStar_Options.interactive () in
           Prims.op_Negation uu____5503 in
         if uu____5502
         then
           let uu____5504 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5504 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5516 = tc_partial_modul env modul in
      match uu____5516 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5539 = FStar_Options.debug_any () in
       if uu____5539
       then
         let uu____5540 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5540
       else ());
      (let env1 =
         let uu___158_5544 = env in
         let uu____5545 =
           let uu____5546 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5546 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___158_5544.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___158_5544.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___158_5544.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___158_5544.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___158_5544.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___158_5544.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___158_5544.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___158_5544.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___158_5544.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___158_5544.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___158_5544.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___158_5544.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___158_5544.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___158_5544.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___158_5544.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___158_5544.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___158_5544.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___158_5544.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5545;
           FStar_TypeChecker_Env.lax_universes =
             (uu___158_5544.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___158_5544.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___158_5544.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___158_5544.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___158_5544.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___158_5544.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___158_5544.FStar_TypeChecker_Env.synth)
         } in
       let uu____5547 = tc_modul env1 m in
       match uu____5547 with
       | (m1,env2) ->
           ((let uu____5555 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5555
             then
               let uu____5556 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5556
             else ());
            (let uu____5559 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5559
             then
               let normalize_toplevel_lets se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),ids,attrs) ->
                     let n1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.Eager_unfolding;
                         FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
                     let update lb =
                       let uu____5586 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5586 with
                       | (univnames1,e) ->
                           let uu___159_5591 = lb in
                           let uu____5592 =
                             let uu____5595 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5595 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___159_5591.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___159_5591.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___159_5591.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___159_5591.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5592
                           } in
                     let uu___160_5596 = se in
                     let uu____5597 =
                       let uu____5598 =
                         let uu____5604 =
                           let uu____5608 = FStar_List.map update lbs in
                           (b, uu____5608) in
                         (uu____5604, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5598 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5597;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___160_5596.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___160_5596.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___160_5596.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5616 -> se in
               let normalized_module =
                 let uu___161_5618 = m1 in
                 let uu____5619 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___161_5618.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5619;
                   FStar_Syntax_Syntax.exports =
                     (uu___161_5618.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___161_5618.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5620 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5620
             else ());
            (m1, env2)))