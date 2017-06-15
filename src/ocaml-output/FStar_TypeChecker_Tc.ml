open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for () in
      match uu____7 with
      | Some l ->
          let lid =
            let uu____11 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____11 l in
          let uu___120_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___120_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___120_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___120_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___120_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___120_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___120_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___120_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___120_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___120_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___120_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___120_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___120_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___120_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___120_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___120_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___120_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___120_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___120_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___120_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___120_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___120_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___120_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___120_12.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___120_12.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___120_12.FStar_TypeChecker_Env.synth)
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____18 = FStar_TypeChecker_Env.current_module env in
                let uu____19 =
                  let uu____20 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____20 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____18 uu____19
            | l::uu____22 -> l in
          let uu___121_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___121_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___121_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___121_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___121_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___121_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___121_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___121_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___121_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___121_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___121_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___121_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___121_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___121_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___121_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___121_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___121_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___121_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___121_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___121_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___121_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___121_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___121_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___121_24.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___121_24.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___121_24.FStar_TypeChecker_Env.synth)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____30 =
         let uu____31 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____31 in
       Prims.op_Negation uu____30)
let is_native_tactic:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun tac_lid  ->
    fun h  ->
      match h.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_uinst (h',uu____39) ->
          let uu____44 =
            let uu____45 = FStar_Syntax_Subst.compress h' in
            uu____45.FStar_Syntax_Syntax.n in
          (match uu____44 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.tactic_lid
               -> FStar_Tactics_Native.is_native_tactic tac_lid
           | uu____49 -> false)
      | uu____50 -> false
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____60 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____60 with
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
        (let uu____82 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____82
         then
           let uu____83 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____83
         else ());
        (let uu____85 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____85 with
         | (t',uu____90,uu____91) ->
             ((let uu____93 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____93
               then
                 let uu____94 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____94
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
        let uu____105 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____105
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____127 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____127)
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
        let fail4 uu____149 =
          let uu____150 =
            let uu____151 =
              let uu____154 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____154, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____151 in
          raise uu____150 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____182)::(wp,uu____184)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____193 -> fail4 ())
        | uu____194 -> fail4 ()
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____256 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____256 with
      | (effect_params_un,signature_un,opening) ->
          let uu____263 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____263 with
           | (effect_params,env,uu____269) ->
               let uu____270 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____270 with
                | (signature,uu____274) ->
                    let ed1 =
                      let uu___122_276 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___122_276.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___122_276.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___122_276.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___122_276.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___122_276.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___122_276.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___122_276.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___122_276.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___122_276.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___122_276.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___122_276.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___122_276.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___122_276.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___122_276.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___122_276.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___122_276.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___122_276.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____280 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
                          let uu___123_298 = ed1 in
                          let uu____299 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____300 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____301 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____302 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____303 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____304 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____305 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____306 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____307 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____308 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____309 =
                            let uu____310 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____310 in
                          let uu____316 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____317 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____318 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___124_321 = a in
                                 let uu____322 =
                                   let uu____323 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____323 in
                                 let uu____329 =
                                   let uu____330 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____330 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___124_321.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___124_321.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___124_321.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___124_321.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____322;
                                   FStar_Syntax_Syntax.action_typ = uu____329
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___123_298.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___123_298.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___123_298.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___123_298.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___123_298.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____299;
                            FStar_Syntax_Syntax.bind_wp = uu____300;
                            FStar_Syntax_Syntax.if_then_else = uu____301;
                            FStar_Syntax_Syntax.ite_wp = uu____302;
                            FStar_Syntax_Syntax.stronger = uu____303;
                            FStar_Syntax_Syntax.close_wp = uu____304;
                            FStar_Syntax_Syntax.assert_p = uu____305;
                            FStar_Syntax_Syntax.assume_p = uu____306;
                            FStar_Syntax_Syntax.null_wp = uu____307;
                            FStar_Syntax_Syntax.trivial = uu____308;
                            FStar_Syntax_Syntax.repr = uu____309;
                            FStar_Syntax_Syntax.return_repr = uu____316;
                            FStar_Syntax_Syntax.bind_repr = uu____317;
                            FStar_Syntax_Syntax.actions = uu____318
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail4 t =
                        let uu____358 =
                          let uu____359 =
                            let uu____362 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____362, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____359 in
                        raise uu____358 in
                      let uu____367 =
                        let uu____368 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____368.FStar_Syntax_Syntax.n in
                      match uu____367 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____393)::(wp,uu____395)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____404 -> fail4 signature1)
                      | uu____405 -> fail4 signature1 in
                    let uu____406 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____406 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____424 =
                           let uu____425 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____425 with
                           | (signature1,uu____433) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____435 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____435 in
                         ((let uu____437 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____437
                           then
                             let uu____438 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____439 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____440 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____441 =
                               let uu____442 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____442 in
                             let uu____443 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____438 uu____439 uu____440 uu____441
                               uu____443
                           else ());
                          (let check_and_gen' env2 uu____456 k =
                             match uu____456 with
                             | (uu____461,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____469 =
                                 let uu____473 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____474 =
                                   let uu____476 =
                                     let uu____477 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____477 in
                                   [uu____476] in
                                 uu____473 :: uu____474 in
                               let uu____478 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____469 uu____478 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____482 = fresh_effect_signature () in
                             match uu____482 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____496 =
                                     let uu____500 =
                                       let uu____501 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____501 in
                                     [uu____500] in
                                   let uu____502 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____496
                                     uu____502 in
                                 let expected_k =
                                   let uu____508 =
                                     let uu____512 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____513 =
                                       let uu____515 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____516 =
                                         let uu____518 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____519 =
                                           let uu____521 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____522 =
                                             let uu____524 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____524] in
                                           uu____521 :: uu____522 in
                                         uu____518 :: uu____519 in
                                       uu____515 :: uu____516 in
                                     uu____512 :: uu____513 in
                                   let uu____525 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____508
                                     uu____525 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____530 =
                                 let uu____531 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____531
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____530 in
                             let expected_k =
                               let uu____539 =
                                 let uu____543 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____544 =
                                   let uu____546 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____547 =
                                     let uu____549 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____550 =
                                       let uu____552 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____552] in
                                     uu____549 :: uu____550 in
                                   uu____546 :: uu____547 in
                                 uu____543 :: uu____544 in
                               let uu____553 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____539 uu____553 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____560 =
                                 let uu____564 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____565 =
                                   let uu____567 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____567] in
                                 uu____564 :: uu____565 in
                               let uu____568 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____560 uu____568 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____572 = FStar_Syntax_Util.type_u () in
                             match uu____572 with
                             | (t,uu____576) ->
                                 let expected_k =
                                   let uu____580 =
                                     let uu____584 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____585 =
                                       let uu____587 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____588 =
                                         let uu____590 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____590] in
                                       uu____587 :: uu____588 in
                                     uu____584 :: uu____585 in
                                   let uu____591 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____580
                                     uu____591 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____596 =
                                 let uu____597 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____597
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____596 in
                             let b_wp_a =
                               let uu____605 =
                                 let uu____609 =
                                   let uu____610 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____610 in
                                 [uu____609] in
                               let uu____611 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____605 uu____611 in
                             let expected_k =
                               let uu____617 =
                                 let uu____621 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____622 =
                                   let uu____624 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____625 =
                                     let uu____627 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____627] in
                                   uu____624 :: uu____625 in
                                 uu____621 :: uu____622 in
                               let uu____628 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____617 uu____628 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____635 =
                                 let uu____639 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____640 =
                                   let uu____642 =
                                     let uu____643 =
                                       let uu____644 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____644
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____643 in
                                   let uu____649 =
                                     let uu____651 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____651] in
                                   uu____642 :: uu____649 in
                                 uu____639 :: uu____640 in
                               let uu____652 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____635 uu____652 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____659 =
                                 let uu____663 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____664 =
                                   let uu____666 =
                                     let uu____667 =
                                       let uu____668 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____668
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____667 in
                                   let uu____673 =
                                     let uu____675 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____675] in
                                   uu____666 :: uu____673 in
                                 uu____663 :: uu____664 in
                               let uu____676 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____659 uu____676 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____683 =
                                 let uu____687 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____687] in
                               let uu____688 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____683 uu____688 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____692 = FStar_Syntax_Util.type_u () in
                             match uu____692 with
                             | (t,uu____696) ->
                                 let expected_k =
                                   let uu____700 =
                                     let uu____704 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____705 =
                                       let uu____707 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____707] in
                                     uu____704 :: uu____705 in
                                   let uu____708 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____700
                                     uu____708 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____711 =
                             let uu____717 =
                               let uu____718 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____718.FStar_Syntax_Syntax.n in
                             match uu____717 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____727 ->
                                 let repr =
                                   let uu____729 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____729 with
                                   | (t,uu____733) ->
                                       let expected_k =
                                         let uu____737 =
                                           let uu____741 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____742 =
                                             let uu____744 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____744] in
                                           uu____741 :: uu____742 in
                                         let uu____745 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____737
                                           uu____745 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____758 =
                                     let uu____761 =
                                       let uu____762 =
                                         let uu____772 =
                                           let uu____774 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____775 =
                                             let uu____777 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____777] in
                                           uu____774 :: uu____775 in
                                         (repr1, uu____772) in
                                       FStar_Syntax_Syntax.Tm_app uu____762 in
                                     FStar_Syntax_Syntax.mk uu____761 in
                                   uu____758 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____796 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____796 wp in
                                 let destruct_repr t =
                                   let uu____807 =
                                     let uu____808 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____808.FStar_Syntax_Syntax.n in
                                   match uu____807 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____817,(t1,uu____819)::(wp,uu____821)::[])
                                       -> (t1, wp)
                                   | uu____855 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____864 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____864
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____865 = fresh_effect_signature () in
                                   match uu____865 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____879 =
                                           let uu____883 =
                                             let uu____884 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____884 in
                                           [uu____883] in
                                         let uu____885 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____879
                                           uu____885 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____891 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____891 in
                                       let wp_g_x =
                                         let uu____895 =
                                           let uu____896 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____897 =
                                             let uu____898 =
                                               let uu____899 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____899 in
                                             [uu____898] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____896 uu____897 in
                                         uu____895 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____910 =
                                             let uu____911 =
                                               let uu____912 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____912
                                                 FStar_Pervasives.snd in
                                             let uu____917 =
                                               let uu____918 =
                                                 let uu____920 =
                                                   let uu____922 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____923 =
                                                     let uu____925 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____926 =
                                                       let uu____928 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____929 =
                                                         let uu____931 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____931] in
                                                       uu____928 :: uu____929 in
                                                     uu____925 :: uu____926 in
                                                   uu____922 :: uu____923 in
                                                 r :: uu____920 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____918 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____911 uu____917 in
                                           uu____910 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____939 =
                                           let uu____943 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____944 =
                                             let uu____946 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____947 =
                                               let uu____949 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____950 =
                                                 let uu____952 =
                                                   let uu____953 =
                                                     let uu____954 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____954 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____953 in
                                                 let uu____955 =
                                                   let uu____957 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____958 =
                                                     let uu____960 =
                                                       let uu____961 =
                                                         let uu____962 =
                                                           let uu____966 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____966] in
                                                         let uu____967 =
                                                           let uu____970 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____970 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____962
                                                           uu____967 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____961 in
                                                     [uu____960] in
                                                   uu____957 :: uu____958 in
                                                 uu____952 :: uu____955 in
                                               uu____949 :: uu____950 in
                                             uu____946 :: uu____947 in
                                           uu____943 :: uu____944 in
                                         let uu____971 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____939
                                           uu____971 in
                                       let uu____974 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____974 with
                                        | (expected_k1,uu____979,uu____980)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___125_984 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___125_984.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___125_984.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___125_984.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___125_984.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___125_984.FStar_TypeChecker_Env.synth)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____991 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____991 in
                                   let res =
                                     let wp =
                                       let uu____998 =
                                         let uu____999 =
                                           let uu____1000 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1000
                                             FStar_Pervasives.snd in
                                         let uu____1005 =
                                           let uu____1006 =
                                             let uu____1008 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1009 =
                                               let uu____1011 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1011] in
                                             uu____1008 :: uu____1009 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1006 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____999 uu____1005 in
                                       uu____998 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1019 =
                                       let uu____1023 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1024 =
                                         let uu____1026 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1026] in
                                       uu____1023 :: uu____1024 in
                                     let uu____1027 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1019
                                       uu____1027 in
                                   let uu____1030 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1030 with
                                   | (expected_k1,uu____1038,uu____1039) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1042 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1042 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1054 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1068 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1068 with
                                     | (act_typ,uu____1073,g_t) ->
                                         let env' =
                                           let uu___126_1076 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___126_1076.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___126_1076.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___126_1076.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___126_1076.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___126_1076.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___126_1076.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___126_1076.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___126_1076.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___126_1076.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___126_1076.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___126_1076.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___126_1076.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___126_1076.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___126_1076.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___126_1076.FStar_TypeChecker_Env.synth)
                                           } in
                                         ((let uu____1078 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1078
                                           then
                                             let uu____1079 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1080 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1079 uu____1080
                                           else ());
                                          (let uu____1082 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1082 with
                                           | (act_defn,uu____1087,g_a) ->
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
                                               let uu____1091 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1109 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1109 with
                                                      | (bs1,uu____1115) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1122 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1122 in
                                                          let uu____1125 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1125
                                                           with
                                                           | (k1,uu____1132,g)
                                                               -> (k1, g)))
                                                 | uu____1134 ->
                                                     let uu____1135 =
                                                       let uu____1136 =
                                                         let uu____1139 =
                                                           let uu____1140 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1141 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1140
                                                             uu____1141 in
                                                         (uu____1139,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1136 in
                                                     raise uu____1135 in
                                               (match uu____1091 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1148 =
                                                        let uu____1149 =
                                                          let uu____1150 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1150 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1149 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1148);
                                                     (let act_typ2 =
                                                        let uu____1154 =
                                                          let uu____1155 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1155.FStar_Syntax_Syntax.n in
                                                        match uu____1154 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1172 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1172
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1179
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1179
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1199
                                                                    =
                                                                    let uu____1200
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1200] in
                                                                    let uu____1201
                                                                    =
                                                                    let uu____1207
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1207] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1199;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1201;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1208
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1208))
                                                        | uu____1211 ->
                                                            failwith "" in
                                                      let uu____1214 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1214 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___127_1220 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___127_1220.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___127_1220.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___127_1220.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____711 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1236 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1236 in
                               let uu____1239 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1239 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1245 =
                                        let uu____1248 =
                                          let uu____1249 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1249.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1248) in
                                      match uu____1245 with
                                      | ([],uu____1252) -> t1
                                      | (uu____1258,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1259,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1271 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1282 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1282 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1288 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1289 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1289))
                                           && (m <> n1) in
                                       if uu____1288
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1303 =
                                           let uu____1304 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1305 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1304 uu____1305 in
                                         failwith uu____1303
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1311 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1311 with
                                      | (univs2,defn) ->
                                          let uu____1316 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1316 with
                                           | (univs',typ) ->
                                               let uu___128_1322 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___128_1322.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___128_1322.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___128_1322.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___129_1325 = ed2 in
                                      let uu____1326 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1327 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1328 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1329 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1330 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1331 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1332 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1333 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1334 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1335 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1336 =
                                        let uu____1337 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1337 in
                                      let uu____1343 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1344 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1345 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___129_1325.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___129_1325.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1326;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1327;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1328;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1329;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1330;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1331;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1332;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1333;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1334;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1335;
                                        FStar_Syntax_Syntax.repr = uu____1336;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1343;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1344;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1345
                                      } in
                                    ((let uu____1348 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1348
                                      then
                                        let uu____1349 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1349
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
      let uu____1353 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1353 with
      | (effect_binders_un,signature_un) ->
          let uu____1363 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1363 with
           | (effect_binders,env1,uu____1374) ->
               let uu____1375 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1375 with
                | (signature,uu____1384) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1393  ->
                           match uu____1393 with
                           | (bv,qual) ->
                               let uu____1400 =
                                 let uu___130_1401 = bv in
                                 let uu____1402 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___130_1401.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___130_1401.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1402
                                 } in
                               (uu____1400, qual)) effect_binders in
                    let uu____1405 =
                      let uu____1410 =
                        let uu____1411 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1411.FStar_Syntax_Syntax.n in
                      match uu____1410 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1419)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1434 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1405 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1451 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1451
                           then
                             let uu____1452 =
                               let uu____1454 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1454 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1452
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1478 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1478 with
                           | (t2,comp,uu____1486) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1497 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1497 with
                          | (repr,_comp) ->
                              ((let uu____1510 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1510
                                then
                                  let uu____1511 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1511
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
                                  let uu____1517 =
                                    let uu____1518 =
                                      let uu____1519 =
                                        let uu____1529 =
                                          let uu____1533 =
                                            let uu____1536 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1537 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1536, uu____1537) in
                                          [uu____1533] in
                                        (wp_type1, uu____1529) in
                                      FStar_Syntax_Syntax.Tm_app uu____1519 in
                                    mk1 uu____1518 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1517 in
                                let effect_signature =
                                  let binders =
                                    let uu____1552 =
                                      let uu____1555 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1555) in
                                    let uu____1556 =
                                      let uu____1560 =
                                        let uu____1561 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1561
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1560] in
                                    uu____1552 :: uu____1556 in
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
                                  let uu____1604 = item in
                                  match uu____1604 with
                                  | (u_item,item1) ->
                                      let uu____1616 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1616 with
                                       | (item2,item_comp) ->
                                           ((let uu____1626 =
                                               let uu____1627 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1627 in
                                             if uu____1626
                                             then
                                               let uu____1628 =
                                                 let uu____1629 =
                                                   let uu____1630 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1631 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1630 uu____1631 in
                                                 FStar_Errors.Err uu____1629 in
                                               raise uu____1628
                                             else ());
                                            (let uu____1633 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1633 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1646 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1646 with
                                | (dmff_env1,uu____1659,bind_wp,bind_elab) ->
                                    let uu____1662 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1662 with
                                     | (dmff_env2,uu____1675,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1679 =
                                             let uu____1680 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1680.FStar_Syntax_Syntax.n in
                                           match uu____1679 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1718 =
                                                 let uu____1726 =
                                                   let uu____1729 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1729 in
                                                 match uu____1726 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1768 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1718 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1790 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1790 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1801 =
                                                          let uu____1802 =
                                                            let uu____1812 =
                                                              let uu____1816
                                                                =
                                                                let uu____1819
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1820
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1819,
                                                                  uu____1820) in
                                                              [uu____1816] in
                                                            (wp_type1,
                                                              uu____1812) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1802 in
                                                        mk1 uu____1801 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1828 =
                                                      let uu____1838 =
                                                        let uu____1839 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1839 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1838 in
                                                    (match uu____1828 with
                                                     | (bs1,body2,what') ->
                                                         let fail4 uu____1867
                                                           =
                                                           let error_msg =
                                                             let uu____1869 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1870 =
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
                                                                   (lid,uu____1886))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1869
                                                               uu____1870 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  ->
                                                               fail4 ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1912
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1912
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
                                                               (lid,uu____1918))
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
                                                             let uu____1938 =
                                                               let uu____1939
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1940
                                                                 =
                                                                 let uu____1941
                                                                   =
                                                                   let uu____1945
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1945,
                                                                    None) in
                                                                 [uu____1941] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1939
                                                                 uu____1940 in
                                                             uu____1938 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1961 =
                                                             let uu____1962 =
                                                               let uu____1966
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1966] in
                                                             b11 ::
                                                               uu____1962 in
                                                           let uu____1969 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1961
                                                             uu____1969
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1979 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1981 =
                                             let uu____1982 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1982.FStar_Syntax_Syntax.n in
                                           match uu____1981 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2020 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2020
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2036 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2038 =
                                             let uu____2039 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2039.FStar_Syntax_Syntax.n in
                                           match uu____2038 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2068 =
                                                 let uu____2069 =
                                                   let uu____2071 =
                                                     let uu____2072 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2072 in
                                                   [uu____2071] in
                                                 FStar_List.append uu____2069
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2068 body what
                                           | uu____2073 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2093 =
                                                let uu____2094 =
                                                  let uu____2095 =
                                                    let uu____2105 =
                                                      let uu____2106 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2106 in
                                                    (t, uu____2105) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2095 in
                                                mk1 uu____2094 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2093) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2129 = f a2 in
                                               [uu____2129]
                                           | x::xs ->
                                               let uu____2133 =
                                                 apply_last1 f xs in
                                               x :: uu____2133 in
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
                                           let uu____2148 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2148 with
                                           | Some (_us,_t) ->
                                               ((let uu____2165 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2165
                                                 then
                                                   let uu____2166 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2166
                                                 else ());
                                                (let uu____2168 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2168))
                                           | None  ->
                                               let uu____2173 =
                                                 let uu____2176 = mk_lid name in
                                                 let uu____2177 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2176 uu____2177 in
                                               (match uu____2173 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2186 =
                                                        let uu____2188 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2188 in
                                                      FStar_ST.write sigelts
                                                        uu____2186);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2199 =
                                             let uu____2201 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2202 =
                                               FStar_ST.read sigelts in
                                             uu____2201 :: uu____2202 in
                                           FStar_ST.write sigelts uu____2199);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2212 =
                                              let uu____2214 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2215 =
                                                FStar_ST.read sigelts in
                                              uu____2214 :: uu____2215 in
                                            FStar_ST.write sigelts uu____2212);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2225 =
                                               let uu____2227 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2228 =
                                                 FStar_ST.read sigelts in
                                               uu____2227 :: uu____2228 in
                                             FStar_ST.write sigelts
                                               uu____2225);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2238 =
                                                let uu____2240 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2241 =
                                                  FStar_ST.read sigelts in
                                                uu____2240 :: uu____2241 in
                                              FStar_ST.write sigelts
                                                uu____2238);
                                             (let uu____2249 =
                                                FStar_List.fold_left
                                                  (fun uu____2256  ->
                                                     fun action  ->
                                                       match uu____2256 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2269 =
                                                             let uu____2273 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2273
                                                               params_un in
                                                           (match uu____2269
                                                            with
                                                            | (action_params,env',uu____2279)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2288
                                                                     ->
                                                                    match uu____2288
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2295
                                                                    =
                                                                    let uu___131_2296
                                                                    = bv in
                                                                    let uu____2297
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___131_2296.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___131_2296.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2297
                                                                    } in
                                                                    (uu____2295,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2301
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2301
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
                                                                    uu____2327
                                                                    ->
                                                                    let uu____2328
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2328 in
                                                                    ((
                                                                    let uu____2332
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2332
                                                                    then
                                                                    let uu____2333
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2334
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2335
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2336
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2333
                                                                    uu____2334
                                                                    uu____2335
                                                                    uu____2336
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
                                                                    let uu____2340
                                                                    =
                                                                    let uu____2342
                                                                    =
                                                                    let uu___132_2343
                                                                    = action in
                                                                    let uu____2344
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2345
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___132_2343.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___132_2343.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___132_2343.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2344;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2345
                                                                    } in
                                                                    uu____2342
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2340))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2249 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2365 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2366 =
                                                        let uu____2368 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2368] in
                                                      uu____2365 ::
                                                        uu____2366 in
                                                    let uu____2369 =
                                                      let uu____2370 =
                                                        let uu____2371 =
                                                          let uu____2372 =
                                                            let uu____2382 =
                                                              let uu____2386
                                                                =
                                                                let uu____2389
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2390
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2389,
                                                                  uu____2390) in
                                                              [uu____2386] in
                                                            (repr,
                                                              uu____2382) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2372 in
                                                        mk1 uu____2371 in
                                                      let uu____2398 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2370
                                                        uu____2398 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2369 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2406 =
                                                    let uu____2411 =
                                                      let uu____2412 =
                                                        let uu____2415 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2415 in
                                                      uu____2412.FStar_Syntax_Syntax.n in
                                                    match uu____2411 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2423)
                                                        ->
                                                        let uu____2450 =
                                                          let uu____2459 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2459
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2490 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2450
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2518 =
                                                               let uu____2519
                                                                 =
                                                                 let uu____2522
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2522 in
                                                               uu____2519.FStar_Syntax_Syntax.n in
                                                             (match uu____2518
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2539
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2539
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2548
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2559
                                                                     ->
                                                                    match uu____2559
                                                                    with
                                                                    | 
                                                                    (bv,uu____2563)
                                                                    ->
                                                                    let uu____2564
                                                                    =
                                                                    let uu____2565
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2565
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2564
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2548
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
                                                                    uu____2598
                                                                    ->
                                                                    let uu____2602
                                                                    =
                                                                    let uu____2603
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2603 in
                                                                    failwith
                                                                    uu____2602 in
                                                                    let uu____2606
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2609
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2606,
                                                                    uu____2609)))
                                                              | uu____2619 ->
                                                                  let uu____2620
                                                                    =
                                                                    let uu____2621
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2621 in
                                                                  failwith
                                                                    uu____2620))
                                                    | uu____2626 ->
                                                        let uu____2627 =
                                                          let uu____2628 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2628 in
                                                        failwith uu____2627 in
                                                  (match uu____2406 with
                                                   | (pre,post) ->
                                                       ((let uu____2645 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2647 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2649 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___133_2651
                                                             = ed in
                                                           let uu____2652 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2653 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2654 =
                                                             let uu____2655 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2655) in
                                                           let uu____2661 =
                                                             let uu____2662 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2662) in
                                                           let uu____2668 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2669 =
                                                             let uu____2670 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2670) in
                                                           let uu____2676 =
                                                             let uu____2677 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2677) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2652;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2653;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2654;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2661;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___133_2651.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2668;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2669;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2676;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2683 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2683
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2694
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2694
                                                               then
                                                                 let uu____2695
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2695
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
                                                                    let uu____2707
                                                                    =
                                                                    let uu____2709
                                                                    =
                                                                    let uu____2715
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2715) in
                                                                    Some
                                                                    uu____2709 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2707;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2726
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2726
                                                                 else None in
                                                               let uu____2728
                                                                 =
                                                                 let uu____2730
                                                                   =
                                                                   let uu____2732
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2732 in
                                                                 FStar_List.append
                                                                   uu____2730
                                                                   sigelts' in
                                                               (uu____2728,
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
                (lex_t1,[],[],t,uu____2755,uu____2756);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2758;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2762);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2764;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2768);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2770;_}::[]
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
                let uu____2809 =
                  let uu____2812 =
                    let uu____2813 =
                      let uu____2818 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2818, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2813 in
                  FStar_Syntax_Syntax.mk uu____2812 in
                uu____2809 None r1 in
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
                  let uu____2838 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2838 in
                let hd1 =
                  let uu____2844 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2844 in
                let tl1 =
                  let uu____2846 =
                    let uu____2847 =
                      let uu____2850 =
                        let uu____2851 =
                          let uu____2856 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2856, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2851 in
                      FStar_Syntax_Syntax.mk uu____2850 in
                    uu____2847 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2846 in
                let res =
                  let uu____2869 =
                    let uu____2872 =
                      let uu____2873 =
                        let uu____2878 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2878,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2873 in
                    FStar_Syntax_Syntax.mk uu____2872 in
                  uu____2869 None r2 in
                let uu____2888 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2888 in
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
              let uu____2910 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2910;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2913 ->
              let uu____2915 =
                let uu____2916 =
                  let uu____2917 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2917 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2916 in
              failwith uu____2915
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
            let uu____2927 = FStar_Syntax_Util.type_u () in
            match uu____2927 with
            | (k,uu____2931) ->
                let phi1 =
                  let uu____2933 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2933
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
          let uu____2943 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2943 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2962 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2962 FStar_List.flatten in
              ((let uu____2970 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2970
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
                          let uu____2976 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2982,uu____2983,uu____2984,uu____2985,uu____2986)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2991 -> failwith "Impossible!" in
                          match uu____2976 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____3000 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____3004,uu____3005,uu____3006,uu____3007,uu____3008)
                        -> lid
                    | uu____3013 -> failwith "Impossible" in
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
                let uu____3019 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____3019
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
                   let uu____3037 =
                     let uu____3039 =
                       let uu____3040 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____3040;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____3039 :: ses1 in
                   (uu____3037, data_ops_ses))))
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3058 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3071 ->
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
           let uu____3101 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3101 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3126 = FStar_Options.set_options t s in
             match uu____3126 with
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
                ((let uu____3143 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3143 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3149 = cps_and_elaborate env1 ne in
           (match uu____3149 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___134_3170 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___134_3170.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___134_3170.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___134_3170.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___135_3171 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___135_3171.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___135_3171.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___135_3171.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___136_3177 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___136_3177.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___136_3177.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___136_3177.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3183 =
             let uu____3188 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3188 in
           (match uu____3183 with
            | (a,wp_a_src) ->
                let uu____3199 =
                  let uu____3204 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3204 in
                (match uu____3199 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3216 =
                         let uu____3218 =
                           let uu____3219 =
                             let uu____3224 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3224) in
                           FStar_Syntax_Syntax.NT uu____3219 in
                         [uu____3218] in
                       FStar_Syntax_Subst.subst uu____3216 wp_b_tgt in
                     let expected_k =
                       let uu____3228 =
                         let uu____3232 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3233 =
                           let uu____3235 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3235] in
                         uu____3232 :: uu____3233 in
                       let uu____3236 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3228 uu____3236 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3257 =
                           let uu____3258 =
                             let uu____3261 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3262 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3261, uu____3262) in
                           FStar_Errors.Error uu____3258 in
                         raise uu____3257 in
                       let uu____3265 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3265 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3284 =
                             let uu____3285 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3285 in
                           if uu____3284
                           then no_reify eff_name
                           else
                             (let uu____3290 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3291 =
                                let uu____3294 =
                                  let uu____3295 =
                                    let uu____3305 =
                                      let uu____3307 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3308 =
                                        let uu____3310 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3310] in
                                      uu____3307 :: uu____3308 in
                                    (repr, uu____3305) in
                                  FStar_Syntax_Syntax.Tm_app uu____3295 in
                                FStar_Syntax_Syntax.mk uu____3294 in
                              uu____3291 None uu____3290) in
                     let uu____3320 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3335,lift_wp)) ->
                           let uu____3348 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3348)
                       | (Some (what,lift),None ) ->
                           ((let uu____3363 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3363
                             then
                               let uu____3364 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3364
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3367 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3367 with
                             | (lift1,comp,uu____3376) ->
                                 let uu____3377 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3377 with
                                  | (uu____3384,lift_wp,lift_elab) ->
                                      let uu____3387 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3388 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3320 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___137_3411 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___137_3411.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___137_3411.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___137_3411.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___137_3411.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___137_3411.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___137_3411.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___137_3411.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___137_3411.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___137_3411.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___137_3411.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___137_3411.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___137_3411.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___137_3411.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___137_3411.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___137_3411.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___137_3411.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___137_3411.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___137_3411.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___137_3411.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___137_3411.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___137_3411.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___137_3411.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___137_3411.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___137_3411.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___137_3411.FStar_TypeChecker_Env.synth)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3415,lift1) ->
                                let uu____3422 =
                                  let uu____3427 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3427 in
                                (match uu____3422 with
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
                                         let uu____3449 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3450 =
                                           let uu____3453 =
                                             let uu____3454 =
                                               let uu____3464 =
                                                 let uu____3466 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3467 =
                                                   let uu____3469 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3469] in
                                                 uu____3466 :: uu____3467 in
                                               (lift_wp1, uu____3464) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3454 in
                                           FStar_Syntax_Syntax.mk uu____3453 in
                                         uu____3450 None uu____3449 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3482 =
                                         let uu____3486 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3487 =
                                           let uu____3489 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3490 =
                                             let uu____3492 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3492] in
                                           uu____3489 :: uu____3490 in
                                         uu____3486 :: uu____3487 in
                                       let uu____3493 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3482
                                         uu____3493 in
                                     let uu____3496 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3496 with
                                      | (expected_k2,uu____3502,uu____3503)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___138_3506 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___138_3506.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___138_3506.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___139_3508 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___139_3508.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___139_3508.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___139_3508.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3521 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3521 with
            | (tps1,c1) ->
                let uu____3530 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3530 with
                 | (tps2,env3,us) ->
                     let uu____3541 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3541 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3555 =
                              let uu____3556 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3556 in
                            match uu____3555 with
                            | (uvs1,t) ->
                                let uu____3569 =
                                  let uu____3577 =
                                    let uu____3580 =
                                      let uu____3581 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3581.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3580) in
                                  match uu____3577 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3591,c4)) -> ([], c4)
                                  | (uu____3615,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3633 -> failwith "Impossible" in
                                (match uu____3569 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3664 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3664 with
                                         | (uu____3667,t1) ->
                                             let uu____3669 =
                                               let uu____3670 =
                                                 let uu____3673 =
                                                   let uu____3674 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3675 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3680 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3674 uu____3675
                                                     uu____3680 in
                                                 (uu____3673, r) in
                                               FStar_Errors.Error uu____3670 in
                                             raise uu____3669)
                                      else ();
                                      (let se1 =
                                         let uu___140_3683 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___140_3683.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___140_3683.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___140_3683.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3693,uu____3694,uu____3695) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___114_3697  ->
                   match uu___114_3697 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3698 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3701,uu____3702,uu____3703) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___114_3709  ->
                   match uu___114_3709 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3710 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3717 =
             if uvs = []
             then
               let uu____3718 =
                 let uu____3719 = FStar_Syntax_Util.type_u () in
                 fst uu____3719 in
               check_and_gen env2 t uu____3718
             else
               (let uu____3723 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3723 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3729 =
                        let uu____3730 = FStar_Syntax_Util.type_u () in
                        fst uu____3730 in
                      tc_check_trivial_guard env2 t1 uu____3729 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3734 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3734)) in
           (match uu____3717 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___141_3744 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_3744.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_3744.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_3744.FStar_Syntax_Syntax.sigmeta)
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
           let uu____3756 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3756 with
            | (e1,c,g1) ->
                let uu____3767 =
                  let uu____3771 =
                    let uu____3773 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3773 in
                  let uu____3774 =
                    let uu____3777 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3777) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3771 uu____3774 in
                (match uu____3767 with
                 | (e2,uu____3787,g) ->
                     ((let uu____3790 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3790);
                      (let se1 =
                         let uu___142_3792 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___142_3792.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___142_3792.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___142_3792.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3828 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3828
                 then Some q
                 else
                   (let uu____3841 =
                      let uu____3842 =
                        let uu____3845 =
                          let uu____3846 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3847 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3848 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3846 uu____3847 uu____3848 in
                        (uu____3845, r) in
                      FStar_Errors.Error uu____3842 in
                    raise uu____3841) in
           let uu____3851 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3872  ->
                     fun lb  ->
                       match uu____3872 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3896 =
                             let uu____3902 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3902 with
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
                                   | uu____3954 ->
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
                                  (let uu____3966 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3966, quals_opt1))) in
                           (match uu____3896 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3851 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____4019 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___115_4021  ->
                                match uu___115_4021 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____4022 -> false)) in
                      if uu____4019
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____4030 =
                    let uu____4033 =
                      let uu____4034 =
                        let uu____4042 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____4042) in
                      FStar_Syntax_Syntax.Tm_let uu____4034 in
                    FStar_Syntax_Syntax.mk uu____4033 in
                  uu____4030 None r in
                let uu____4064 =
                  let uu____4070 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___143_4074 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___143_4074.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___143_4074.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___143_4074.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___143_4074.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___143_4074.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___143_4074.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___143_4074.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___143_4074.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___143_4074.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___143_4074.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___143_4074.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___143_4074.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___143_4074.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___143_4074.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___143_4074.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___143_4074.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___143_4074.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___143_4074.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___143_4074.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___143_4074.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___143_4074.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___143_4074.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___143_4074.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___143_4074.FStar_TypeChecker_Env.synth)
                       }) e in
                  match uu____4070 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4082;
                       FStar_Syntax_Syntax.pos = uu____4083;
                       FStar_Syntax_Syntax.vars = uu____4084;_},uu____4085,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4104,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4109 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___116_4112  ->
                             match uu___116_4112 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4114 =
                                   let uu____4115 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4119 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4119)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4115 in
                                 if uu____4114
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___144_4128 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___144_4128.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___144_4128.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4134 -> failwith "impossible" in
                (match uu____4064 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4161 = log env2 in
                       if uu____4161
                       then
                         let uu____4162 =
                           let uu____4163 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4170 =
                                         let uu____4175 =
                                           let uu____4176 =
                                             let uu____4181 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4181.FStar_Syntax_Syntax.fv_name in
                                           uu____4176.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4175 in
                                       match uu____4170 with
                                       | None  -> true
                                       | uu____4188 -> false in
                                     if should_log
                                     then
                                       let uu____4193 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4194 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4193 uu____4194
                                     else "")) in
                           FStar_All.pipe_right uu____4163
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4162
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4218 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____4218 with
                              | (bs1,c1) ->
                                  let uu____4223 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____4223
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4233 =
                                            let uu____4234 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____4234.FStar_Syntax_Syntax.n in
                                          (match uu____4233 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4253 =
                                                 let uu____4254 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____4254.FStar_Syntax_Syntax.n in
                                               (match uu____4253 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4264 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4264 in
                                                    let uu____4265 =
                                                      let uu____4266 =
                                                        let uu____4267 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4267 args in
                                                      uu____4266 None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4265 u
                                                | uu____4272 -> c1)
                                           | uu____4273 -> c1)
                                      | uu____4274 -> c1 in
                                    let uu___145_4275 = t1 in
                                    let uu____4276 =
                                      let uu____4277 =
                                        let uu____4285 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4285) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4277 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4276;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___145_4275.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___145_4275.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___145_4275.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4307 =
                               let uu____4308 = FStar_Syntax_Subst.compress h in
                               uu____4308.FStar_Syntax_Syntax.n in
                             (match uu____4307 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4318 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4318 in
                                  let uu____4319 =
                                    let uu____4320 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4320
                                      args in
                                  uu____4319 None t1.FStar_Syntax_Syntax.pos
                              | uu____4325 -> t1)
                         | uu____4326 -> t1 in
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
                           let uu____4357 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4357 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4366 =
                                  FStar_Syntax_Syntax.bv_to_name (fst x) in
                                (uu____4366, (snd x))) bs in
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
                           let uu____4398 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4398 in
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
                         let uu___146_4429 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___147_4436 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___147_4436.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___147_4436.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___147_4436.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___147_4436.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids, attrs));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___146_4429.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___146_4429.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___146_4429.FStar_Syntax_Syntax.sigmeta)
                         } in
                       let tactic_decls =
                         match snd lbs1 with
                         | hd1::[] ->
                             let uu____4446 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4446 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4466 =
                                    let uu____4467 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4467.FStar_Syntax_Syntax.n in
                                  (match uu____4466 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4491 =
                                           let uu____4496 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4496.FStar_Syntax_Syntax.fv_name in
                                         uu____4491.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4501 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4501 in
                                       let uu____4502 =
                                         (is_native_tactic assm_lid h1) &&
                                           (let uu____4503 =
                                              let uu____4504 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4504 in
                                            Prims.op_Negation uu____4503) in
                                       if uu____4502
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl (fst lbs1)
                                             hd1 bs assm_lid comp in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4527 -> None))
                         | uu____4530 -> None in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4543 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4543
                             then
                               let uu____4544 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4545 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4544 uu____4545
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
             (fun uu___117_4576  ->
                match uu___117_4576 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4577 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4583) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4587 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4592 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4595 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4608 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4621) ->
          let uu____4626 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4626
          then
            let for_export_bundle se1 uu____4645 =
              match uu____4645 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4668,uu____4669) ->
                       let dec =
                         let uu___148_4675 = se1 in
                         let uu____4676 =
                           let uu____4677 =
                             let uu____4681 =
                               let uu____4684 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4684 in
                             (l, us, uu____4681) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4677 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4676;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___148_4675.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___148_4675.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4694,uu____4695,uu____4696) ->
                       let dec =
                         let uu___149_4700 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___149_4700.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___149_4700.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4703 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4715,uu____4716) ->
          let uu____4717 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4717 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4730 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4730
          then
            ([(let uu___150_4738 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___150_4738.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___150_4738.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4740 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___118_4742  ->
                       match uu___118_4742 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4743 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4746 -> true
                       | uu____4747 -> false)) in
             if uu____4740 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4757 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4760 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4763 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4766 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4769 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4779,uu____4780)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4796 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4796
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4817) ->
          let uu____4822 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4822
          then
            let uu____4827 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___151_4833 = se in
                      let uu____4834 =
                        let uu____4835 =
                          let uu____4839 =
                            let uu____4840 =
                              let uu____4845 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4845.FStar_Syntax_Syntax.fv_name in
                            uu____4840.FStar_Syntax_Syntax.v in
                          (uu____4839, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4835 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4834;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___151_4833.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___151_4833.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4827, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4863 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4872 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4881 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4884 = FStar_Options.using_facts_from () in
                 match uu____4884 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4896 =
                         let uu____4901 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4901 [([], false)] in
                       [uu____4896] in
                     let uu___152_4929 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___152_4929.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___152_4929.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___152_4929.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___152_4929.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___152_4929.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___152_4929.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___152_4929.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___152_4929.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___152_4929.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___152_4929.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___152_4929.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___152_4929.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___152_4929.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___152_4929.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___152_4929.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___152_4929.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___152_4929.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___152_4929.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___152_4929.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___152_4929.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___152_4929.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___152_4929.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___152_4929.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___152_4929.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___152_4929.FStar_TypeChecker_Env.synth)
                     }
                 | None  -> env))
           | uu____4931 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4932 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4938 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4938) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4939,uu____4940,uu____4941) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_4943  ->
                  match uu___119_4943 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4944 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4945,uu____4946,uu____4947) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_4953  ->
                  match uu___119_4953 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4954 -> false))
          -> env
      | uu____4955 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4991 se =
        match uu____4991 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5021 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____5021
              then
                let uu____5022 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5022
              else ());
             (let uu____5024 = tc_decl env1 se in
              match uu____5024 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____5050 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____5050
                    then
                      let uu____5051 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____5054 =
                                 let uu____5055 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____5055 "\n" in
                               Prims.strcat s uu____5054) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____5051
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____5059 =
                      let accum_exports_hidden uu____5077 se1 =
                        match uu____5077 with
                        | (exports1,hidden1) ->
                            let uu____5093 = for_export hidden1 se1 in
                            (match uu____5093 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____5059 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____5143 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____5143 with
      | (ses1,exports,env1,uu____5169) ->
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
      (let uu____5194 = FStar_Options.debug_any () in
       if uu____5194
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
         let uu___153_5200 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___153_5200.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___153_5200.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___153_5200.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___153_5200.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___153_5200.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___153_5200.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___153_5200.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___153_5200.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___153_5200.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___153_5200.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___153_5200.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___153_5200.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___153_5200.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___153_5200.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___153_5200.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___153_5200.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___153_5200.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___153_5200.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___153_5200.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___153_5200.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___153_5200.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___153_5200.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___153_5200.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___153_5200.FStar_TypeChecker_Env.synth)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____5203 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5203 with
        | (ses,exports,env3) ->
            ((let uu___154_5221 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___154_5221.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___154_5221.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___154_5221.FStar_Syntax_Syntax.is_interface)
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
        let uu____5237 = tc_decls env decls in
        match uu____5237 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___155_5255 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___155_5255.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___155_5255.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___155_5255.FStar_Syntax_Syntax.is_interface)
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
          let uu___156_5269 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___156_5269.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___156_5269.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___156_5269.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___156_5269.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___156_5269.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___156_5269.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___156_5269.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___156_5269.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___156_5269.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___156_5269.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___156_5269.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___156_5269.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___156_5269.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___156_5269.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___156_5269.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___156_5269.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___156_5269.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___156_5269.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___156_5269.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___156_5269.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___156_5269.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___156_5269.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___156_5269.FStar_TypeChecker_Env.synth)
          } in
        let check_term lid univs1 t =
          let uu____5280 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5280 with
          | (univs2,t1) ->
              ((let uu____5286 =
                  let uu____5287 =
                    let uu____5290 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5290 in
                  FStar_All.pipe_left uu____5287
                    (FStar_Options.Other "Exports") in
                if uu____5286
                then
                  let uu____5291 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5292 =
                    let uu____5293 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5293
                      (FStar_String.concat ", ") in
                  let uu____5298 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5291 uu____5292 uu____5298
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5301 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5301 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5319 =
             let uu____5320 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5321 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5320 uu____5321 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5319);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5328) ->
              let uu____5333 =
                let uu____5334 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5334 in
              if uu____5333
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5342,uu____5343) ->
              let t =
                let uu____5351 =
                  let uu____5354 =
                    let uu____5355 =
                      let uu____5363 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5363) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5355 in
                  FStar_Syntax_Syntax.mk uu____5354 in
                uu____5351 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5375,uu____5376,uu____5377) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5383 =
                let uu____5384 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5384 in
              if uu____5383 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5387,lbs),uu____5389,uu____5390) ->
              let uu____5400 =
                let uu____5401 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5401 in
              if uu____5400
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
              let uu____5418 =
                let uu____5419 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5419 in
              if uu____5418
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5433 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5434 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5437 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5438 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5439 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5440 -> () in
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
          let uu___157_5454 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___157_5454.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___157_5454.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5457 =
           let uu____5458 = FStar_Options.lax () in
           Prims.op_Negation uu____5458 in
         if uu____5457 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5464 =
           let uu____5465 = FStar_Options.interactive () in
           Prims.op_Negation uu____5465 in
         if uu____5464
         then
           let uu____5466 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5466 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5476 = tc_partial_modul env modul in
      match uu____5476 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5497 = FStar_Options.debug_any () in
       if uu____5497
       then
         let uu____5498 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5498
       else ());
      (let env1 =
         let uu___158_5502 = env in
         let uu____5503 =
           let uu____5504 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5504 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___158_5502.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___158_5502.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___158_5502.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___158_5502.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___158_5502.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___158_5502.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___158_5502.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___158_5502.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___158_5502.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___158_5502.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___158_5502.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___158_5502.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___158_5502.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___158_5502.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___158_5502.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___158_5502.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___158_5502.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___158_5502.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5503;
           FStar_TypeChecker_Env.lax_universes =
             (uu___158_5502.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___158_5502.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___158_5502.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___158_5502.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___158_5502.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___158_5502.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___158_5502.FStar_TypeChecker_Env.synth)
         } in
       let uu____5505 = tc_modul env1 m in
       match uu____5505 with
       | (m1,env2) ->
           ((let uu____5513 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5513
             then
               let uu____5514 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5514
             else ());
            (let uu____5517 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5517
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
                       let uu____5544 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5544 with
                       | (univnames1,e) ->
                           let uu___159_5549 = lb in
                           let uu____5550 =
                             let uu____5553 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5553 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___159_5549.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___159_5549.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___159_5549.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___159_5549.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5550
                           } in
                     let uu___160_5554 = se in
                     let uu____5555 =
                       let uu____5556 =
                         let uu____5562 =
                           let uu____5566 = FStar_List.map update lbs in
                           (b, uu____5566) in
                         (uu____5562, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5556 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5555;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___160_5554.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___160_5554.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___160_5554.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5574 -> se in
               let normalized_module =
                 let uu___161_5576 = m1 in
                 let uu____5577 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___161_5576.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5577;
                   FStar_Syntax_Syntax.exports =
                     (uu___161_5576.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___161_5576.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5578 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5578
             else ());
            (m1, env2)))