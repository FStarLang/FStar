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
          let uu___126_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___126_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___126_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___126_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___126_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___126_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___126_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___126_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___126_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___126_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___126_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___126_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___126_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___126_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___126_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___126_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___126_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___126_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___126_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___126_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___126_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___126_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___126_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___126_12.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___126_12.FStar_TypeChecker_Env.proof_ns)
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
          let uu___127_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___127_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___127_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___127_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___127_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___127_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___127_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___127_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___127_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___127_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___127_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___127_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___127_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___127_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___127_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___127_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___127_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___127_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___127_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___127_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___127_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___127_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___127_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___127_24.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___127_24.FStar_TypeChecker_Env.proof_ns)
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
        let fail1 uu____149 =
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
             | uu____193 -> fail1 ())
        | uu____194 -> fail1 ()
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
                      let uu___128_276 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___128_276.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___128_276.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___128_276.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___128_276.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___128_276.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___128_276.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___128_276.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___128_276.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___128_276.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___128_276.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___128_276.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___128_276.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___128_276.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___128_276.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___128_276.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___128_276.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___128_276.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____280 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts) in
                            ([], t1) in
                          let uu___129_298 = ed1 in
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
                            Prims.snd uu____310 in
                          let uu____316 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____317 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____318 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___130_321 = a in
                                 let uu____322 =
                                   let uu____323 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   Prims.snd uu____323 in
                                 let uu____329 =
                                   let uu____330 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   Prims.snd uu____330 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___130_321.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___130_321.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___130_321.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___130_321.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____322;
                                   FStar_Syntax_Syntax.action_typ = uu____329
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___129_298.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___129_298.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___129_298.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___129_298.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___129_298.FStar_Syntax_Syntax.signature);
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
                      let fail1 t =
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
                           | uu____404 -> fail1 signature1)
                      | uu____405 -> fail1 signature1 in
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
                                 FStar_All.pipe_right uu____531 Prims.fst in
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
                                 FStar_All.pipe_right uu____597 Prims.fst in
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
                                         Prims.fst in
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
                                         Prims.fst in
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
                                                 Prims.snd in
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
                                                (Prims.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___131_984 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___131_984.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___131_984.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___131_984.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___131_984.FStar_TypeChecker_Env.proof_ns)
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
                                             Prims.snd in
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
                                           (Prims.snd
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
                                           let uu___132_1076 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___132_1076.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___132_1076.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___132_1076.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___132_1076.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___132_1076.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___132_1076.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___132_1076.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___132_1076.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___132_1076.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___132_1076.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___132_1076.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___132_1076.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___132_1076.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___132_1076.FStar_TypeChecker_Env.proof_ns)
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
                                                          let uu___133_1220 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___133_1220.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___133_1220.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___133_1220.FStar_Syntax_Syntax.action_params);
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
                                      let m =
                                        FStar_List.length (Prims.fst ts1) in
                                      (let uu____1287 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1288 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts1) in
                                             Prims.op_Negation uu____1288))
                                           && (m <> n1) in
                                       if uu____1287
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1297 =
                                           let uu____1298 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1299 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1298 uu____1299 in
                                         failwith uu____1297
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1305 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1305 with
                                      | (univs2,defn) ->
                                          let uu____1310 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1310 with
                                           | (univs',typ) ->
                                               let uu___134_1316 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___134_1316.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___134_1316.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___134_1316.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___135_1319 = ed2 in
                                      let uu____1320 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1321 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1322 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1323 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1324 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1325 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1326 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1327 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1328 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1329 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1330 =
                                        let uu____1331 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        Prims.snd uu____1331 in
                                      let uu____1337 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1338 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1339 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___135_1319.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___135_1319.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1320;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1321;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1322;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1323;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1324;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1325;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1326;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1327;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1328;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1329;
                                        FStar_Syntax_Syntax.repr = uu____1330;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1337;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1338;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1339
                                      } in
                                    ((let uu____1342 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1342
                                      then
                                        let uu____1343 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1343
                                      else ());
                                     ed3)))))))
and cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.eff_decl*
        FStar_Syntax_Syntax.sigelt Prims.option)
  =
  fun env  ->
    fun ed  ->
      let uu____1347 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1347 with
      | (effect_binders_un,signature_un) ->
          let uu____1357 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1357 with
           | (effect_binders,env1,uu____1368) ->
               let uu____1369 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1369 with
                | (signature,uu____1378) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1387  ->
                           match uu____1387 with
                           | (bv,qual) ->
                               let uu____1394 =
                                 let uu___136_1395 = bv in
                                 let uu____1396 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___136_1395.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___136_1395.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1396
                                 } in
                               (uu____1394, qual)) effect_binders in
                    let uu____1399 =
                      let uu____1404 =
                        let uu____1405 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1405.FStar_Syntax_Syntax.n in
                      match uu____1404 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1413)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1428 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1399 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1445 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1445
                           then
                             let uu____1446 =
                               let uu____1448 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1448 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1446
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1472 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1472 with
                           | (t2,comp,uu____1480) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1491 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1491 with
                          | (repr,_comp) ->
                              ((let uu____1504 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1504
                                then
                                  let uu____1505 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1505
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
                                  let uu____1511 =
                                    let uu____1512 =
                                      let uu____1513 =
                                        let uu____1523 =
                                          let uu____1527 =
                                            let uu____1530 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1531 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1530, uu____1531) in
                                          [uu____1527] in
                                        (wp_type1, uu____1523) in
                                      FStar_Syntax_Syntax.Tm_app uu____1513 in
                                    mk1 uu____1512 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1511 in
                                let effect_signature =
                                  let binders =
                                    let uu____1546 =
                                      let uu____1549 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1549) in
                                    let uu____1550 =
                                      let uu____1554 =
                                        let uu____1555 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1555
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1554] in
                                    uu____1546 :: uu____1550 in
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
                                  let uu____1598 = item in
                                  match uu____1598 with
                                  | (u_item,item1) ->
                                      let uu____1610 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1610 with
                                       | (item2,item_comp) ->
                                           ((let uu____1620 =
                                               let uu____1621 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1621 in
                                             if uu____1620
                                             then
                                               let uu____1622 =
                                                 let uu____1623 =
                                                   let uu____1624 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1625 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1624 uu____1625 in
                                                 FStar_Errors.Err uu____1623 in
                                               raise uu____1622
                                             else ());
                                            (let uu____1627 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1627 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1640 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1640 with
                                | (dmff_env1,uu____1653,bind_wp,bind_elab) ->
                                    let uu____1656 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1656 with
                                     | (dmff_env2,uu____1669,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1673 =
                                             let uu____1674 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1674.FStar_Syntax_Syntax.n in
                                           match uu____1673 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1712 =
                                                 let uu____1720 =
                                                   let uu____1723 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1723 in
                                                 match uu____1720 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1762 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1712 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1784 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1784 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1795 =
                                                          let uu____1796 =
                                                            let uu____1806 =
                                                              let uu____1810
                                                                =
                                                                let uu____1813
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    Prims.fst
                                                                    b11) in
                                                                let uu____1814
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1813,
                                                                  uu____1814) in
                                                              [uu____1810] in
                                                            (wp_type1,
                                                              uu____1806) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1796 in
                                                        mk1 uu____1795 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1822 =
                                                      let uu____1832 =
                                                        let uu____1833 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1833 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1832 in
                                                    (match uu____1822 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____1861
                                                           =
                                                           let error_msg =
                                                             let uu____1863 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1864 =
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
                                                                   (lid,uu____1880))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1863
                                                               uu____1864 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  ->
                                                               fail1 ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1906
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1906
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
                                                                    fail1 ())
                                                               else fail1 ()
                                                           | Some
                                                               (FStar_Util.Inr
                                                               (lid,uu____1912))
                                                               ->
                                                               if
                                                                 Prims.op_Negation
                                                                   (FStar_Syntax_Util.is_pure_effect
                                                                    lid)
                                                               then fail1 ()
                                                               else ());
                                                          (let wp =
                                                             let t2 =
                                                               (Prims.fst b21).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp" None
                                                               pure_wp_type in
                                                           let body3 =
                                                             let uu____1932 =
                                                               let uu____1933
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1934
                                                                 =
                                                                 let uu____1935
                                                                   =
                                                                   let uu____1939
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1939,
                                                                    None) in
                                                                 [uu____1935] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1933
                                                                 uu____1934 in
                                                             uu____1932 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1955 =
                                                             let uu____1956 =
                                                               let uu____1960
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1960] in
                                                             b11 ::
                                                               uu____1956 in
                                                           let uu____1963 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1955
                                                             uu____1963
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1973 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1975 =
                                             let uu____1976 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1976.FStar_Syntax_Syntax.n in
                                           match uu____1975 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2014 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2014
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2030 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2032 =
                                             let uu____2033 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2033.FStar_Syntax_Syntax.n in
                                           match uu____2032 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2062 =
                                                 let uu____2063 =
                                                   let uu____2065 =
                                                     let uu____2066 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2066 in
                                                   [uu____2065] in
                                                 FStar_List.append uu____2063
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2062 body what
                                           | uu____2067 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2085 =
                                                let uu____2086 =
                                                  let uu____2087 =
                                                    let uu____2097 =
                                                      let uu____2098 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      Prims.snd uu____2098 in
                                                    (t, uu____2097) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2087 in
                                                mk1 uu____2086 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2085) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2121 = f a2 in
                                               [uu____2121]
                                           | x::xs ->
                                               let uu____2125 =
                                                 apply_last1 f xs in
                                               x :: uu____2125 in
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
                                           let uu____2140 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2140 with
                                           | Some (_us,_t) ->
                                               ((let uu____2157 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2157
                                                 then
                                                   let uu____2158 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2158
                                                 else ());
                                                (let uu____2160 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2160))
                                           | None  ->
                                               let uu____2165 =
                                                 let uu____2168 = mk_lid name in
                                                 let uu____2169 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2168 uu____2169 in
                                               (match uu____2165 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2178 =
                                                        let uu____2180 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2180 in
                                                      FStar_ST.write sigelts
                                                        uu____2178);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2191 =
                                             let uu____2193 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2194 =
                                               FStar_ST.read sigelts in
                                             uu____2193 :: uu____2194 in
                                           FStar_ST.write sigelts uu____2191);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2204 =
                                              let uu____2206 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2207 =
                                                FStar_ST.read sigelts in
                                              uu____2206 :: uu____2207 in
                                            FStar_ST.write sigelts uu____2204);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2217 =
                                               let uu____2219 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2220 =
                                                 FStar_ST.read sigelts in
                                               uu____2219 :: uu____2220 in
                                             FStar_ST.write sigelts
                                               uu____2217);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2230 =
                                                let uu____2232 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2233 =
                                                  FStar_ST.read sigelts in
                                                uu____2232 :: uu____2233 in
                                              FStar_ST.write sigelts
                                                uu____2230);
                                             (let uu____2241 =
                                                FStar_List.fold_left
                                                  (fun uu____2248  ->
                                                     fun action  ->
                                                       match uu____2248 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2261 =
                                                             let uu____2265 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2265
                                                               params_un in
                                                           (match uu____2261
                                                            with
                                                            | (action_params,env',uu____2271)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2280
                                                                     ->
                                                                    match uu____2280
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2287
                                                                    =
                                                                    let uu___137_2288
                                                                    = bv in
                                                                    let uu____2289
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___137_2288.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___137_2288.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2289
                                                                    } in
                                                                    (uu____2287,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2293
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2293
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
                                                                    uu____2319
                                                                    ->
                                                                    let uu____2320
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2320 in
                                                                    ((
                                                                    let uu____2324
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2324
                                                                    then
                                                                    let uu____2325
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2326
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2327
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2328
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2325
                                                                    uu____2326
                                                                    uu____2327
                                                                    uu____2328
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
                                                                    let uu____2332
                                                                    =
                                                                    let uu____2334
                                                                    =
                                                                    let uu___138_2335
                                                                    = action in
                                                                    let uu____2336
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2337
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___138_2335.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___138_2335.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___138_2335.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2336;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2337
                                                                    } in
                                                                    uu____2334
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2332))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2241 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2357 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2358 =
                                                        let uu____2360 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2360] in
                                                      uu____2357 ::
                                                        uu____2358 in
                                                    let uu____2361 =
                                                      let uu____2362 =
                                                        let uu____2363 =
                                                          let uu____2364 =
                                                            let uu____2374 =
                                                              let uu____2378
                                                                =
                                                                let uu____2381
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2382
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2381,
                                                                  uu____2382) in
                                                              [uu____2378] in
                                                            (repr,
                                                              uu____2374) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2364 in
                                                        mk1 uu____2363 in
                                                      let uu____2390 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2362
                                                        uu____2390 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2361 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2398 =
                                                    let uu____2403 =
                                                      let uu____2404 =
                                                        let uu____2407 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2407 in
                                                      uu____2404.FStar_Syntax_Syntax.n in
                                                    match uu____2403 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2415)
                                                        ->
                                                        let uu____2442 =
                                                          let uu____2451 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2451
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2482 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2442
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2510 =
                                                               let uu____2511
                                                                 =
                                                                 let uu____2514
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2514 in
                                                               uu____2511.FStar_Syntax_Syntax.n in
                                                             (match uu____2510
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2531
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2531
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2540
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2551
                                                                     ->
                                                                    match uu____2551
                                                                    with
                                                                    | 
                                                                    (bv,uu____2555)
                                                                    ->
                                                                    let uu____2556
                                                                    =
                                                                    let uu____2557
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2557
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2556
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2540
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
                                                                    uu____2590
                                                                    ->
                                                                    let uu____2594
                                                                    =
                                                                    let uu____2595
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2595 in
                                                                    failwith
                                                                    uu____2594 in
                                                                    let uu____2598
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2601
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2598,
                                                                    uu____2601)))
                                                              | uu____2611 ->
                                                                  let uu____2612
                                                                    =
                                                                    let uu____2613
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2613 in
                                                                  failwith
                                                                    uu____2612))
                                                    | uu____2618 ->
                                                        let uu____2619 =
                                                          let uu____2620 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2620 in
                                                        failwith uu____2619 in
                                                  (match uu____2398 with
                                                   | (pre,post) ->
                                                       ((let uu____2637 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2639 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2641 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___139_2643
                                                             = ed in
                                                           let uu____2644 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2645 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2646 =
                                                             let uu____2647 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2647) in
                                                           let uu____2653 =
                                                             let uu____2654 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2654) in
                                                           let uu____2660 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2661 =
                                                             let uu____2662 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2662) in
                                                           let uu____2668 =
                                                             let uu____2669 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2669) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2644;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2645;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2646;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2653;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___139_2643.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2660;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2661;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2668;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2675 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2675
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2686
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2686
                                                               then
                                                                 let uu____2687
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2687
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
                                                                    let uu____2697
                                                                    =
                                                                    let uu____2699
                                                                    =
                                                                    let uu____2705
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2705) in
                                                                    Some
                                                                    uu____2699 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2697;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2716
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2716
                                                                 else None in
                                                               let uu____2718
                                                                 =
                                                                 let uu____2720
                                                                   =
                                                                   let uu____2722
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2722 in
                                                                 FStar_List.append
                                                                   uu____2720
                                                                   sigelts' in
                                                               (uu____2718,
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
                (lex_t1,[],[],t,uu____2745,uu____2746);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2748;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_29,uu____2752);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2754;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_30,uu____2758);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2760;_}::[]
              when
              ((_0_29 = (Prims.parse_int "0")) &&
                 (_0_30 = (Prims.parse_int "0")))
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
                let uu____2799 =
                  let uu____2802 =
                    let uu____2803 =
                      let uu____2808 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2808, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2803 in
                  FStar_Syntax_Syntax.mk uu____2802 in
                uu____2799 None r1 in
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
                  let uu____2828 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2828 in
                let hd1 =
                  let uu____2834 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2834 in
                let tl1 =
                  let uu____2836 =
                    let uu____2837 =
                      let uu____2840 =
                        let uu____2841 =
                          let uu____2846 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2846, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2841 in
                      FStar_Syntax_Syntax.mk uu____2840 in
                    uu____2837 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2836 in
                let res =
                  let uu____2859 =
                    let uu____2862 =
                      let uu____2863 =
                        let uu____2868 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2868,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2863 in
                    FStar_Syntax_Syntax.mk uu____2862 in
                  uu____2859 None r2 in
                let uu____2878 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2878 in
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
              let uu____2900 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2900;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2903 ->
              let uu____2905 =
                let uu____2906 =
                  let uu____2907 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2907 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2906 in
              failwith uu____2905
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
            let uu____2917 = FStar_Syntax_Util.type_u () in
            match uu____2917 with
            | (k,uu____2921) ->
                let phi1 =
                  let uu____2923 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2923
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
          let uu____2933 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2933 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2952 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2952 FStar_List.flatten in
              ((let uu____2960 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2960
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
                          let uu____2966 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2972,uu____2973,uu____2974,uu____2975,uu____2976)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2981 -> failwith "Impossible!" in
                          match uu____2966 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2990 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2994,uu____2995,uu____2996,uu____2997,uu____2998)
                        -> lid
                    | uu____3003 -> failwith "Impossible" in
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
                let uu____3009 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____3009
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
                   let uu____3025 =
                     let uu____3027 =
                       let uu____3028 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____3028;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____3027 :: ses1 in
                   (uu____3025, data_ops_ses))))
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
       | FStar_Syntax_Syntax.Sig_inductive_typ _
         |FStar_Syntax_Syntax.Sig_datacon _ ->
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
           let uu____3070 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3070 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3095 = FStar_Options.set_options t s in
             match uu____3095 with
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
                ((let uu____3112 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3112 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3118 = cps_and_elaborate env1 ne in
           (match uu____3118 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___140_3139 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___140_3139.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___140_3139.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___140_3139.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___141_3140 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___141_3140.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___141_3140.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___141_3140.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___142_3146 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___142_3146.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___142_3146.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___142_3146.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3152 =
             let uu____3157 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3157 in
           (match uu____3152 with
            | (a,wp_a_src) ->
                let uu____3168 =
                  let uu____3173 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3173 in
                (match uu____3168 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3185 =
                         let uu____3187 =
                           let uu____3188 =
                             let uu____3193 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3193) in
                           FStar_Syntax_Syntax.NT uu____3188 in
                         [uu____3187] in
                       FStar_Syntax_Subst.subst uu____3185 wp_b_tgt in
                     let expected_k =
                       let uu____3197 =
                         let uu____3201 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3202 =
                           let uu____3204 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3204] in
                         uu____3201 :: uu____3202 in
                       let uu____3205 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3197 uu____3205 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3226 =
                           let uu____3227 =
                             let uu____3230 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3231 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3230, uu____3231) in
                           FStar_Errors.Error uu____3227 in
                         raise uu____3226 in
                       let uu____3234 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3234 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3253 =
                             let uu____3254 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3254 in
                           if uu____3253
                           then no_reify eff_name
                           else
                             (let uu____3259 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3260 =
                                let uu____3263 =
                                  let uu____3264 =
                                    let uu____3274 =
                                      let uu____3276 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3277 =
                                        let uu____3279 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3279] in
                                      uu____3276 :: uu____3277 in
                                    (repr, uu____3274) in
                                  FStar_Syntax_Syntax.Tm_app uu____3264 in
                                FStar_Syntax_Syntax.mk uu____3263 in
                              uu____3260 None uu____3259) in
                     let uu____3289 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3304,lift_wp)) ->
                           let uu____3317 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3317)
                       | (Some (what,lift),None ) ->
                           ((let uu____3332 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3332
                             then
                               let uu____3333 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3333
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3336 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3336 with
                             | (lift1,comp,uu____3345) ->
                                 let uu____3346 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3346 with
                                  | (uu____3353,lift_wp,lift_elab) ->
                                      let uu____3356 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3357 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3289 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___143_3380 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___143_3380.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___143_3380.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___143_3380.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___143_3380.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___143_3380.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___143_3380.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___143_3380.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___143_3380.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___143_3380.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___143_3380.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___143_3380.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___143_3380.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___143_3380.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___143_3380.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___143_3380.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___143_3380.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___143_3380.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___143_3380.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___143_3380.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___143_3380.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___143_3380.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___143_3380.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___143_3380.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___143_3380.FStar_TypeChecker_Env.proof_ns)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3384,lift1) ->
                                let uu____3391 =
                                  let uu____3396 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3396 in
                                (match uu____3391 with
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
                                           env2 (Prims.snd lift_wp) in
                                       let lift_wp_a =
                                         let uu____3418 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3419 =
                                           let uu____3422 =
                                             let uu____3423 =
                                               let uu____3433 =
                                                 let uu____3435 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3436 =
                                                   let uu____3438 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3438] in
                                                 uu____3435 :: uu____3436 in
                                               (lift_wp1, uu____3433) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3423 in
                                           FStar_Syntax_Syntax.mk uu____3422 in
                                         uu____3419 None uu____3418 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3451 =
                                         let uu____3455 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3456 =
                                           let uu____3458 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3459 =
                                             let uu____3461 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3461] in
                                           uu____3458 :: uu____3459 in
                                         uu____3455 :: uu____3456 in
                                       let uu____3462 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3451
                                         uu____3462 in
                                     let uu____3465 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3465 with
                                      | (expected_k2,uu____3471,uu____3472)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___144_3475 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___144_3475.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___144_3475.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___145_3477 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___145_3477.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___145_3477.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___145_3477.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3490 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3490 with
            | (tps1,c1) ->
                let uu____3499 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3499 with
                 | (tps2,env3,us) ->
                     let uu____3510 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3510 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3524 =
                              let uu____3525 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3525 in
                            match uu____3524 with
                            | (uvs1,t) ->
                                let uu____3538 =
                                  let uu____3546 =
                                    let uu____3549 =
                                      let uu____3550 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3550.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3549) in
                                  match uu____3546 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3560,c4)) -> ([], c4)
                                  | (uu____3584,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3602 -> failwith "Impossible" in
                                (match uu____3538 with
                                 | (tps4,c4) ->
                                     (if
                                        ((FStar_List.length uvs1) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3631 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3631 with
                                         | (uu____3634,t1) ->
                                             let uu____3636 =
                                               let uu____3637 =
                                                 let uu____3640 =
                                                   let uu____3641 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3642 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3645 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3641 uu____3642
                                                     uu____3645 in
                                                 (uu____3640, r) in
                                               FStar_Errors.Error uu____3637 in
                                             raise uu____3636)
                                      else ();
                                      (let se1 =
                                         let uu___146_3648 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___146_3648.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___146_3648.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___146_3648.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_)
         |FStar_Syntax_Syntax.Sig_let (_,_,_) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___120_3667  ->
                   match uu___120_3667 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3668 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3675 =
             if uvs = []
             then
               let uu____3676 =
                 let uu____3677 = FStar_Syntax_Util.type_u () in
                 Prims.fst uu____3677 in
               check_and_gen env2 t uu____3676
             else
               (let uu____3681 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3681 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3687 =
                        let uu____3688 = FStar_Syntax_Util.type_u () in
                        Prims.fst uu____3688 in
                      tc_check_trivial_guard env2 t1 uu____3687 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3692 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3692)) in
           (match uu____3675 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___147_3702 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___147_3702.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___147_3702.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___147_3702.FStar_Syntax_Syntax.sigmeta)
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
           let uu____3714 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3714 with
            | (e1,c,g1) ->
                let uu____3725 =
                  let uu____3729 =
                    let uu____3731 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3731 in
                  let uu____3732 =
                    let uu____3735 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3735) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3729 uu____3732 in
                (match uu____3725 with
                 | (e2,uu____3745,g) ->
                     ((let uu____3748 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3748);
                      (let se1 =
                         let uu___148_3750 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___148_3750.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___148_3750.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___148_3750.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3786 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3786
                 then Some q
                 else
                   (let uu____3795 =
                      let uu____3796 =
                        let uu____3799 =
                          let uu____3800 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3801 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3802 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3800 uu____3801 uu____3802 in
                        (uu____3799, r) in
                      FStar_Errors.Error uu____3796 in
                    raise uu____3795) in
           let uu____3805 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3826  ->
                     fun lb  ->
                       match uu____3826 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3850 =
                             let uu____3856 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3856 with
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
                                   | uu____3908 ->
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
                                  (let uu____3916 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3916, quals_opt1))) in
                           (match uu____3850 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3805 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3969 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___121_3971  ->
                                match uu___121_3971 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3972 -> false)) in
                      if uu____3969
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____3980 =
                    let uu____3983 =
                      let uu____3984 =
                        let uu____3992 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((Prims.fst lbs), lbs'1), uu____3992) in
                      FStar_Syntax_Syntax.Tm_let uu____3984 in
                    FStar_Syntax_Syntax.mk uu____3983 in
                  uu____3980 None r in
                let uu____4014 =
                  let uu____4020 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___149_4024 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___149_4024.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___149_4024.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___149_4024.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___149_4024.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___149_4024.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___149_4024.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___149_4024.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___149_4024.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___149_4024.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___149_4024.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___149_4024.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___149_4024.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___149_4024.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___149_4024.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___149_4024.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___149_4024.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___149_4024.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___149_4024.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___149_4024.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___149_4024.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___149_4024.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___149_4024.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___149_4024.FStar_TypeChecker_Env.proof_ns)
                       }) e in
                  match uu____4020 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4032;
                       FStar_Syntax_Syntax.pos = uu____4033;
                       FStar_Syntax_Syntax.vars = uu____4034;_},uu____4035,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4054,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4059 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___122_4062  ->
                             match uu___122_4062 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4064 =
                                   let uu____4065 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4069 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4069)
                                          else ();
                                          ok) (Prims.snd lbs1) in
                                   Prims.op_Negation uu____4065 in
                                 if uu____4064
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___150_4078 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___150_4078.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___150_4078.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4084 -> failwith "impossible" in
                (match uu____4014 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (Prims.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4111 = log env2 in
                       if uu____4111
                       then
                         let uu____4112 =
                           let uu____4113 =
                             FStar_All.pipe_right (Prims.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4120 =
                                         let uu____4125 =
                                           let uu____4126 =
                                             let uu____4131 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4131.FStar_Syntax_Syntax.fv_name in
                                           uu____4126.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4125 in
                                       match uu____4120 with
                                       | None  -> true
                                       | uu____4138 -> false in
                                     if should_log
                                     then
                                       let uu____4143 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4144 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4143 uu____4144
                                     else "")) in
                           FStar_All.pipe_right uu____4113
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4112
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4168 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____4168 with
                              | (bs1,c1) ->
                                  let uu____4173 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____4173
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4183 =
                                            let uu____4184 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____4184.FStar_Syntax_Syntax.n in
                                          (match uu____4183 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4203 =
                                                 let uu____4204 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____4204.FStar_Syntax_Syntax.n in
                                               (match uu____4203 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4214 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4214 in
                                                    let uu____4215 =
                                                      let uu____4216 =
                                                        let uu____4217 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4217 args in
                                                      uu____4216 None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4215 u
                                                | uu____4222 -> c1)
                                           | uu____4223 -> c1)
                                      | uu____4224 -> c1 in
                                    let uu___151_4225 = t1 in
                                    let uu____4226 =
                                      let uu____4227 =
                                        let uu____4235 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4235) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4227 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4226;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___151_4225.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___151_4225.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___151_4225.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4257 =
                               let uu____4258 = FStar_Syntax_Subst.compress h in
                               uu____4258.FStar_Syntax_Syntax.n in
                             (match uu____4257 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4268 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4268 in
                                  let uu____4269 =
                                    let uu____4270 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4270
                                      args in
                                  uu____4269 None t1.FStar_Syntax_Syntax.pos
                              | uu____4275 -> t1)
                         | uu____4276 -> t1 in
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
                           let uu____4307 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4307 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4316 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (Prims.fst x) in
                                (uu____4316, (Prims.snd x))) bs in
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
                           let uu____4348 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4348 in
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
                         let uu___152_4379 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___153_4386 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___153_4386.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___153_4386.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___153_4386.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___153_4386.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids, attrs));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___152_4379.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___152_4379.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___152_4379.FStar_Syntax_Syntax.sigmeta)
                         } in
                       let tactic_decls =
                         match Prims.snd lbs1 with
                         | hd1::[] ->
                             let uu____4396 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4396 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4416 =
                                    let uu____4417 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4417.FStar_Syntax_Syntax.n in
                                  (match uu____4416 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4441 =
                                           let uu____4446 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4446.FStar_Syntax_Syntax.fv_name in
                                         uu____4441.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4451 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4451 in
                                       let uu____4452 =
                                         (is_native_tactic assm_lid h1) &&
                                           (let uu____4453 =
                                              let uu____4454 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4454 in
                                            Prims.op_Negation uu____4453) in
                                       if uu____4452
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl
                                             (Prims.fst lbs1) hd1 bs assm_lid
                                             comp in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4477 -> None))
                         | uu____4480 -> None in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4493 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4493
                             then
                               let uu____4494 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4495 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4494 uu____4495
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
             (fun uu___123_4526  ->
                match uu___123_4526 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4527 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4535 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4540 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4550) ->
          let uu____4555 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4555
          then
            let for_export_bundle se1 uu____4574 =
              match uu____4574 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4597,uu____4598) ->
                       let dec =
                         let uu___154_4604 = se1 in
                         let uu____4605 =
                           let uu____4606 =
                             let uu____4610 =
                               let uu____4613 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4613 in
                             (l, us, uu____4610) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4606 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4605;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___154_4604.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___154_4604.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4623,uu____4624,uu____4625) ->
                       let dec =
                         let uu___155_4629 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___155_4629.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___155_4629.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4632 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4644,uu____4645) ->
          let uu____4646 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4646 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4659 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4659
          then
            ([(let uu___156_4667 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___156_4667.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___156_4667.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4669 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___124_4671  ->
                       match uu___124_4671 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____4674 -> false)) in
             if uu____4669 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4684 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4694,uu____4695)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4711 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4711
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4732) ->
          let uu____4737 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4737
          then
            let uu____4742 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___157_4748 = se in
                      let uu____4749 =
                        let uu____4750 =
                          let uu____4754 =
                            let uu____4755 =
                              let uu____4760 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4760.FStar_Syntax_Syntax.fv_name in
                            uu____4755.FStar_Syntax_Syntax.v in
                          (uu____4754, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4750 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4749;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___157_4748.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___157_4748.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4742, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4778 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4787 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4796 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4799 = FStar_Options.using_facts_from () in
                 match uu____4799 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4811 =
                         let uu____4816 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4816 [([], false)] in
                       [uu____4811] in
                     let uu___158_4844 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___158_4844.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___158_4844.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___158_4844.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___158_4844.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___158_4844.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___158_4844.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___158_4844.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___158_4844.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___158_4844.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___158_4844.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___158_4844.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___158_4844.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___158_4844.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___158_4844.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___158_4844.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___158_4844.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___158_4844.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___158_4844.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___158_4844.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___158_4844.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___158_4844.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___158_4844.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___158_4844.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___158_4844.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns
                     }
                 | None  -> env))
           | uu____4846 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4847 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4853 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4853) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_)
        |FStar_Syntax_Syntax.Sig_let (_,_,_) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_4863  ->
                  match uu___125_4863 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4864 -> false))
          -> env
      | uu____4865 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4901 se =
        match uu____4901 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4931 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4931
              then
                let uu____4932 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4932
              else ());
             (let uu____4934 = tc_decl env1 se in
              match uu____4934 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____4960 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4960
                    then
                      let uu____4961 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4964 =
                                 let uu____4965 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4965 "\n" in
                               Prims.strcat s uu____4964) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4961
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4969 =
                      let accum_exports_hidden uu____4987 se1 =
                        match uu____4987 with
                        | (exports1,hidden1) ->
                            let uu____5003 = for_export hidden1 se1 in
                            (match uu____5003 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____4969 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____5053 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____5053 with
      | (ses1,exports,env1,uu____5079) ->
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
      (let uu____5104 = FStar_Options.debug_any () in
       if uu____5104
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
         let uu___159_5110 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___159_5110.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___159_5110.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___159_5110.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___159_5110.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___159_5110.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___159_5110.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___159_5110.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___159_5110.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___159_5110.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___159_5110.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___159_5110.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___159_5110.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___159_5110.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___159_5110.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___159_5110.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___159_5110.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___159_5110.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___159_5110.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___159_5110.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___159_5110.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___159_5110.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___159_5110.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___159_5110.FStar_TypeChecker_Env.proof_ns)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____5113 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5113 with
        | (ses,exports,env3) ->
            ((let uu___160_5131 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___160_5131.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___160_5131.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___160_5131.FStar_Syntax_Syntax.is_interface)
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
        let uu____5147 = tc_decls env decls in
        match uu____5147 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___161_5165 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___161_5165.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___161_5165.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___161_5165.FStar_Syntax_Syntax.is_interface)
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
          let uu___162_5179 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___162_5179.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___162_5179.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___162_5179.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___162_5179.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___162_5179.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___162_5179.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___162_5179.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___162_5179.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___162_5179.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___162_5179.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___162_5179.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___162_5179.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___162_5179.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___162_5179.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___162_5179.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___162_5179.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___162_5179.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___162_5179.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___162_5179.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___162_5179.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___162_5179.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___162_5179.FStar_TypeChecker_Env.proof_ns)
          } in
        let check_term lid univs1 t =
          let uu____5190 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5190 with
          | (univs2,t1) ->
              ((let uu____5196 =
                  let uu____5197 =
                    let uu____5200 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5200 in
                  FStar_All.pipe_left uu____5197
                    (FStar_Options.Other "Exports") in
                if uu____5196
                then
                  let uu____5201 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5202 =
                    let uu____5203 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5203
                      (FStar_String.concat ", ") in
                  let uu____5208 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5201 uu____5202 uu____5208
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5211 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5211 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5229 =
             let uu____5230 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5231 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5230 uu____5231 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5229);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5238) ->
              let uu____5243 =
                let uu____5244 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5244 in
              if uu____5243
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5252,uu____5253) ->
              let t =
                let uu____5261 =
                  let uu____5264 =
                    let uu____5265 =
                      let uu____5273 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5273) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5265 in
                  FStar_Syntax_Syntax.mk uu____5264 in
                uu____5261 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5285,uu____5286,uu____5287) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5293 =
                let uu____5294 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5294 in
              if uu____5293 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5297,lbs),uu____5299,uu____5300) ->
              let uu____5310 =
                let uu____5311 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5311 in
              if uu____5310
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
              let uu____5328 =
                let uu____5329 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5329 in
              if uu____5328
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main _
            |FStar_Syntax_Syntax.Sig_assume _
             |FStar_Syntax_Syntax.Sig_new_effect _
              |FStar_Syntax_Syntax.Sig_new_effect_for_free _
               |FStar_Syntax_Syntax.Sig_sub_effect _
                |FStar_Syntax_Syntax.Sig_pragma _
              -> () in
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
          let uu___163_5362 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___163_5362.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___163_5362.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5365 =
           let uu____5366 = FStar_Options.lax () in
           Prims.op_Negation uu____5366 in
         if uu____5365 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5372 =
           let uu____5373 = FStar_Options.interactive () in
           Prims.op_Negation uu____5373 in
         if uu____5372
         then
           let uu____5374 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5374 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5384 = tc_partial_modul env modul in
      match uu____5384 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5405 = FStar_Options.debug_any () in
       if uu____5405
       then
         let uu____5406 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5406
       else ());
      (let env1 =
         let uu___164_5410 = env in
         let uu____5411 =
           let uu____5412 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5412 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___164_5410.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___164_5410.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___164_5410.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___164_5410.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___164_5410.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___164_5410.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___164_5410.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___164_5410.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___164_5410.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___164_5410.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___164_5410.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___164_5410.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___164_5410.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___164_5410.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___164_5410.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___164_5410.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___164_5410.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___164_5410.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5411;
           FStar_TypeChecker_Env.lax_universes =
             (uu___164_5410.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___164_5410.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___164_5410.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___164_5410.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___164_5410.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___164_5410.FStar_TypeChecker_Env.proof_ns)
         } in
       let uu____5413 = tc_modul env1 m in
       match uu____5413 with
       | (m1,env2) ->
           ((let uu____5421 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5421
             then
               let uu____5422 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5422
             else ());
            (let uu____5425 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5425
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
                       let uu____5452 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5452 with
                       | (univnames1,e) ->
                           let uu___165_5457 = lb in
                           let uu____5458 =
                             let uu____5461 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5461 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___165_5457.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___165_5457.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___165_5457.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___165_5457.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5458
                           } in
                     let uu___166_5462 = se in
                     let uu____5463 =
                       let uu____5464 =
                         let uu____5470 =
                           let uu____5474 = FStar_List.map update lbs in
                           (b, uu____5474) in
                         (uu____5470, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5464 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5463;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___166_5462.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___166_5462.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___166_5462.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5482 -> se in
               let normalized_module =
                 let uu___167_5484 = m1 in
                 let uu____5485 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___167_5484.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5485;
                   FStar_Syntax_Syntax.exports =
                     (uu___167_5484.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___167_5484.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5486 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5486
             else ());
            (m1, env2)))