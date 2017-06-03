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
          let uu___90_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___90_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___90_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___90_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___90_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___90_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___90_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___90_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___90_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___90_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___90_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___90_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___90_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___90_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___90_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___90_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___90_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___90_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___90_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___90_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___90_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___90_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___90_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___90_12.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___90_12.FStar_TypeChecker_Env.proof_ns)
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
          let uu___91_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___91_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___91_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___91_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___91_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___91_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___91_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___91_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___91_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___91_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___91_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___91_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___91_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___91_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___91_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___91_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___91_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___91_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___91_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___91_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___91_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___91_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___91_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___91_24.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___91_24.FStar_TypeChecker_Env.proof_ns)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____30 =
         let uu____31 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____31 in
       Prims.op_Negation uu____30)
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____41 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____41 with
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
        (let uu____63 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____63
         then
           let uu____64 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____64
         else ());
        (let uu____66 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____66 with
         | (t',uu____71,uu____72) ->
             ((let uu____74 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____74
               then
                 let uu____75 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____75
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
        let uu____86 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____86
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____108 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____108)
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
        let fail uu____130 =
          let uu____131 =
            let uu____132 =
              let uu____135 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____135, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____132 in
          raise uu____131 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____163)::(wp,uu____165)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____174 -> fail ())
        | uu____175 -> fail ()
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____237 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____237 with
      | (effect_params_un,signature_un,opening) ->
          let uu____244 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____244 with
           | (effect_params,env,uu____250) ->
               let uu____251 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____251 with
                | (signature,uu____255) ->
                    let ed1 =
                      let uu___92_257 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___92_257.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___92_257.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___92_257.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___92_257.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___92_257.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___92_257.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___92_257.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___92_257.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___92_257.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___92_257.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___92_257.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___92_257.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___92_257.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___92_257.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___92_257.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___92_257.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___92_257.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____261 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
                          let uu___93_279 = ed1 in
                          let uu____280 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____281 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____282 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____283 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____284 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____285 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____286 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____287 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____288 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____289 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____290 =
                            let uu____291 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____291 in
                          let uu____297 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____298 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____299 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___94_302 = a in
                                 let uu____303 =
                                   let uu____304 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____304 in
                                 let uu____310 =
                                   let uu____311 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____311 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___94_302.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___94_302.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___94_302.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___94_302.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____303;
                                   FStar_Syntax_Syntax.action_typ = uu____310
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___93_279.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___93_279.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___93_279.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___93_279.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___93_279.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____280;
                            FStar_Syntax_Syntax.bind_wp = uu____281;
                            FStar_Syntax_Syntax.if_then_else = uu____282;
                            FStar_Syntax_Syntax.ite_wp = uu____283;
                            FStar_Syntax_Syntax.stronger = uu____284;
                            FStar_Syntax_Syntax.close_wp = uu____285;
                            FStar_Syntax_Syntax.assert_p = uu____286;
                            FStar_Syntax_Syntax.assume_p = uu____287;
                            FStar_Syntax_Syntax.null_wp = uu____288;
                            FStar_Syntax_Syntax.trivial = uu____289;
                            FStar_Syntax_Syntax.repr = uu____290;
                            FStar_Syntax_Syntax.return_repr = uu____297;
                            FStar_Syntax_Syntax.bind_repr = uu____298;
                            FStar_Syntax_Syntax.actions = uu____299
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____339 =
                          let uu____340 =
                            let uu____343 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____343, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____340 in
                        raise uu____339 in
                      let uu____348 =
                        let uu____349 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____349.FStar_Syntax_Syntax.n in
                      match uu____348 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____374)::(wp,uu____376)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____385 -> fail signature1)
                      | uu____386 -> fail signature1 in
                    let uu____387 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____387 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____405 =
                           let uu____406 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____406 with
                           | (signature1,uu____414) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____416 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____416 in
                         ((let uu____418 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____418
                           then
                             let uu____419 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____420 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____421 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____422 =
                               let uu____423 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____423 in
                             let uu____424 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____419 uu____420 uu____421 uu____422
                               uu____424
                           else ());
                          (let check_and_gen' env2 uu____437 k =
                             match uu____437 with
                             | (uu____442,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____450 =
                                 let uu____454 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____455 =
                                   let uu____457 =
                                     let uu____458 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____458 in
                                   [uu____457] in
                                 uu____454 :: uu____455 in
                               let uu____459 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____450 uu____459 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____463 = fresh_effect_signature () in
                             match uu____463 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____477 =
                                     let uu____481 =
                                       let uu____482 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____482 in
                                     [uu____481] in
                                   let uu____483 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____477
                                     uu____483 in
                                 let expected_k =
                                   let uu____489 =
                                     let uu____493 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____494 =
                                       let uu____496 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____497 =
                                         let uu____499 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____500 =
                                           let uu____502 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____503 =
                                             let uu____505 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____505] in
                                           uu____502 :: uu____503 in
                                         uu____499 :: uu____500 in
                                       uu____496 :: uu____497 in
                                     uu____493 :: uu____494 in
                                   let uu____506 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____489
                                     uu____506 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____511 =
                                 let uu____512 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____512
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____511 in
                             let expected_k =
                               let uu____520 =
                                 let uu____524 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____525 =
                                   let uu____527 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____528 =
                                     let uu____530 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____531 =
                                       let uu____533 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____533] in
                                     uu____530 :: uu____531 in
                                   uu____527 :: uu____528 in
                                 uu____524 :: uu____525 in
                               let uu____534 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____520 uu____534 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____541 =
                                 let uu____545 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____546 =
                                   let uu____548 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____548] in
                                 uu____545 :: uu____546 in
                               let uu____549 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____541 uu____549 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____553 = FStar_Syntax_Util.type_u () in
                             match uu____553 with
                             | (t,uu____557) ->
                                 let expected_k =
                                   let uu____561 =
                                     let uu____565 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____566 =
                                       let uu____568 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____569 =
                                         let uu____571 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____571] in
                                       uu____568 :: uu____569 in
                                     uu____565 :: uu____566 in
                                   let uu____572 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____561
                                     uu____572 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____577 =
                                 let uu____578 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____578
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____577 in
                             let b_wp_a =
                               let uu____586 =
                                 let uu____590 =
                                   let uu____591 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____591 in
                                 [uu____590] in
                               let uu____592 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____586 uu____592 in
                             let expected_k =
                               let uu____598 =
                                 let uu____602 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____603 =
                                   let uu____605 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____606 =
                                     let uu____608 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____608] in
                                   uu____605 :: uu____606 in
                                 uu____602 :: uu____603 in
                               let uu____609 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____598 uu____609 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____616 =
                                 let uu____620 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____621 =
                                   let uu____623 =
                                     let uu____624 =
                                       let uu____625 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____625
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____624 in
                                   let uu____630 =
                                     let uu____632 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____632] in
                                   uu____623 :: uu____630 in
                                 uu____620 :: uu____621 in
                               let uu____633 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____616 uu____633 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____640 =
                                 let uu____644 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____645 =
                                   let uu____647 =
                                     let uu____648 =
                                       let uu____649 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____649
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____648 in
                                   let uu____654 =
                                     let uu____656 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____656] in
                                   uu____647 :: uu____654 in
                                 uu____644 :: uu____645 in
                               let uu____657 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____640 uu____657 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____664 =
                                 let uu____668 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____668] in
                               let uu____669 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____664 uu____669 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____673 = FStar_Syntax_Util.type_u () in
                             match uu____673 with
                             | (t,uu____677) ->
                                 let expected_k =
                                   let uu____681 =
                                     let uu____685 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____686 =
                                       let uu____688 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____688] in
                                     uu____685 :: uu____686 in
                                   let uu____689 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____681
                                     uu____689 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____692 =
                             let uu____698 =
                               let uu____699 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____699.FStar_Syntax_Syntax.n in
                             match uu____698 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____708 ->
                                 let repr =
                                   let uu____710 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____710 with
                                   | (t,uu____714) ->
                                       let expected_k =
                                         let uu____718 =
                                           let uu____722 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____723 =
                                             let uu____725 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____725] in
                                           uu____722 :: uu____723 in
                                         let uu____726 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____718
                                           uu____726 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____739 =
                                     let uu____742 =
                                       let uu____743 =
                                         let uu____753 =
                                           let uu____755 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____756 =
                                             let uu____758 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____758] in
                                           uu____755 :: uu____756 in
                                         (repr1, uu____753) in
                                       FStar_Syntax_Syntax.Tm_app uu____743 in
                                     FStar_Syntax_Syntax.mk uu____742 in
                                   uu____739 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____777 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____777 wp in
                                 let destruct_repr t =
                                   let uu____788 =
                                     let uu____789 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____789.FStar_Syntax_Syntax.n in
                                   match uu____788 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____798,(t1,uu____800)::(wp,uu____802)::[])
                                       -> (t1, wp)
                                   | uu____836 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____845 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____845
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____846 = fresh_effect_signature () in
                                   match uu____846 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____860 =
                                           let uu____864 =
                                             let uu____865 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____865 in
                                           [uu____864] in
                                         let uu____866 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____860
                                           uu____866 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____872 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____872 in
                                       let wp_g_x =
                                         let uu____876 =
                                           let uu____877 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____878 =
                                             let uu____879 =
                                               let uu____880 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____880 in
                                             [uu____879] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____877 uu____878 in
                                         uu____876 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____891 =
                                             let uu____892 =
                                               let uu____893 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____893
                                                 FStar_Pervasives.snd in
                                             let uu____898 =
                                               let uu____899 =
                                                 let uu____901 =
                                                   let uu____903 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____904 =
                                                     let uu____906 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____907 =
                                                       let uu____909 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____910 =
                                                         let uu____912 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____912] in
                                                       uu____909 :: uu____910 in
                                                     uu____906 :: uu____907 in
                                                   uu____903 :: uu____904 in
                                                 r :: uu____901 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____899 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____892 uu____898 in
                                           uu____891 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____920 =
                                           let uu____924 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____925 =
                                             let uu____927 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____928 =
                                               let uu____930 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____931 =
                                                 let uu____933 =
                                                   let uu____934 =
                                                     let uu____935 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____935 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____934 in
                                                 let uu____936 =
                                                   let uu____938 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____939 =
                                                     let uu____941 =
                                                       let uu____942 =
                                                         let uu____943 =
                                                           let uu____947 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____947] in
                                                         let uu____948 =
                                                           let uu____951 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____951 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____943
                                                           uu____948 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____942 in
                                                     [uu____941] in
                                                   uu____938 :: uu____939 in
                                                 uu____933 :: uu____936 in
                                               uu____930 :: uu____931 in
                                             uu____927 :: uu____928 in
                                           uu____924 :: uu____925 in
                                         let uu____952 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____920
                                           uu____952 in
                                       let uu____955 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____955 with
                                        | (expected_k1,uu____960,uu____961)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___95_965 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___95_965.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___95_965.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___95_965.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___95_965.FStar_TypeChecker_Env.proof_ns)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____972 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____972 in
                                   let res =
                                     let wp =
                                       let uu____979 =
                                         let uu____980 =
                                           let uu____981 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____981
                                             FStar_Pervasives.snd in
                                         let uu____986 =
                                           let uu____987 =
                                             let uu____989 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____990 =
                                               let uu____992 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____992] in
                                             uu____989 :: uu____990 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____987 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____980 uu____986 in
                                       uu____979 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1000 =
                                       let uu____1004 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1005 =
                                         let uu____1007 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1007] in
                                       uu____1004 :: uu____1005 in
                                     let uu____1008 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1000
                                       uu____1008 in
                                   let uu____1011 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1011 with
                                   | (expected_k1,uu____1019,uu____1020) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1023 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1023 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1035 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1049 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1049 with
                                     | (act_typ,uu____1054,g_t) ->
                                         let env' =
                                           let uu___96_1057 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___96_1057.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___96_1057.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___96_1057.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___96_1057.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___96_1057.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___96_1057.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___96_1057.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___96_1057.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___96_1057.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___96_1057.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___96_1057.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___96_1057.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___96_1057.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___96_1057.FStar_TypeChecker_Env.proof_ns)
                                           } in
                                         ((let uu____1059 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1059
                                           then
                                             let uu____1060 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1061 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1060 uu____1061
                                           else ());
                                          (let uu____1063 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1063 with
                                           | (act_defn,uu____1068,g_a) ->
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
                                               let uu____1072 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1090 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1090 with
                                                      | (bs1,uu____1096) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1103 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1103 in
                                                          let uu____1106 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1106
                                                           with
                                                           | (k1,uu____1113,g)
                                                               -> (k1, g)))
                                                 | uu____1115 ->
                                                     let uu____1116 =
                                                       let uu____1117 =
                                                         let uu____1120 =
                                                           let uu____1121 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1122 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1121
                                                             uu____1122 in
                                                         (uu____1120,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1117 in
                                                     raise uu____1116 in
                                               (match uu____1072 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1129 =
                                                        let uu____1130 =
                                                          let uu____1131 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1131 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1130 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1129);
                                                     (let act_typ2 =
                                                        let uu____1135 =
                                                          let uu____1136 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1136.FStar_Syntax_Syntax.n in
                                                        match uu____1135 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1153 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1153
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1160
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1160
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1180
                                                                    =
                                                                    let uu____1181
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1181] in
                                                                    let uu____1182
                                                                    =
                                                                    let uu____1188
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1188] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1180;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1182;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1189
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1189))
                                                        | uu____1192 ->
                                                            failwith "" in
                                                      let uu____1195 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1195 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___97_1201 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___97_1201.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___97_1201.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___97_1201.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____692 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1217 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1217 in
                               let uu____1220 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1220 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1226 =
                                        let uu____1229 =
                                          let uu____1230 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1230.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1229) in
                                      match uu____1226 with
                                      | ([],uu____1233) -> t1
                                      | (uu____1239,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1240,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1252 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1263 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1263 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1269 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1270 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1270))
                                           && (m <> n1) in
                                       if uu____1269
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1284 =
                                           let uu____1285 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1286 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1285 uu____1286 in
                                         failwith uu____1284
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1292 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1292 with
                                      | (univs2,defn) ->
                                          let uu____1297 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1297 with
                                           | (univs',typ) ->
                                               let uu___98_1303 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___98_1303.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___98_1303.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___98_1303.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___99_1306 = ed2 in
                                      let uu____1307 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1308 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1309 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1310 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1311 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1312 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1313 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1314 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1315 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1316 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1317 =
                                        let uu____1318 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1318 in
                                      let uu____1324 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1325 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1326 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___99_1306.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___99_1306.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1307;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1308;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1309;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1310;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1311;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1312;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1313;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1314;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1315;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1316;
                                        FStar_Syntax_Syntax.repr = uu____1317;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1324;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1325;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1326
                                      } in
                                    ((let uu____1329 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1329
                                      then
                                        let uu____1330 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1330
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
      let uu____1334 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1334 with
      | (effect_binders_un,signature_un) ->
          let uu____1344 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1344 with
           | (effect_binders,env1,uu____1355) ->
               let uu____1356 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1356 with
                | (signature,uu____1365) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1374  ->
                           match uu____1374 with
                           | (bv,qual) ->
                               let uu____1381 =
                                 let uu___100_1382 = bv in
                                 let uu____1383 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___100_1382.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___100_1382.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1383
                                 } in
                               (uu____1381, qual)) effect_binders in
                    let uu____1386 =
                      let uu____1391 =
                        let uu____1392 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1392.FStar_Syntax_Syntax.n in
                      match uu____1391 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1400)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1415 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1386 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1432 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1432
                           then
                             let uu____1433 =
                               let uu____1435 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1435 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1433
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1459 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1459 with
                           | (t2,comp,uu____1467) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1478 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1478 with
                          | (repr,_comp) ->
                              ((let uu____1491 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1491
                                then
                                  let uu____1492 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1492
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
                                  let uu____1498 =
                                    let uu____1499 =
                                      let uu____1500 =
                                        let uu____1510 =
                                          let uu____1514 =
                                            let uu____1517 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1518 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1517, uu____1518) in
                                          [uu____1514] in
                                        (wp_type1, uu____1510) in
                                      FStar_Syntax_Syntax.Tm_app uu____1500 in
                                    mk1 uu____1499 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1498 in
                                let effect_signature =
                                  let binders =
                                    let uu____1533 =
                                      let uu____1536 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1536) in
                                    let uu____1537 =
                                      let uu____1541 =
                                        let uu____1542 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1542
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1541] in
                                    uu____1533 :: uu____1537 in
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
                                  let uu____1585 = item in
                                  match uu____1585 with
                                  | (u_item,item1) ->
                                      let uu____1597 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1597 with
                                       | (item2,item_comp) ->
                                           ((let uu____1607 =
                                               let uu____1608 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1608 in
                                             if uu____1607
                                             then
                                               let uu____1609 =
                                                 let uu____1610 =
                                                   let uu____1611 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1612 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1611 uu____1612 in
                                                 FStar_Errors.Err uu____1610 in
                                               raise uu____1609
                                             else ());
                                            (let uu____1614 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1614 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1627 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1627 with
                                | (dmff_env1,uu____1640,bind_wp,bind_elab) ->
                                    let uu____1643 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1643 with
                                     | (dmff_env2,uu____1656,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1660 =
                                             let uu____1661 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1661.FStar_Syntax_Syntax.n in
                                           match uu____1660 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1699 =
                                                 let uu____1707 =
                                                   let uu____1710 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1710 in
                                                 match uu____1707 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1749 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1699 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1771 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1771 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1782 =
                                                          let uu____1783 =
                                                            let uu____1793 =
                                                              let uu____1797
                                                                =
                                                                let uu____1800
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1801
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1800,
                                                                  uu____1801) in
                                                              [uu____1797] in
                                                            (wp_type1,
                                                              uu____1793) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1783 in
                                                        mk1 uu____1782 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1809 =
                                                      let uu____1819 =
                                                        let uu____1820 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1820 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1819 in
                                                    (match uu____1809 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1848
                                                           =
                                                           let error_msg =
                                                             let uu____1850 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1851 =
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
                                                                   (lid,uu____1867))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1850
                                                               uu____1851 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1893
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1893
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
                                                                    fail ())
                                                               else fail ()
                                                           | Some
                                                               (FStar_Util.Inr
                                                               (lid,uu____1899))
                                                               ->
                                                               if
                                                                 Prims.op_Negation
                                                                   (FStar_Syntax_Util.is_pure_effect
                                                                    lid)
                                                               then fail ()
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
                                                             let uu____1919 =
                                                               let uu____1920
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1921
                                                                 =
                                                                 let uu____1922
                                                                   =
                                                                   let uu____1926
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1926,
                                                                    None) in
                                                                 [uu____1922] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1920
                                                                 uu____1921 in
                                                             uu____1919 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1942 =
                                                             let uu____1943 =
                                                               let uu____1947
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1947] in
                                                             b11 ::
                                                               uu____1943 in
                                                           let uu____1950 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1942
                                                             uu____1950
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1960 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1962 =
                                             let uu____1963 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1963.FStar_Syntax_Syntax.n in
                                           match uu____1962 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2001 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2001
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2017 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2019 =
                                             let uu____2020 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2020.FStar_Syntax_Syntax.n in
                                           match uu____2019 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2049 =
                                                 let uu____2050 =
                                                   let uu____2052 =
                                                     let uu____2053 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2053 in
                                                   [uu____2052] in
                                                 FStar_List.append uu____2050
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2049 body what
                                           | uu____2054 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2074 =
                                                let uu____2075 =
                                                  let uu____2076 =
                                                    let uu____2086 =
                                                      let uu____2087 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2087 in
                                                    (t, uu____2086) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2076 in
                                                mk1 uu____2075 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2074) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2110 = f a2 in
                                               [uu____2110]
                                           | x::xs ->
                                               let uu____2114 =
                                                 apply_last1 f xs in
                                               x :: uu____2114 in
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
                                           let uu____2129 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2129 with
                                           | Some (_us,_t) ->
                                               ((let uu____2146 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2146
                                                 then
                                                   let uu____2147 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2147
                                                 else ());
                                                (let uu____2149 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2149))
                                           | None  ->
                                               let uu____2154 =
                                                 let uu____2157 = mk_lid name in
                                                 let uu____2158 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2157 uu____2158 in
                                               (match uu____2154 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2167 =
                                                        let uu____2169 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2169 in
                                                      FStar_ST.write sigelts
                                                        uu____2167);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2180 =
                                             let uu____2182 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2183 =
                                               FStar_ST.read sigelts in
                                             uu____2182 :: uu____2183 in
                                           FStar_ST.write sigelts uu____2180);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2193 =
                                              let uu____2195 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2196 =
                                                FStar_ST.read sigelts in
                                              uu____2195 :: uu____2196 in
                                            FStar_ST.write sigelts uu____2193);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2206 =
                                               let uu____2208 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2209 =
                                                 FStar_ST.read sigelts in
                                               uu____2208 :: uu____2209 in
                                             FStar_ST.write sigelts
                                               uu____2206);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2219 =
                                                let uu____2221 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2222 =
                                                  FStar_ST.read sigelts in
                                                uu____2221 :: uu____2222 in
                                              FStar_ST.write sigelts
                                                uu____2219);
                                             (let uu____2230 =
                                                FStar_List.fold_left
                                                  (fun uu____2237  ->
                                                     fun action  ->
                                                       match uu____2237 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2250 =
                                                             let uu____2254 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2254
                                                               params_un in
                                                           (match uu____2250
                                                            with
                                                            | (action_params,env',uu____2260)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2269
                                                                     ->
                                                                    match uu____2269
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2276
                                                                    =
                                                                    let uu___101_2277
                                                                    = bv in
                                                                    let uu____2278
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___101_2277.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___101_2277.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2278
                                                                    } in
                                                                    (uu____2276,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2282
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2282
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
                                                                    uu____2308
                                                                    ->
                                                                    let uu____2309
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2309 in
                                                                    ((
                                                                    let uu____2313
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2313
                                                                    then
                                                                    let uu____2314
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2315
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2316
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2317
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2314
                                                                    uu____2315
                                                                    uu____2316
                                                                    uu____2317
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
                                                                    let uu____2321
                                                                    =
                                                                    let uu____2323
                                                                    =
                                                                    let uu___102_2324
                                                                    = action in
                                                                    let uu____2325
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2326
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___102_2324.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___102_2324.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___102_2324.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2325;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2326
                                                                    } in
                                                                    uu____2323
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2321))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2230 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2346 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2347 =
                                                        let uu____2349 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2349] in
                                                      uu____2346 ::
                                                        uu____2347 in
                                                    let uu____2350 =
                                                      let uu____2351 =
                                                        let uu____2352 =
                                                          let uu____2353 =
                                                            let uu____2363 =
                                                              let uu____2367
                                                                =
                                                                let uu____2370
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2371
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2370,
                                                                  uu____2371) in
                                                              [uu____2367] in
                                                            (repr,
                                                              uu____2363) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2353 in
                                                        mk1 uu____2352 in
                                                      let uu____2379 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2351
                                                        uu____2379 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2350 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2387 =
                                                    let uu____2392 =
                                                      let uu____2393 =
                                                        let uu____2396 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2396 in
                                                      uu____2393.FStar_Syntax_Syntax.n in
                                                    match uu____2392 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2404)
                                                        ->
                                                        let uu____2431 =
                                                          let uu____2440 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2440
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2471 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2431
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2499 =
                                                               let uu____2500
                                                                 =
                                                                 let uu____2503
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2503 in
                                                               uu____2500.FStar_Syntax_Syntax.n in
                                                             (match uu____2499
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2520
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2520
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2529
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2540
                                                                     ->
                                                                    match uu____2540
                                                                    with
                                                                    | 
                                                                    (bv,uu____2544)
                                                                    ->
                                                                    let uu____2545
                                                                    =
                                                                    let uu____2546
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2546
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2545
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2529
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
                                                                    uu____2579
                                                                    ->
                                                                    let uu____2583
                                                                    =
                                                                    let uu____2584
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2584 in
                                                                    failwith
                                                                    uu____2583 in
                                                                    let uu____2587
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2590
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2587,
                                                                    uu____2590)))
                                                              | uu____2600 ->
                                                                  let uu____2601
                                                                    =
                                                                    let uu____2602
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2602 in
                                                                  failwith
                                                                    uu____2601))
                                                    | uu____2607 ->
                                                        let uu____2608 =
                                                          let uu____2609 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2609 in
                                                        failwith uu____2608 in
                                                  (match uu____2387 with
                                                   | (pre,post) ->
                                                       ((let uu____2626 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2628 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2630 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___103_2632
                                                             = ed in
                                                           let uu____2633 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2634 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2635 =
                                                             let uu____2636 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2636) in
                                                           let uu____2642 =
                                                             let uu____2643 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2643) in
                                                           let uu____2649 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2650 =
                                                             let uu____2651 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2651) in
                                                           let uu____2657 =
                                                             let uu____2658 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2658) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2633;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2634;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2635;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2642;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___103_2632.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2649;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2650;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2657;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2664 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2664
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2675
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2675
                                                               then
                                                                 let uu____2676
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2676
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
                                                                    let uu____2688
                                                                    =
                                                                    let uu____2690
                                                                    =
                                                                    let uu____2696
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2696) in
                                                                    Some
                                                                    uu____2690 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2688;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2707
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2707
                                                                 else None in
                                                               let uu____2709
                                                                 =
                                                                 let uu____2711
                                                                   =
                                                                   let uu____2713
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2713 in
                                                                 FStar_List.append
                                                                   uu____2711
                                                                   sigelts' in
                                                               (uu____2709,
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
                (lex_t1,[],[],t,uu____2736,uu____2737);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2739;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_29,uu____2743);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2745;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_30,uu____2749);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2751;_}::[]
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
                let uu____2790 =
                  let uu____2793 =
                    let uu____2794 =
                      let uu____2799 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2799, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2794 in
                  FStar_Syntax_Syntax.mk uu____2793 in
                uu____2790 None r1 in
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
                  let uu____2819 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2819 in
                let hd1 =
                  let uu____2825 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2825 in
                let tl1 =
                  let uu____2827 =
                    let uu____2828 =
                      let uu____2831 =
                        let uu____2832 =
                          let uu____2837 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2837, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2832 in
                      FStar_Syntax_Syntax.mk uu____2831 in
                    uu____2828 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2827 in
                let res =
                  let uu____2850 =
                    let uu____2853 =
                      let uu____2854 =
                        let uu____2859 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2859,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2854 in
                    FStar_Syntax_Syntax.mk uu____2853 in
                  uu____2850 None r2 in
                let uu____2869 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2869 in
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
              let uu____2891 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2891;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2894 ->
              let uu____2896 =
                let uu____2897 =
                  let uu____2898 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2898 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2897 in
              failwith uu____2896
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
            let uu____2908 = FStar_Syntax_Util.type_u () in
            match uu____2908 with
            | (k,uu____2912) ->
                let phi1 =
                  let uu____2914 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2914
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
          let uu____2924 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2924 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2943 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2943 FStar_List.flatten in
              ((let uu____2951 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2951
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
                          let uu____2957 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2963,uu____2964,uu____2965,uu____2966,uu____2967)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2972 -> failwith "Impossible!" in
                          match uu____2957 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2981 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2985,uu____2986,uu____2987,uu____2988,uu____2989)
                        -> lid
                    | uu____2994 -> failwith "Impossible" in
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
                let uu____3000 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____3000
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
                   let uu____3018 =
                     let uu____3020 =
                       let uu____3021 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____3021;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____3020 :: ses1 in
                   (uu____3018, data_ops_ses))))
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3039 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3052 ->
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
           let uu____3082 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3082 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3107 = FStar_Options.set_options t s in
             match uu____3107 with
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
                ((let uu____3124 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3124 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3130 = cps_and_elaborate env1 ne in
           (match uu____3130 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___104_3151 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___104_3151.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___104_3151.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___104_3151.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___105_3152 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___105_3152.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_3152.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_3152.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___106_3158 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___106_3158.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___106_3158.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___106_3158.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3164 =
             let uu____3169 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3169 in
           (match uu____3164 with
            | (a,wp_a_src) ->
                let uu____3180 =
                  let uu____3185 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3185 in
                (match uu____3180 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3197 =
                         let uu____3199 =
                           let uu____3200 =
                             let uu____3205 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3205) in
                           FStar_Syntax_Syntax.NT uu____3200 in
                         [uu____3199] in
                       FStar_Syntax_Subst.subst uu____3197 wp_b_tgt in
                     let expected_k =
                       let uu____3209 =
                         let uu____3213 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3214 =
                           let uu____3216 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3216] in
                         uu____3213 :: uu____3214 in
                       let uu____3217 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3209 uu____3217 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3238 =
                           let uu____3239 =
                             let uu____3242 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3243 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3242, uu____3243) in
                           FStar_Errors.Error uu____3239 in
                         raise uu____3238 in
                       let uu____3246 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3246 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3265 =
                             let uu____3266 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3266 in
                           if uu____3265
                           then no_reify eff_name
                           else
                             (let uu____3271 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3272 =
                                let uu____3275 =
                                  let uu____3276 =
                                    let uu____3286 =
                                      let uu____3288 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3289 =
                                        let uu____3291 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3291] in
                                      uu____3288 :: uu____3289 in
                                    (repr, uu____3286) in
                                  FStar_Syntax_Syntax.Tm_app uu____3276 in
                                FStar_Syntax_Syntax.mk uu____3275 in
                              uu____3272 None uu____3271) in
                     let uu____3301 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3316,lift_wp)) ->
                           let uu____3329 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3329)
                       | (Some (what,lift),None ) ->
                           ((let uu____3344 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3344
                             then
                               let uu____3345 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3345
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3348 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3348 with
                             | (lift1,comp,uu____3357) ->
                                 let uu____3358 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3358 with
                                  | (uu____3365,lift_wp,lift_elab) ->
                                      let uu____3368 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3369 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3301 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___107_3392 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___107_3392.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___107_3392.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___107_3392.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___107_3392.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___107_3392.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___107_3392.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___107_3392.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___107_3392.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___107_3392.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___107_3392.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___107_3392.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___107_3392.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___107_3392.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___107_3392.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___107_3392.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___107_3392.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___107_3392.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___107_3392.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___107_3392.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___107_3392.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___107_3392.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___107_3392.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___107_3392.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___107_3392.FStar_TypeChecker_Env.proof_ns)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3396,lift1) ->
                                let uu____3403 =
                                  let uu____3408 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3408 in
                                (match uu____3403 with
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
                                         let uu____3430 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3431 =
                                           let uu____3434 =
                                             let uu____3435 =
                                               let uu____3445 =
                                                 let uu____3447 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3448 =
                                                   let uu____3450 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3450] in
                                                 uu____3447 :: uu____3448 in
                                               (lift_wp1, uu____3445) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3435 in
                                           FStar_Syntax_Syntax.mk uu____3434 in
                                         uu____3431 None uu____3430 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3463 =
                                         let uu____3467 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3468 =
                                           let uu____3470 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3471 =
                                             let uu____3473 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3473] in
                                           uu____3470 :: uu____3471 in
                                         uu____3467 :: uu____3468 in
                                       let uu____3474 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3463
                                         uu____3474 in
                                     let uu____3477 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3477 with
                                      | (expected_k2,uu____3483,uu____3484)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___108_3487 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___108_3487.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___108_3487.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___109_3489 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___109_3489.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___109_3489.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___109_3489.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3502 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3502 with
            | (tps1,c1) ->
                let uu____3511 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3511 with
                 | (tps2,env3,us) ->
                     let uu____3522 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3522 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3536 =
                              let uu____3537 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3537 in
                            match uu____3536 with
                            | (uvs1,t) ->
                                let uu____3550 =
                                  let uu____3558 =
                                    let uu____3561 =
                                      let uu____3562 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3562.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3561) in
                                  match uu____3558 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3572,c4)) -> ([], c4)
                                  | (uu____3596,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3614 -> failwith "Impossible" in
                                (match uu____3550 with
                                 | (tps4,c4) ->
                                     (if
                                        ((FStar_List.length uvs1) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3645 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3645 with
                                         | (uu____3648,t1) ->
                                             let uu____3650 =
                                               let uu____3651 =
                                                 let uu____3654 =
                                                   let uu____3655 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3656 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3661 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3655 uu____3656
                                                     uu____3661 in
                                                 (uu____3654, r) in
                                               FStar_Errors.Error uu____3651 in
                                             raise uu____3650)
                                      else ();
                                      (let se1 =
                                         let uu___110_3664 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___110_3664.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___110_3664.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___110_3664.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3674,uu____3675,uu____3676) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___84_3678  ->
                   match uu___84_3678 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3679 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3682,uu____3683,uu____3684) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___84_3690  ->
                   match uu___84_3690 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3691 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3698 =
             if uvs = []
             then
               let uu____3699 =
                 let uu____3700 = FStar_Syntax_Util.type_u () in
                 fst uu____3700 in
               check_and_gen env2 t uu____3699
             else
               (let uu____3704 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3704 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3710 =
                        let uu____3711 = FStar_Syntax_Util.type_u () in
                        fst uu____3711 in
                      tc_check_trivial_guard env2 t1 uu____3710 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3715 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3715)) in
           (match uu____3698 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___111_3725 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___111_3725.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___111_3725.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___111_3725.FStar_Syntax_Syntax.sigmeta)
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
           let uu____3737 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3737 with
            | (e1,c,g1) ->
                let uu____3748 =
                  let uu____3752 =
                    let uu____3754 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3754 in
                  let uu____3755 =
                    let uu____3758 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3758) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3752 uu____3755 in
                (match uu____3748 with
                 | (e2,uu____3768,g) ->
                     ((let uu____3771 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3771);
                      (let se1 =
                         let uu___112_3773 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___112_3773.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___112_3773.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___112_3773.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3809 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3809
                 then Some q
                 else
                   (let uu____3822 =
                      let uu____3823 =
                        let uu____3826 =
                          let uu____3827 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3828 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3829 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3827 uu____3828 uu____3829 in
                        (uu____3826, r) in
                      FStar_Errors.Error uu____3823 in
                    raise uu____3822) in
           let uu____3832 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3853  ->
                     fun lb  ->
                       match uu____3853 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3877 =
                             let uu____3883 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3883 with
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
                                   | uu____3935 ->
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
                                  (let uu____3947 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3947, quals_opt1))) in
                           (match uu____3877 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3832 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____4000 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___85_4002  ->
                                match uu___85_4002 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____4003 -> false)) in
                      if uu____4000
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____4011 =
                    let uu____4014 =
                      let uu____4015 =
                        let uu____4023 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____4023) in
                      FStar_Syntax_Syntax.Tm_let uu____4015 in
                    FStar_Syntax_Syntax.mk uu____4014 in
                  uu____4011 None r in
                let uu____4045 =
                  let uu____4051 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___113_4055 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___113_4055.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___113_4055.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___113_4055.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___113_4055.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___113_4055.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___113_4055.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___113_4055.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___113_4055.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___113_4055.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___113_4055.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___113_4055.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___113_4055.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___113_4055.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___113_4055.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___113_4055.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___113_4055.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___113_4055.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___113_4055.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___113_4055.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___113_4055.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___113_4055.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___113_4055.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___113_4055.FStar_TypeChecker_Env.proof_ns)
                       }) e in
                  match uu____4051 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4063;
                       FStar_Syntax_Syntax.pos = uu____4064;
                       FStar_Syntax_Syntax.vars = uu____4065;_},uu____4066,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4085,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4090 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___86_4093  ->
                             match uu___86_4093 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4095 =
                                   let uu____4096 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4100 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4100)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4096 in
                                 if uu____4095
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___114_4109 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___114_4109.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___114_4109.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4115 -> failwith "impossible" in
                (match uu____4045 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4142 = log env2 in
                       if uu____4142
                       then
                         let uu____4143 =
                           let uu____4144 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4151 =
                                         let uu____4156 =
                                           let uu____4157 =
                                             let uu____4162 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4162.FStar_Syntax_Syntax.fv_name in
                                           uu____4157.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4156 in
                                       match uu____4151 with
                                       | None  -> true
                                       | uu____4169 -> false in
                                     if should_log
                                     then
                                       let uu____4174 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4175 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4174 uu____4175
                                     else "")) in
                           FStar_All.pipe_right uu____4144
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4143
                       else ());
                      ([se1], [])))))
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
             (fun uu___87_4204  ->
                match uu___87_4204 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4205 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4211) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4215 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4220 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4223 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4236 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4249) ->
          let uu____4254 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4254
          then
            let for_export_bundle se1 uu____4273 =
              match uu____4273 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4296,uu____4297) ->
                       let dec =
                         let uu___115_4303 = se1 in
                         let uu____4304 =
                           let uu____4305 =
                             let uu____4309 =
                               let uu____4312 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4312 in
                             (l, us, uu____4309) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4305 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4304;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___115_4303.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___115_4303.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4322,uu____4323,uu____4324) ->
                       let dec =
                         let uu___116_4328 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___116_4328.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___116_4328.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4331 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4343,uu____4344) ->
          let uu____4345 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4345 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4358 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4358
          then
            ([(let uu___117_4366 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___117_4366.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___117_4366.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4368 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___88_4370  ->
                       match uu___88_4370 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4371 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4374 -> true
                       | uu____4375 -> false)) in
             if uu____4368 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4385 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4388 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4391 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4394 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4397 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4407,uu____4408)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4424 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4424
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4445) ->
          let uu____4450 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4450
          then
            let uu____4455 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___118_4461 = se in
                      let uu____4462 =
                        let uu____4463 =
                          let uu____4467 =
                            let uu____4468 =
                              let uu____4473 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4473.FStar_Syntax_Syntax.fv_name in
                            uu____4468.FStar_Syntax_Syntax.v in
                          (uu____4467, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4463 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4462;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___118_4461.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___118_4461.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4455, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4491 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4500 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4509 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4512 = FStar_Options.using_facts_from () in
                 match uu____4512 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4524 =
                         let uu____4529 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4529 [([], false)] in
                       [uu____4524] in
                     let uu___119_4557 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___119_4557.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___119_4557.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___119_4557.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___119_4557.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___119_4557.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___119_4557.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___119_4557.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___119_4557.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___119_4557.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___119_4557.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___119_4557.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___119_4557.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___119_4557.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___119_4557.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___119_4557.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___119_4557.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___119_4557.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___119_4557.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___119_4557.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___119_4557.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___119_4557.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___119_4557.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___119_4557.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___119_4557.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns
                     }
                 | None  -> env))
           | uu____4559 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4560 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4566 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4566) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4567,uu____4568,uu____4569) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___89_4571  ->
                  match uu___89_4571 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4572 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4573,uu____4574,uu____4575) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___89_4581  ->
                  match uu___89_4581 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4582 -> false))
          -> env
      | uu____4583 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4619 se =
        match uu____4619 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4649 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4649
              then
                let uu____4650 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4650
              else ());
             (let uu____4652 = tc_decl env1 se in
              match uu____4652 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____4678 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4678
                    then
                      let uu____4679 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4682 =
                                 let uu____4683 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4683 "\n" in
                               Prims.strcat s uu____4682) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4679
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4687 =
                      let accum_exports_hidden uu____4705 se1 =
                        match uu____4705 with
                        | (exports1,hidden1) ->
                            let uu____4721 = for_export hidden1 se1 in
                            (match uu____4721 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____4687 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____4771 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4771 with
      | (ses1,exports,env1,uu____4797) ->
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
      (let uu____4822 = FStar_Options.debug_any () in
       if uu____4822
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
         let uu___120_4828 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___120_4828.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___120_4828.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___120_4828.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___120_4828.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___120_4828.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___120_4828.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___120_4828.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___120_4828.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___120_4828.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___120_4828.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___120_4828.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___120_4828.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___120_4828.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___120_4828.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___120_4828.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___120_4828.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___120_4828.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___120_4828.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___120_4828.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___120_4828.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___120_4828.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___120_4828.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___120_4828.FStar_TypeChecker_Env.proof_ns)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____4831 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____4831 with
        | (ses,exports,env3) ->
            ((let uu___121_4849 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___121_4849.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___121_4849.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___121_4849.FStar_Syntax_Syntax.is_interface)
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
        let uu____4865 = tc_decls env decls in
        match uu____4865 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___122_4883 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___122_4883.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___122_4883.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___122_4883.FStar_Syntax_Syntax.is_interface)
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
          let uu___123_4897 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___123_4897.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___123_4897.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___123_4897.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___123_4897.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___123_4897.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___123_4897.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___123_4897.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___123_4897.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___123_4897.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___123_4897.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___123_4897.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___123_4897.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___123_4897.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___123_4897.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___123_4897.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___123_4897.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___123_4897.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___123_4897.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___123_4897.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___123_4897.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___123_4897.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___123_4897.FStar_TypeChecker_Env.proof_ns)
          } in
        let check_term lid univs1 t =
          let uu____4908 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____4908 with
          | (univs2,t1) ->
              ((let uu____4914 =
                  let uu____4915 =
                    let uu____4918 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4918 in
                  FStar_All.pipe_left uu____4915
                    (FStar_Options.Other "Exports") in
                if uu____4914
                then
                  let uu____4919 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____4920 =
                    let uu____4921 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____4921
                      (FStar_String.concat ", ") in
                  let uu____4926 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4919 uu____4920 uu____4926
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____4929 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____4929 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____4947 =
             let uu____4948 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____4949 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4948 uu____4949 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4947);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4956) ->
              let uu____4961 =
                let uu____4962 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4962 in
              if uu____4961
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4970,uu____4971) ->
              let t =
                let uu____4979 =
                  let uu____4982 =
                    let uu____4983 =
                      let uu____4991 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____4991) in
                    FStar_Syntax_Syntax.Tm_arrow uu____4983 in
                  FStar_Syntax_Syntax.mk uu____4982 in
                uu____4979 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5003,uu____5004,uu____5005) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5011 =
                let uu____5012 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5012 in
              if uu____5011 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5015,lbs),uu____5017,uu____5018) ->
              let uu____5028 =
                let uu____5029 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5029 in
              if uu____5028
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
              let uu____5046 =
                let uu____5047 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5047 in
              if uu____5046
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5061 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5062 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5065 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5066 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5067 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5068 -> () in
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
          let uu___124_5082 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___124_5082.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___124_5082.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5085 =
           let uu____5086 = FStar_Options.lax () in
           Prims.op_Negation uu____5086 in
         if uu____5085 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5092 =
           let uu____5093 = FStar_Options.interactive () in
           Prims.op_Negation uu____5093 in
         if uu____5092
         then
           let uu____5094 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5094 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5104 = tc_partial_modul env modul in
      match uu____5104 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5125 = FStar_Options.debug_any () in
       if uu____5125
       then
         let uu____5126 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5126
       else ());
      (let env1 =
         let uu___125_5130 = env in
         let uu____5131 =
           let uu____5132 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5132 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___125_5130.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___125_5130.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___125_5130.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___125_5130.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___125_5130.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___125_5130.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___125_5130.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___125_5130.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___125_5130.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___125_5130.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___125_5130.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___125_5130.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___125_5130.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___125_5130.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___125_5130.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___125_5130.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___125_5130.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___125_5130.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5131;
           FStar_TypeChecker_Env.lax_universes =
             (uu___125_5130.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___125_5130.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___125_5130.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___125_5130.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___125_5130.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___125_5130.FStar_TypeChecker_Env.proof_ns)
         } in
       let uu____5133 = tc_modul env1 m in
       match uu____5133 with
       | (m1,env2) ->
           ((let uu____5141 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5141
             then
               let uu____5142 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5142
             else ());
            (let uu____5145 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5145
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
                       let uu____5172 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5172 with
                       | (univnames1,e) ->
                           let uu___126_5177 = lb in
                           let uu____5178 =
                             let uu____5181 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5181 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___126_5177.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___126_5177.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___126_5177.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___126_5177.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5178
                           } in
                     let uu___127_5182 = se in
                     let uu____5183 =
                       let uu____5184 =
                         let uu____5190 =
                           let uu____5194 = FStar_List.map update lbs in
                           (b, uu____5194) in
                         (uu____5190, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5184 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5183;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___127_5182.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___127_5182.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___127_5182.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5202 -> se in
               let normalized_module =
                 let uu___128_5204 = m1 in
                 let uu____5205 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___128_5204.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5205;
                   FStar_Syntax_Syntax.exports =
                     (uu___128_5204.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___128_5204.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5206 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5206
             else ());
            (m1, env2)))