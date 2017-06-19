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
          let uu___89_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___89_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___89_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___89_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___89_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___89_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___89_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___89_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___89_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___89_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___89_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___89_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___89_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___89_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___89_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___89_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___89_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___89_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___89_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___89_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___89_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___89_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___89_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___89_12.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
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
          let uu___90_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___90_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___90_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___90_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___90_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___90_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___90_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___90_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___90_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___90_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___90_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___90_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___90_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___90_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___90_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___90_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___90_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___90_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___90_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___90_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___90_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___90_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___90_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___90_24.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
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
                      let uu___91_257 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___91_257.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___91_257.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___91_257.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___91_257.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___91_257.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___91_257.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___91_257.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___91_257.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___91_257.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___91_257.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___91_257.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___91_257.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___91_257.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___91_257.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___91_257.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___91_257.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___91_257.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____261 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
                          let uu___92_279 = ed1 in
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
                                 let uu___93_302 = a in
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
                                     (uu___93_302.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___93_302.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___93_302.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___93_302.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____303;
                                   FStar_Syntax_Syntax.action_typ = uu____310
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___92_279.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___92_279.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___92_279.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___92_279.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___92_279.FStar_Syntax_Syntax.signature);
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
                                              let uu___94_965 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___94_965.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___94_965.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___94_965.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___94_965.FStar_TypeChecker_Env.qname_and_index)
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
                                           let uu___95_1057 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___95_1057.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___95_1057.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___95_1057.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___95_1057.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___95_1057.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___95_1057.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___95_1057.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___95_1057.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___95_1057.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___95_1057.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___95_1057.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___95_1057.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___95_1057.FStar_TypeChecker_Env.qname_and_index)
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
                                                          let uu___96_1201 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___96_1201.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___96_1201.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___96_1201.FStar_Syntax_Syntax.action_params);
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
                                      (let uu____1268 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1269 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1269))
                                           && (m <> n1) in
                                       if uu____1268
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1278 =
                                           let uu____1279 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1280 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1279 uu____1280 in
                                         failwith uu____1278
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1286 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1286 with
                                      | (univs2,defn) ->
                                          let uu____1291 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1291 with
                                           | (univs',typ) ->
                                               let uu___97_1297 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___97_1297.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___97_1297.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___97_1297.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___98_1300 = ed2 in
                                      let uu____1301 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1302 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1303 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1304 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1305 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1306 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1307 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1308 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1309 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1310 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1311 =
                                        let uu____1312 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1312 in
                                      let uu____1318 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1319 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1320 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___98_1300.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___98_1300.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1301;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1302;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1303;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1304;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1305;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1306;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1307;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1308;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1309;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1310;
                                        FStar_Syntax_Syntax.repr = uu____1311;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1318;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1319;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1320
                                      } in
                                    ((let uu____1323 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1323
                                      then
                                        let uu____1324 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1324
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
      let uu____1328 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1328 with
      | (effect_binders_un,signature_un) ->
          let uu____1338 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1338 with
           | (effect_binders,env1,uu____1349) ->
               let uu____1350 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1350 with
                | (signature,uu____1359) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1368  ->
                           match uu____1368 with
                           | (bv,qual) ->
                               let uu____1375 =
                                 let uu___99_1376 = bv in
                                 let uu____1377 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___99_1376.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___99_1376.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1377
                                 } in
                               (uu____1375, qual)) effect_binders in
                    let uu____1380 =
                      let uu____1385 =
                        let uu____1386 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1386.FStar_Syntax_Syntax.n in
                      match uu____1385 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1394)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1409 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1380 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1426 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1426
                           then
                             let uu____1427 =
                               let uu____1429 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1429 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1427
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1453 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1453 with
                           | (t2,comp,uu____1461) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1472 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1472 with
                          | (repr,_comp) ->
                              ((let uu____1485 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1485
                                then
                                  let uu____1486 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1486
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
                                  let uu____1492 =
                                    let uu____1493 =
                                      let uu____1494 =
                                        let uu____1504 =
                                          let uu____1508 =
                                            let uu____1511 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1512 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1511, uu____1512) in
                                          [uu____1508] in
                                        (wp_type1, uu____1504) in
                                      FStar_Syntax_Syntax.Tm_app uu____1494 in
                                    mk1 uu____1493 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1492 in
                                let effect_signature =
                                  let binders =
                                    let uu____1527 =
                                      let uu____1530 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1530) in
                                    let uu____1531 =
                                      let uu____1535 =
                                        let uu____1536 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1536
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1535] in
                                    uu____1527 :: uu____1531 in
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
                                  let uu____1579 = item in
                                  match uu____1579 with
                                  | (u_item,item1) ->
                                      let uu____1591 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1591 with
                                       | (item2,item_comp) ->
                                           ((let uu____1601 =
                                               let uu____1602 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1602 in
                                             if uu____1601
                                             then
                                               let uu____1603 =
                                                 let uu____1604 =
                                                   let uu____1605 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1606 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1605 uu____1606 in
                                                 FStar_Errors.Err uu____1604 in
                                               raise uu____1603
                                             else ());
                                            (let uu____1608 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1608 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1621 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1621 with
                                | (dmff_env1,uu____1634,bind_wp,bind_elab) ->
                                    let uu____1637 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1637 with
                                     | (dmff_env2,uu____1650,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1654 =
                                             let uu____1655 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1655.FStar_Syntax_Syntax.n in
                                           match uu____1654 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1693 =
                                                 let uu____1701 =
                                                   let uu____1704 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1704 in
                                                 match uu____1701 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1743 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1693 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1765 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1765 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1776 =
                                                          let uu____1777 =
                                                            let uu____1787 =
                                                              let uu____1791
                                                                =
                                                                let uu____1794
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1795
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1794,
                                                                  uu____1795) in
                                                              [uu____1791] in
                                                            (wp_type1,
                                                              uu____1787) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1777 in
                                                        mk1 uu____1776 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1803 =
                                                      let uu____1813 =
                                                        let uu____1814 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1814 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1813 in
                                                    (match uu____1803 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1842
                                                           =
                                                           let error_msg =
                                                             let uu____1844 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1845 =
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
                                                                   (lid,uu____1861))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1844
                                                               uu____1845 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1887
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1887
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
                                                               (lid,uu____1893))
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
                                                             let uu____1913 =
                                                               let uu____1914
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1915
                                                                 =
                                                                 let uu____1916
                                                                   =
                                                                   let uu____1920
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1920,
                                                                    None) in
                                                                 [uu____1916] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1914
                                                                 uu____1915 in
                                                             uu____1913 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1936 =
                                                             let uu____1937 =
                                                               let uu____1941
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1941] in
                                                             b11 ::
                                                               uu____1937 in
                                                           let uu____1944 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1936
                                                             uu____1944
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1954 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1956 =
                                             let uu____1957 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1957.FStar_Syntax_Syntax.n in
                                           match uu____1956 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1995 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1995
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2011 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2013 =
                                             let uu____2014 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2014.FStar_Syntax_Syntax.n in
                                           match uu____2013 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2043 =
                                                 let uu____2044 =
                                                   let uu____2046 =
                                                     let uu____2047 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2047 in
                                                   [uu____2046] in
                                                 FStar_List.append uu____2044
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2043 body what
                                           | uu____2048 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2066 =
                                                let uu____2067 =
                                                  let uu____2068 =
                                                    let uu____2078 =
                                                      let uu____2079 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2079 in
                                                    (t, uu____2078) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2068 in
                                                mk1 uu____2067 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2066) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2102 = f a2 in
                                               [uu____2102]
                                           | x::xs ->
                                               let uu____2106 =
                                                 apply_last1 f xs in
                                               x :: uu____2106 in
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
                                           let uu____2121 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2121 with
                                           | Some (_us,_t) ->
                                               ((let uu____2138 =
                                                   FStar_Ident.string_of_lid
                                                     l' in
                                                 FStar_Util.print1
                                                   "DM4F: Applying override %s\n"
                                                   uu____2138);
                                                (let uu____2139 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2139))
                                           | None  ->
                                               let uu____2144 =
                                                 let uu____2147 = mk_lid name in
                                                 let uu____2148 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2147 uu____2148 in
                                               (match uu____2144 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2157 =
                                                        let uu____2159 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2159 in
                                                      FStar_ST.write sigelts
                                                        uu____2157);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2170 =
                                             let uu____2172 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2173 =
                                               FStar_ST.read sigelts in
                                             uu____2172 :: uu____2173 in
                                           FStar_ST.write sigelts uu____2170);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2183 =
                                              let uu____2185 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2186 =
                                                FStar_ST.read sigelts in
                                              uu____2185 :: uu____2186 in
                                            FStar_ST.write sigelts uu____2183);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2196 =
                                               let uu____2198 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2199 =
                                                 FStar_ST.read sigelts in
                                               uu____2198 :: uu____2199 in
                                             FStar_ST.write sigelts
                                               uu____2196);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2209 =
                                                let uu____2211 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2212 =
                                                  FStar_ST.read sigelts in
                                                uu____2211 :: uu____2212 in
                                              FStar_ST.write sigelts
                                                uu____2209);
                                             (let uu____2220 =
                                                FStar_List.fold_left
                                                  (fun uu____2227  ->
                                                     fun action  ->
                                                       match uu____2227 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2240 =
                                                             let uu____2244 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2244
                                                               params_un in
                                                           (match uu____2240
                                                            with
                                                            | (action_params,env',uu____2250)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2259
                                                                     ->
                                                                    match uu____2259
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2266
                                                                    =
                                                                    let uu___100_2267
                                                                    = bv in
                                                                    let uu____2268
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___100_2267.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___100_2267.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2268
                                                                    } in
                                                                    (uu____2266,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2272
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2272
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
                                                                    uu____2298
                                                                    ->
                                                                    let uu____2299
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2299 in
                                                                    ((
                                                                    let uu____2303
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2303
                                                                    then
                                                                    let uu____2304
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2305
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2306
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2307
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2304
                                                                    uu____2305
                                                                    uu____2306
                                                                    uu____2307
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
                                                                    let uu____2311
                                                                    =
                                                                    let uu____2313
                                                                    =
                                                                    let uu___101_2314
                                                                    = action in
                                                                    let uu____2315
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2316
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___101_2314.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___101_2314.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___101_2314.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2315;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2316
                                                                    } in
                                                                    uu____2313
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2311))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2220 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2336 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2337 =
                                                        let uu____2339 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2339] in
                                                      uu____2336 ::
                                                        uu____2337 in
                                                    let uu____2340 =
                                                      let uu____2341 =
                                                        let uu____2342 =
                                                          let uu____2343 =
                                                            let uu____2353 =
                                                              let uu____2357
                                                                =
                                                                let uu____2360
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2361
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2360,
                                                                  uu____2361) in
                                                              [uu____2357] in
                                                            (repr,
                                                              uu____2353) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2343 in
                                                        mk1 uu____2342 in
                                                      let uu____2369 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2341
                                                        uu____2369 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2340 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2377 =
                                                    let uu____2382 =
                                                      let uu____2383 =
                                                        let uu____2386 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2386 in
                                                      uu____2383.FStar_Syntax_Syntax.n in
                                                    match uu____2382 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2394)
                                                        ->
                                                        let uu____2421 =
                                                          let uu____2430 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2430
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2461 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2421
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2489 =
                                                               let uu____2490
                                                                 =
                                                                 let uu____2493
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2493 in
                                                               uu____2490.FStar_Syntax_Syntax.n in
                                                             (match uu____2489
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2510
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2510
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2519
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2530
                                                                     ->
                                                                    match uu____2530
                                                                    with
                                                                    | 
                                                                    (bv,uu____2534)
                                                                    ->
                                                                    let uu____2535
                                                                    =
                                                                    let uu____2536
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2536
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2535
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2519
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
                                                                    uu____2569
                                                                    ->
                                                                    let uu____2573
                                                                    =
                                                                    let uu____2574
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2574 in
                                                                    failwith
                                                                    uu____2573 in
                                                                    let uu____2577
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2580
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2577,
                                                                    uu____2580)))
                                                              | uu____2590 ->
                                                                  let uu____2591
                                                                    =
                                                                    let uu____2592
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2592 in
                                                                  failwith
                                                                    uu____2591))
                                                    | uu____2597 ->
                                                        let uu____2598 =
                                                          let uu____2599 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2599 in
                                                        failwith uu____2598 in
                                                  (match uu____2377 with
                                                   | (pre,post) ->
                                                       ((let uu____2616 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2618 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2620 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___102_2622
                                                             = ed in
                                                           let uu____2623 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2624 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2625 =
                                                             let uu____2626 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2626) in
                                                           let uu____2632 =
                                                             let uu____2633 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2633) in
                                                           let uu____2639 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2640 =
                                                             let uu____2641 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2641) in
                                                           let uu____2647 =
                                                             let uu____2648 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2648) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2623;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2624;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2625;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2632;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___102_2622.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2639;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2640;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2647;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2654 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2654
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2665
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2665
                                                               then
                                                                 let uu____2666
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2666
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
                                                                    let uu____2676
                                                                    =
                                                                    let uu____2678
                                                                    =
                                                                    let uu____2684
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2684) in
                                                                    Some
                                                                    uu____2678 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2676;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2695
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2695
                                                                 else None in
                                                               let uu____2697
                                                                 =
                                                                 let uu____2699
                                                                   =
                                                                   let uu____2701
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2701 in
                                                                 FStar_List.append
                                                                   uu____2699
                                                                   sigelts' in
                                                               (uu____2697,
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
                (lex_t1,[],[],t,uu____2724,uu____2725);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2727;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_29,uu____2731);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2733;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_30,uu____2737);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2739;_}::[]
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
                let uu____2778 =
                  let uu____2781 =
                    let uu____2782 =
                      let uu____2787 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2787, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2782 in
                  FStar_Syntax_Syntax.mk uu____2781 in
                uu____2778 None r1 in
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
                  let uu____2807 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2807 in
                let hd1 =
                  let uu____2813 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2813 in
                let tl1 =
                  let uu____2815 =
                    let uu____2816 =
                      let uu____2819 =
                        let uu____2820 =
                          let uu____2825 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2825, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2820 in
                      FStar_Syntax_Syntax.mk uu____2819 in
                    uu____2816 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2815 in
                let res =
                  let uu____2838 =
                    let uu____2841 =
                      let uu____2842 =
                        let uu____2847 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2847,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2842 in
                    FStar_Syntax_Syntax.mk uu____2841 in
                  uu____2838 None r2 in
                let uu____2857 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2857 in
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
              let uu____2879 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2879;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2882 ->
              let uu____2884 =
                let uu____2885 =
                  let uu____2886 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2886 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2885 in
              failwith uu____2884
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
            let uu____2896 = FStar_Syntax_Util.type_u () in
            match uu____2896 with
            | (k,uu____2900) ->
                let phi1 =
                  let uu____2902 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2902
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
          let uu____2912 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2912 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2931 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2931 FStar_List.flatten in
              ((let uu____2939 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2939
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
                          let uu____2945 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2951,uu____2952,uu____2953,uu____2954,uu____2955)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2960 -> failwith "Impossible!" in
                          match uu____2945 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2969 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2973,uu____2974,uu____2975,uu____2976,uu____2977)
                        -> lid
                    | uu____2982 -> failwith "Impossible" in
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
                let uu____2988 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____2988
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
                   let uu____3004 =
                     let uu____3006 =
                       let uu____3007 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____3007;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____3006 :: ses1 in
                   (uu____3004, data_ops_ses))))
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3025 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3038 ->
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
           let uu____3068 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3068 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3093 = FStar_Options.set_options t s in
             match uu____3093 with
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
                ((let uu____3110 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3110 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3116 = cps_and_elaborate env1 ne in
           (match uu____3116 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___103_3137 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___103_3137.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___103_3137.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___103_3137.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___104_3138 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___104_3138.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___104_3138.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___104_3138.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___105_3144 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___105_3144.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___105_3144.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___105_3144.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3150 =
             let uu____3155 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3155 in
           (match uu____3150 with
            | (a,wp_a_src) ->
                let uu____3166 =
                  let uu____3171 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3171 in
                (match uu____3166 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3183 =
                         let uu____3185 =
                           let uu____3186 =
                             let uu____3191 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3191) in
                           FStar_Syntax_Syntax.NT uu____3186 in
                         [uu____3185] in
                       FStar_Syntax_Subst.subst uu____3183 wp_b_tgt in
                     let expected_k =
                       let uu____3195 =
                         let uu____3199 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3200 =
                           let uu____3202 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3202] in
                         uu____3199 :: uu____3200 in
                       let uu____3203 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3195 uu____3203 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3224 =
                           let uu____3225 =
                             let uu____3228 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3229 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3228, uu____3229) in
                           FStar_Errors.Error uu____3225 in
                         raise uu____3224 in
                       let uu____3232 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3232 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3251 =
                             let uu____3252 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3252 in
                           if uu____3251
                           then no_reify eff_name
                           else
                             (let uu____3257 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3258 =
                                let uu____3261 =
                                  let uu____3262 =
                                    let uu____3272 =
                                      let uu____3274 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3275 =
                                        let uu____3277 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3277] in
                                      uu____3274 :: uu____3275 in
                                    (repr, uu____3272) in
                                  FStar_Syntax_Syntax.Tm_app uu____3262 in
                                FStar_Syntax_Syntax.mk uu____3261 in
                              uu____3258 None uu____3257) in
                     let uu____3287 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3302,lift_wp)) ->
                           let uu____3315 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3315)
                       | (Some (what,lift),None ) ->
                           ((let uu____3330 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3330
                             then
                               let uu____3331 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3331
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3334 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3334 with
                             | (lift1,comp,uu____3343) ->
                                 let uu____3344 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3344 with
                                  | (uu____3351,lift_wp,lift_elab) ->
                                      let uu____3354 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3355 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3287 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___106_3378 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___106_3378.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___106_3378.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___106_3378.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___106_3378.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___106_3378.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___106_3378.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___106_3378.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___106_3378.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___106_3378.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___106_3378.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___106_3378.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___106_3378.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___106_3378.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___106_3378.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___106_3378.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___106_3378.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___106_3378.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___106_3378.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___106_3378.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___106_3378.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___106_3378.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___106_3378.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___106_3378.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3382,lift1) ->
                                let uu____3389 =
                                  let uu____3394 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3394 in
                                (match uu____3389 with
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
                                         let uu____3416 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3417 =
                                           let uu____3420 =
                                             let uu____3421 =
                                               let uu____3431 =
                                                 let uu____3433 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3434 =
                                                   let uu____3436 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3436] in
                                                 uu____3433 :: uu____3434 in
                                               (lift_wp1, uu____3431) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3421 in
                                           FStar_Syntax_Syntax.mk uu____3420 in
                                         uu____3417 None uu____3416 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3449 =
                                         let uu____3453 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3454 =
                                           let uu____3456 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3457 =
                                             let uu____3459 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3459] in
                                           uu____3456 :: uu____3457 in
                                         uu____3453 :: uu____3454 in
                                       let uu____3460 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3449
                                         uu____3460 in
                                     let uu____3463 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3463 with
                                      | (expected_k2,uu____3469,uu____3470)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___107_3473 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___107_3473.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___107_3473.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___108_3475 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___108_3475.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___108_3475.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___108_3475.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3488 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3488 with
            | (tps1,c1) ->
                let uu____3497 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3497 with
                 | (tps2,env3,us) ->
                     let uu____3508 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3508 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3522 =
                              let uu____3523 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3523 in
                            match uu____3522 with
                            | (uvs1,t) ->
                                let uu____3536 =
                                  let uu____3544 =
                                    let uu____3547 =
                                      let uu____3548 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3548.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3547) in
                                  match uu____3544 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3558,c4)) -> ([], c4)
                                  | (uu____3582,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3600 -> failwith "Impossible" in
                                (match uu____3536 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3629 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3629 with
                                         | (uu____3632,t1) ->
                                             let uu____3634 =
                                               let uu____3635 =
                                                 let uu____3638 =
                                                   let uu____3639 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3640 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3643 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3639 uu____3640
                                                     uu____3643 in
                                                 (uu____3638, r) in
                                               FStar_Errors.Error uu____3635 in
                                             raise uu____3634)
                                      else ();
                                      (let se1 =
                                         let uu___109_3646 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___109_3646.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___109_3646.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___109_3646.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3656,uu____3657,uu____3658) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_3660  ->
                   match uu___83_3660 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3661 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3664,uu____3665,uu____3666) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_3672  ->
                   match uu___83_3672 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3673 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3680 =
             if uvs = []
             then
               let uu____3681 =
                 let uu____3682 = FStar_Syntax_Util.type_u () in
                 fst uu____3682 in
               check_and_gen env2 t uu____3681
             else
               (let uu____3686 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3686 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3692 =
                        let uu____3693 = FStar_Syntax_Util.type_u () in
                        fst uu____3693 in
                      tc_check_trivial_guard env2 t1 uu____3692 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3697 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3697)) in
           (match uu____3680 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___110_3707 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___110_3707.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___110_3707.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___110_3707.FStar_Syntax_Syntax.sigmeta)
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
           let uu____3719 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3719 with
            | (e1,c,g1) ->
                let uu____3730 =
                  let uu____3734 =
                    let uu____3736 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3736 in
                  let uu____3737 =
                    let uu____3740 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3740) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3734 uu____3737 in
                (match uu____3730 with
                 | (e2,uu____3750,g) ->
                     ((let uu____3753 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3753);
                      (let se1 =
                         let uu___111_3755 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___111_3755.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___111_3755.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___111_3755.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3791 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3791
                 then Some q
                 else
                   (let uu____3800 =
                      let uu____3801 =
                        let uu____3804 =
                          let uu____3805 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3806 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3807 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3805 uu____3806 uu____3807 in
                        (uu____3804, r) in
                      FStar_Errors.Error uu____3801 in
                    raise uu____3800) in
           let uu____3810 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3831  ->
                     fun lb  ->
                       match uu____3831 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3855 =
                             let uu____3861 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3861 with
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
                                   | uu____3913 ->
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
                                  (let uu____3921 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3921, quals_opt1))) in
                           (match uu____3855 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3810 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3974 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___84_3976  ->
                                match uu___84_3976 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____3977 -> false)) in
                      if uu____3974
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____3985 =
                    let uu____3988 =
                      let uu____3989 =
                        let uu____3997 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____3997) in
                      FStar_Syntax_Syntax.Tm_let uu____3989 in
                    FStar_Syntax_Syntax.mk uu____3988 in
                  uu____3985 None r in
                let uu____4019 =
                  let uu____4025 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___112_4029 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___112_4029.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___112_4029.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___112_4029.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___112_4029.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___112_4029.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___112_4029.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___112_4029.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___112_4029.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___112_4029.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___112_4029.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___112_4029.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___112_4029.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___112_4029.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___112_4029.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___112_4029.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___112_4029.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___112_4029.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___112_4029.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___112_4029.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___112_4029.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___112_4029.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___112_4029.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____4025 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4037;
                       FStar_Syntax_Syntax.pos = uu____4038;
                       FStar_Syntax_Syntax.vars = uu____4039;_},uu____4040,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4059,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4064 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___85_4067  ->
                             match uu___85_4067 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4069 =
                                   let uu____4070 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4074 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4074)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4070 in
                                 if uu____4069
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___113_4083 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___113_4083.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___113_4083.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4089 -> failwith "impossible" in
                (match uu____4019 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4116 = log env2 in
                       if uu____4116
                       then
                         let uu____4117 =
                           let uu____4118 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4125 =
                                         let uu____4130 =
                                           let uu____4131 =
                                             let uu____4136 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4136.FStar_Syntax_Syntax.fv_name in
                                           uu____4131.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4130 in
                                       match uu____4125 with
                                       | None  -> true
                                       | uu____4143 -> false in
                                     if should_log
                                     then
                                       let uu____4148 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4149 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4148 uu____4149
                                     else "")) in
                           FStar_All.pipe_right uu____4118
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4117
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
             (fun uu___86_4178  ->
                match uu___86_4178 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4179 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4185) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4189 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4194 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4197 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4210 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4223) ->
          let uu____4228 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4228
          then
            let for_export_bundle se1 uu____4247 =
              match uu____4247 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4270,uu____4271) ->
                       let dec =
                         let uu___114_4277 = se1 in
                         let uu____4278 =
                           let uu____4279 =
                             let uu____4283 =
                               let uu____4286 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4286 in
                             (l, us, uu____4283) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4279 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4278;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___114_4277.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___114_4277.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4296,uu____4297,uu____4298) ->
                       let dec =
                         let uu___115_4302 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___115_4302.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___115_4302.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4305 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4317,uu____4318) ->
          let uu____4319 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4319 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4332 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4332
          then
            ([(let uu___116_4340 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___116_4340.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___116_4340.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4342 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___87_4344  ->
                       match uu___87_4344 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4345 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4348 -> true
                       | uu____4349 -> false)) in
             if uu____4342 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4359 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4362 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4365 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4368 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4371 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4381,uu____4382)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4398 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4398
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4419) ->
          let uu____4424 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4424
          then
            let uu____4429 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___117_4435 = se in
                      let uu____4436 =
                        let uu____4437 =
                          let uu____4441 =
                            let uu____4442 =
                              let uu____4447 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4447.FStar_Syntax_Syntax.fv_name in
                            uu____4442.FStar_Syntax_Syntax.v in
                          (uu____4441, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4437 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4436;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___117_4435.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___117_4435.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4429, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4465 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4474 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4483 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                env)
           | uu____4486 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4487 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4493 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4493) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4494,uu____4495,uu____4496) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_4498  ->
                  match uu___88_4498 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4499 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4500,uu____4501,uu____4502) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_4508  ->
                  match uu___88_4508 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4509 -> false))
          -> env
      | uu____4510 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4546 se =
        match uu____4546 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4576 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4576
              then
                let uu____4577 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4577
              else ());
             (let uu____4579 = tc_decl env1 se in
              match uu____4579 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____4605 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4605
                    then
                      let uu____4606 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4609 =
                                 let uu____4610 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4610 "\n" in
                               Prims.strcat s uu____4609) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4606
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4614 =
                      let accum_exports_hidden uu____4632 se1 =
                        match uu____4632 with
                        | (exports1,hidden1) ->
                            let uu____4648 = for_export hidden1 se1 in
                            (match uu____4648 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____4614 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____4698 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4698 with
      | (ses1,exports,env1,uu____4724) ->
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
      (let uu____4749 = FStar_Options.debug_any () in
       if uu____4749
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
         let uu___118_4755 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___118_4755.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___118_4755.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___118_4755.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___118_4755.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___118_4755.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___118_4755.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___118_4755.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___118_4755.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___118_4755.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___118_4755.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___118_4755.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___118_4755.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___118_4755.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___118_4755.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___118_4755.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___118_4755.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___118_4755.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___118_4755.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___118_4755.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___118_4755.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___118_4755.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___118_4755.FStar_TypeChecker_Env.qname_and_index)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____4758 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____4758 with
        | (ses,exports,env3) ->
            ((let uu___119_4776 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___119_4776.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___119_4776.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___119_4776.FStar_Syntax_Syntax.is_interface)
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
        let uu____4792 = tc_decls env decls in
        match uu____4792 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___120_4810 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___120_4810.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___120_4810.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___120_4810.FStar_Syntax_Syntax.is_interface)
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
          let uu___121_4824 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___121_4824.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___121_4824.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___121_4824.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___121_4824.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___121_4824.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___121_4824.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___121_4824.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___121_4824.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___121_4824.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___121_4824.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___121_4824.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___121_4824.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___121_4824.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___121_4824.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___121_4824.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___121_4824.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___121_4824.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___121_4824.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___121_4824.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___121_4824.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___121_4824.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs1 t =
          let uu____4835 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____4835 with
          | (univs2,t1) ->
              ((let uu____4841 =
                  let uu____4842 =
                    let uu____4845 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4845 in
                  FStar_All.pipe_left uu____4842
                    (FStar_Options.Other "Exports") in
                if uu____4841
                then
                  let uu____4846 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____4847 =
                    let uu____4848 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____4848
                      (FStar_String.concat ", ") in
                  let uu____4853 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4846 uu____4847 uu____4853
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____4856 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____4856 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____4874 =
             let uu____4875 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____4876 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4875 uu____4876 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4874);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4883) ->
              let uu____4888 =
                let uu____4889 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4889 in
              if uu____4888
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4897,uu____4898) ->
              let t =
                let uu____4906 =
                  let uu____4909 =
                    let uu____4910 =
                      let uu____4918 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____4918) in
                    FStar_Syntax_Syntax.Tm_arrow uu____4910 in
                  FStar_Syntax_Syntax.mk uu____4909 in
                uu____4906 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____4930,uu____4931,uu____4932) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____4938 =
                let uu____4939 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4939 in
              if uu____4938 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4942,lbs),uu____4944,uu____4945) ->
              let uu____4955 =
                let uu____4956 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4956 in
              if uu____4955
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
              let uu____4973 =
                let uu____4974 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4974 in
              if uu____4973
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____4988 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____4989 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____4992 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4993 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____4994 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____4995 -> () in
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
          let uu___122_5009 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___122_5009.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___122_5009.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5012 =
           let uu____5013 = FStar_Options.lax () in
           Prims.op_Negation uu____5013 in
         if uu____5012 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5019 =
           let uu____5020 = FStar_Options.interactive () in
           Prims.op_Negation uu____5020 in
         if uu____5019
         then
           let uu____5021 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5021 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5031 = tc_partial_modul env modul in
      match uu____5031 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5052 = FStar_Options.debug_any () in
       if uu____5052
       then
         let uu____5053 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5053
       else ());
      (let env1 =
         let uu___123_5057 = env in
         let uu____5058 =
           let uu____5059 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5059 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_5057.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_5057.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_5057.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_5057.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_5057.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_5057.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_5057.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_5057.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_5057.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_5057.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_5057.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_5057.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___123_5057.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___123_5057.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_5057.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_5057.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___123_5057.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___123_5057.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5058;
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_5057.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___123_5057.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_5057.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___123_5057.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_5057.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____5060 = tc_modul env1 m in
       match uu____5060 with
       | (m1,env2) ->
           ((let uu____5068 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5068
             then
               let uu____5069 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5069
             else ());
            (let uu____5072 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5072
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
                       let uu____5099 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5099 with
                       | (univnames1,e) ->
                           let uu___124_5104 = lb in
                           let uu____5105 =
                             let uu____5108 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5108 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___124_5104.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___124_5104.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___124_5104.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___124_5104.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5105
                           } in
                     let uu___125_5109 = se in
                     let uu____5110 =
                       let uu____5111 =
                         let uu____5117 =
                           let uu____5121 = FStar_List.map update lbs in
                           (b, uu____5121) in
                         (uu____5117, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5111 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5110;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___125_5109.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___125_5109.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___125_5109.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5129 -> se in
               let normalized_module =
                 let uu___126_5131 = m1 in
                 let uu____5132 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___126_5131.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5132;
                   FStar_Syntax_Syntax.exports =
                     (uu___126_5131.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___126_5131.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5133 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5133
             else ());
            (m1, env2)))