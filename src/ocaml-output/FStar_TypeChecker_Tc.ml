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
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____183 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____183 with
      | (effect_params_un,signature_un,opening) ->
          let uu____190 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____190 with
           | (effect_params,env,uu____196) ->
               let uu____197 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____197 with
                | (signature,uu____201) ->
                    let ed1 =
                      let uu___91_203 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___91_203.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___91_203.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___91_203.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___91_203.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___91_203.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___91_203.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___91_203.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___91_203.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___91_203.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___91_203.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___91_203.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___91_203.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___91_203.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___91_203.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___91_203.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___91_203.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___91_203.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____207 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
                          let uu___92_225 = ed1 in
                          let uu____226 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____227 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____228 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____229 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____230 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____231 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____232 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____233 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____234 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____235 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____236 =
                            let uu____237 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____237 in
                          let uu____243 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____244 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____245 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___93_248 = a in
                                 let uu____249 =
                                   let uu____250 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____250 in
                                 let uu____256 =
                                   let uu____257 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____257 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___93_248.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___93_248.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___93_248.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___93_248.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____249;
                                   FStar_Syntax_Syntax.action_typ = uu____256
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___92_225.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___92_225.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___92_225.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___92_225.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___92_225.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____226;
                            FStar_Syntax_Syntax.bind_wp = uu____227;
                            FStar_Syntax_Syntax.if_then_else = uu____228;
                            FStar_Syntax_Syntax.ite_wp = uu____229;
                            FStar_Syntax_Syntax.stronger = uu____230;
                            FStar_Syntax_Syntax.close_wp = uu____231;
                            FStar_Syntax_Syntax.assert_p = uu____232;
                            FStar_Syntax_Syntax.assume_p = uu____233;
                            FStar_Syntax_Syntax.null_wp = uu____234;
                            FStar_Syntax_Syntax.trivial = uu____235;
                            FStar_Syntax_Syntax.repr = uu____236;
                            FStar_Syntax_Syntax.return_repr = uu____243;
                            FStar_Syntax_Syntax.bind_repr = uu____244;
                            FStar_Syntax_Syntax.actions = uu____245
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____285 =
                          let uu____286 =
                            let uu____289 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____289, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____286 in
                        raise uu____285 in
                      let uu____294 =
                        let uu____295 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____295.FStar_Syntax_Syntax.n in
                      match uu____294 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____320)::(wp,uu____322)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____331 -> fail signature1)
                      | uu____332 -> fail signature1 in
                    let uu____333 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____333 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____351 =
                           let uu____352 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____352 with
                           | (signature1,uu____360) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____362 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____362 in
                         ((let uu____364 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____364
                           then
                             let uu____365 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____366 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____367 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____368 =
                               let uu____369 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____369 in
                             let uu____370 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____365 uu____366 uu____367 uu____368
                               uu____370
                           else ());
                          (let check_and_gen' env2 uu____383 k =
                             match uu____383 with
                             | (uu____388,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____396 =
                                 let uu____400 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____401 =
                                   let uu____403 =
                                     let uu____404 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____404 in
                                   [uu____403] in
                                 uu____400 :: uu____401 in
                               let uu____405 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____396 uu____405 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____409 = fresh_effect_signature () in
                             match uu____409 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____423 =
                                     let uu____427 =
                                       let uu____428 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____428 in
                                     [uu____427] in
                                   let uu____429 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____423
                                     uu____429 in
                                 let expected_k =
                                   let uu____435 =
                                     let uu____439 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____440 =
                                       let uu____442 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____443 =
                                         let uu____445 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____446 =
                                           let uu____448 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____449 =
                                             let uu____451 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____451] in
                                           uu____448 :: uu____449 in
                                         uu____445 :: uu____446 in
                                       uu____442 :: uu____443 in
                                     uu____439 :: uu____440 in
                                   let uu____452 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____435
                                     uu____452 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____457 =
                                 let uu____458 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____458
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____457 in
                             let expected_k =
                               let uu____466 =
                                 let uu____470 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____471 =
                                   let uu____473 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____474 =
                                     let uu____476 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____477 =
                                       let uu____479 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____479] in
                                     uu____476 :: uu____477 in
                                   uu____473 :: uu____474 in
                                 uu____470 :: uu____471 in
                               let uu____480 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____466 uu____480 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____487 =
                                 let uu____491 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____492 =
                                   let uu____494 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____494] in
                                 uu____491 :: uu____492 in
                               let uu____495 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____487 uu____495 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____499 = FStar_Syntax_Util.type_u () in
                             match uu____499 with
                             | (t,uu____503) ->
                                 let expected_k =
                                   let uu____507 =
                                     let uu____511 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____512 =
                                       let uu____514 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____515 =
                                         let uu____517 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____517] in
                                       uu____514 :: uu____515 in
                                     uu____511 :: uu____512 in
                                   let uu____518 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____507
                                     uu____518 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____523 =
                                 let uu____524 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____524
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____523 in
                             let b_wp_a =
                               let uu____532 =
                                 let uu____536 =
                                   let uu____537 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____537 in
                                 [uu____536] in
                               let uu____538 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____532 uu____538 in
                             let expected_k =
                               let uu____544 =
                                 let uu____548 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____549 =
                                   let uu____551 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____552 =
                                     let uu____554 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____554] in
                                   uu____551 :: uu____552 in
                                 uu____548 :: uu____549 in
                               let uu____555 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____544 uu____555 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____562 =
                                 let uu____566 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____567 =
                                   let uu____569 =
                                     let uu____570 =
                                       let uu____571 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____571
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____570 in
                                   let uu____576 =
                                     let uu____578 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____578] in
                                   uu____569 :: uu____576 in
                                 uu____566 :: uu____567 in
                               let uu____579 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____562 uu____579 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____586 =
                                 let uu____590 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____591 =
                                   let uu____593 =
                                     let uu____594 =
                                       let uu____595 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____595
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____594 in
                                   let uu____600 =
                                     let uu____602 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____602] in
                                   uu____593 :: uu____600 in
                                 uu____590 :: uu____591 in
                               let uu____603 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____586 uu____603 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____610 =
                                 let uu____614 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____614] in
                               let uu____615 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____610 uu____615 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____619 = FStar_Syntax_Util.type_u () in
                             match uu____619 with
                             | (t,uu____623) ->
                                 let expected_k =
                                   let uu____627 =
                                     let uu____631 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____632 =
                                       let uu____634 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____634] in
                                     uu____631 :: uu____632 in
                                   let uu____635 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____627
                                     uu____635 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____638 =
                             let uu____644 =
                               let uu____645 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____645.FStar_Syntax_Syntax.n in
                             match uu____644 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____654 ->
                                 let repr =
                                   let uu____656 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____656 with
                                   | (t,uu____660) ->
                                       let expected_k =
                                         let uu____664 =
                                           let uu____668 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____669 =
                                             let uu____671 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____671] in
                                           uu____668 :: uu____669 in
                                         let uu____672 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____664
                                           uu____672 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____685 =
                                     let uu____688 =
                                       let uu____689 =
                                         let uu____699 =
                                           let uu____701 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____702 =
                                             let uu____704 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____704] in
                                           uu____701 :: uu____702 in
                                         (repr1, uu____699) in
                                       FStar_Syntax_Syntax.Tm_app uu____689 in
                                     FStar_Syntax_Syntax.mk uu____688 in
                                   uu____685 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____723 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____723 wp in
                                 let destruct_repr t =
                                   let uu____734 =
                                     let uu____735 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____735.FStar_Syntax_Syntax.n in
                                   match uu____734 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____744,(t1,uu____746)::(wp,uu____748)::[])
                                       -> (t1, wp)
                                   | uu____782 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____791 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____791
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____792 = fresh_effect_signature () in
                                   match uu____792 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____806 =
                                           let uu____810 =
                                             let uu____811 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____811 in
                                           [uu____810] in
                                         let uu____812 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____806
                                           uu____812 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____818 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____818 in
                                       let wp_g_x =
                                         let uu____822 =
                                           let uu____823 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____824 =
                                             let uu____825 =
                                               let uu____826 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____826 in
                                             [uu____825] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____823 uu____824 in
                                         uu____822 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____837 =
                                             let uu____838 =
                                               let uu____839 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____839
                                                 FStar_Pervasives.snd in
                                             let uu____844 =
                                               let uu____845 =
                                                 let uu____847 =
                                                   let uu____849 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____850 =
                                                     let uu____852 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____853 =
                                                       let uu____855 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____856 =
                                                         let uu____858 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____858] in
                                                       uu____855 :: uu____856 in
                                                     uu____852 :: uu____853 in
                                                   uu____849 :: uu____850 in
                                                 r :: uu____847 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____845 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____838 uu____844 in
                                           uu____837 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____866 =
                                           let uu____870 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____871 =
                                             let uu____873 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____874 =
                                               let uu____876 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____877 =
                                                 let uu____879 =
                                                   let uu____880 =
                                                     let uu____881 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____881 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____880 in
                                                 let uu____882 =
                                                   let uu____884 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____885 =
                                                     let uu____887 =
                                                       let uu____888 =
                                                         let uu____889 =
                                                           let uu____893 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____893] in
                                                         let uu____894 =
                                                           let uu____897 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____897 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____889
                                                           uu____894 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____888 in
                                                     [uu____887] in
                                                   uu____884 :: uu____885 in
                                                 uu____879 :: uu____882 in
                                               uu____876 :: uu____877 in
                                             uu____873 :: uu____874 in
                                           uu____870 :: uu____871 in
                                         let uu____898 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____866
                                           uu____898 in
                                       let uu____901 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____901 with
                                        | (expected_k1,uu____906,uu____907)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___94_911 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___94_911.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___94_911.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___94_911.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___94_911.FStar_TypeChecker_Env.qname_and_index)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____918 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____918 in
                                   let res =
                                     let wp =
                                       let uu____925 =
                                         let uu____926 =
                                           let uu____927 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____927
                                             FStar_Pervasives.snd in
                                         let uu____932 =
                                           let uu____933 =
                                             let uu____935 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____936 =
                                               let uu____938 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____938] in
                                             uu____935 :: uu____936 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____933 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____926 uu____932 in
                                       uu____925 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____946 =
                                       let uu____950 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____951 =
                                         let uu____953 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____953] in
                                       uu____950 :: uu____951 in
                                     let uu____954 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____946
                                       uu____954 in
                                   let uu____957 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____957 with
                                   | (expected_k1,uu____965,uu____966) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____969 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____969 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____981 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____995 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____995 with
                                     | (act_typ,uu____1000,g_t) ->
                                         let env' =
                                           let uu___95_1003 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___95_1003.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___95_1003.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___95_1003.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___95_1003.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___95_1003.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___95_1003.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___95_1003.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___95_1003.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___95_1003.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___95_1003.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___95_1003.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___95_1003.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___95_1003.FStar_TypeChecker_Env.qname_and_index)
                                           } in
                                         ((let uu____1005 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1005
                                           then
                                             let uu____1006 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1007 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1006 uu____1007
                                           else ());
                                          (let uu____1009 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1009 with
                                           | (act_defn,uu____1014,g_a) ->
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
                                               let uu____1018 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1036 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1036 with
                                                      | (bs1,uu____1042) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1049 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1049 in
                                                          let uu____1052 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1052
                                                           with
                                                           | (k1,uu____1059,g)
                                                               -> (k1, g)))
                                                 | uu____1061 ->
                                                     let uu____1062 =
                                                       let uu____1063 =
                                                         let uu____1066 =
                                                           let uu____1067 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1068 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1067
                                                             uu____1068 in
                                                         (uu____1066,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1063 in
                                                     raise uu____1062 in
                                               (match uu____1018 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1075 =
                                                        let uu____1076 =
                                                          let uu____1077 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1077 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1076 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1075);
                                                     (let act_typ2 =
                                                        let uu____1081 =
                                                          let uu____1082 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1082.FStar_Syntax_Syntax.n in
                                                        match uu____1081 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1099 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1099
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1106
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1106
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1126
                                                                    =
                                                                    let uu____1127
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1127] in
                                                                    let uu____1128
                                                                    =
                                                                    let uu____1134
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1134] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1126;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1128;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1135
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1135))
                                                        | uu____1138 ->
                                                            failwith "" in
                                                      let uu____1141 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1141 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___96_1147 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___96_1147.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___96_1147.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___96_1147.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____638 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1163 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1163 in
                               let uu____1166 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1166 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1172 =
                                        let uu____1175 =
                                          let uu____1176 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1176.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1175) in
                                      match uu____1172 with
                                      | ([],uu____1179) -> t1
                                      | (uu____1185,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1186,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1198 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1209 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1209 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1214 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1215 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1215))
                                           && (m <> n1) in
                                       if uu____1214
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1224 =
                                           let uu____1225 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1226 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1225 uu____1226 in
                                         failwith uu____1224
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1232 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1232 with
                                      | (univs2,defn) ->
                                          let uu____1237 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1237 with
                                           | (univs',typ) ->
                                               let uu___97_1243 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___97_1243.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___97_1243.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___97_1243.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___98_1246 = ed2 in
                                      let uu____1247 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1248 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1249 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1250 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1251 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1252 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1253 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1254 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1255 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1256 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1257 =
                                        let uu____1258 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1258 in
                                      let uu____1264 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1265 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1266 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___98_1246.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___98_1246.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1247;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1248;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1249;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1250;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1251;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1252;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1253;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1254;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1255;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1256;
                                        FStar_Syntax_Syntax.repr = uu____1257;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1264;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1265;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1266
                                      } in
                                    ((let uu____1269 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1269
                                      then
                                        let uu____1270 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1270
                                      else ());
                                     ed3)))))))
let cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.eff_decl*
        FStar_Syntax_Syntax.sigelt option)
  =
  fun env  ->
    fun ed  ->
      let uu____1283 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1283 with
      | (effect_binders_un,signature_un) ->
          let uu____1293 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1293 with
           | (effect_binders,env1,uu____1304) ->
               let uu____1305 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1305 with
                | (signature,uu____1314) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1323  ->
                           match uu____1323 with
                           | (bv,qual) ->
                               let uu____1330 =
                                 let uu___99_1331 = bv in
                                 let uu____1332 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___99_1331.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___99_1331.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1332
                                 } in
                               (uu____1330, qual)) effect_binders in
                    let uu____1335 =
                      let uu____1340 =
                        let uu____1341 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1341.FStar_Syntax_Syntax.n in
                      match uu____1340 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1349)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1364 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1335 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1381 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1381
                           then
                             let uu____1382 =
                               let uu____1384 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1384 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1382
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1408 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1408 with
                           | (t2,comp,uu____1416) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1427 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1427 with
                          | (repr,_comp) ->
                              ((let uu____1440 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1440
                                then
                                  let uu____1441 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1441
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
                                  let uu____1447 =
                                    let uu____1448 =
                                      let uu____1449 =
                                        let uu____1459 =
                                          let uu____1463 =
                                            let uu____1466 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1467 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1466, uu____1467) in
                                          [uu____1463] in
                                        (wp_type1, uu____1459) in
                                      FStar_Syntax_Syntax.Tm_app uu____1449 in
                                    mk1 uu____1448 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1447 in
                                let effect_signature =
                                  let binders =
                                    let uu____1482 =
                                      let uu____1485 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1485) in
                                    let uu____1486 =
                                      let uu____1490 =
                                        let uu____1491 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1491
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1490] in
                                    uu____1482 :: uu____1486 in
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
                                  let uu____1534 = item in
                                  match uu____1534 with
                                  | (u_item,item1) ->
                                      let uu____1546 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1546 with
                                       | (item2,item_comp) ->
                                           ((let uu____1556 =
                                               let uu____1557 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1557 in
                                             if uu____1556
                                             then
                                               let uu____1558 =
                                                 let uu____1559 =
                                                   let uu____1560 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1561 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1560 uu____1561 in
                                                 FStar_Errors.Err uu____1559 in
                                               raise uu____1558
                                             else ());
                                            (let uu____1563 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1563 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1576 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1576 with
                                | (dmff_env1,uu____1589,bind_wp,bind_elab) ->
                                    let uu____1592 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1592 with
                                     | (dmff_env2,uu____1605,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1609 =
                                             let uu____1610 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1610.FStar_Syntax_Syntax.n in
                                           match uu____1609 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1648 =
                                                 let uu____1656 =
                                                   let uu____1659 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1659 in
                                                 match uu____1656 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1698 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1648 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1720 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1720 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1731 =
                                                          let uu____1732 =
                                                            let uu____1742 =
                                                              let uu____1746
                                                                =
                                                                let uu____1749
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1750
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1749,
                                                                  uu____1750) in
                                                              [uu____1746] in
                                                            (wp_type1,
                                                              uu____1742) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1732 in
                                                        mk1 uu____1731 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1758 =
                                                      let uu____1768 =
                                                        let uu____1769 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1769 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1768 in
                                                    (match uu____1758 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1797
                                                           =
                                                           let error_msg =
                                                             let uu____1799 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1800 =
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
                                                                   (lid,uu____1816))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1799
                                                               uu____1800 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1842
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1842
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
                                                               (lid,uu____1848))
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
                                                             let uu____1868 =
                                                               let uu____1869
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1870
                                                                 =
                                                                 let uu____1871
                                                                   =
                                                                   let uu____1875
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1875,
                                                                    None) in
                                                                 [uu____1871] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1869
                                                                 uu____1870 in
                                                             uu____1868 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1891 =
                                                             let uu____1892 =
                                                               let uu____1896
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1896] in
                                                             b11 ::
                                                               uu____1892 in
                                                           let uu____1899 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1891
                                                             uu____1899
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1909 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1911 =
                                             let uu____1912 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1912.FStar_Syntax_Syntax.n in
                                           match uu____1911 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1950 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1950
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1966 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____1968 =
                                             let uu____1969 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____1969.FStar_Syntax_Syntax.n in
                                           match uu____1968 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____1998 =
                                                 let uu____1999 =
                                                   let uu____2001 =
                                                     let uu____2002 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2002 in
                                                   [uu____2001] in
                                                 FStar_List.append uu____1999
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____1998 body what
                                           | uu____2003 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2021 =
                                                let uu____2022 =
                                                  let uu____2023 =
                                                    let uu____2033 =
                                                      let uu____2034 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2034 in
                                                    (t, uu____2033) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2023 in
                                                mk1 uu____2022 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2021) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2057 = f a2 in
                                               [uu____2057]
                                           | x::xs ->
                                               let uu____2061 =
                                                 apply_last1 f xs in
                                               x :: uu____2061 in
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
                                           let uu____2076 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2076 with
                                           | Some (_us,_t) ->
                                               ((let uu____2093 =
                                                   FStar_Ident.string_of_lid
                                                     l' in
                                                 FStar_Util.print1
                                                   "DM4F: Applying override %s\n"
                                                   uu____2093);
                                                (let uu____2094 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2094))
                                           | None  ->
                                               let uu____2099 =
                                                 let uu____2102 = mk_lid name in
                                                 let uu____2103 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2102 uu____2103 in
                                               (match uu____2099 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2112 =
                                                        let uu____2114 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2114 in
                                                      FStar_ST.write sigelts
                                                        uu____2112);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2125 =
                                             let uu____2127 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2128 =
                                               FStar_ST.read sigelts in
                                             uu____2127 :: uu____2128 in
                                           FStar_ST.write sigelts uu____2125);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2138 =
                                              let uu____2140 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2141 =
                                                FStar_ST.read sigelts in
                                              uu____2140 :: uu____2141 in
                                            FStar_ST.write sigelts uu____2138);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2151 =
                                               let uu____2153 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2154 =
                                                 FStar_ST.read sigelts in
                                               uu____2153 :: uu____2154 in
                                             FStar_ST.write sigelts
                                               uu____2151);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2164 =
                                                let uu____2166 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2167 =
                                                  FStar_ST.read sigelts in
                                                uu____2166 :: uu____2167 in
                                              FStar_ST.write sigelts
                                                uu____2164);
                                             (let uu____2175 =
                                                FStar_List.fold_left
                                                  (fun uu____2182  ->
                                                     fun action  ->
                                                       match uu____2182 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2195 =
                                                             let uu____2199 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2199
                                                               params_un in
                                                           (match uu____2195
                                                            with
                                                            | (action_params,env',uu____2205)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2214
                                                                     ->
                                                                    match uu____2214
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2221
                                                                    =
                                                                    let uu___100_2222
                                                                    = bv in
                                                                    let uu____2223
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___100_2222.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___100_2222.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2223
                                                                    } in
                                                                    (uu____2221,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2227
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2227
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
                                                                    uu____2253
                                                                    ->
                                                                    let uu____2254
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2254 in
                                                                    ((
                                                                    let uu____2258
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2258
                                                                    then
                                                                    let uu____2259
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2260
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2261
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2262
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2259
                                                                    uu____2260
                                                                    uu____2261
                                                                    uu____2262
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
                                                                    let uu____2266
                                                                    =
                                                                    let uu____2268
                                                                    =
                                                                    let uu___101_2269
                                                                    = action in
                                                                    let uu____2270
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2271
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___101_2269.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___101_2269.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___101_2269.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2270;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2271
                                                                    } in
                                                                    uu____2268
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2266))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2175 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2291 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2292 =
                                                        let uu____2294 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2294] in
                                                      uu____2291 ::
                                                        uu____2292 in
                                                    let uu____2295 =
                                                      let uu____2296 =
                                                        let uu____2297 =
                                                          let uu____2298 =
                                                            let uu____2308 =
                                                              let uu____2312
                                                                =
                                                                let uu____2315
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2316
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2315,
                                                                  uu____2316) in
                                                              [uu____2312] in
                                                            (repr,
                                                              uu____2308) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2298 in
                                                        mk1 uu____2297 in
                                                      let uu____2324 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2296
                                                        uu____2324 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2295 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2332 =
                                                    let uu____2337 =
                                                      let uu____2338 =
                                                        let uu____2341 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2341 in
                                                      uu____2338.FStar_Syntax_Syntax.n in
                                                    match uu____2337 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2349)
                                                        ->
                                                        let uu____2376 =
                                                          let uu____2385 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2385
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2416 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2376
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2444 =
                                                               let uu____2445
                                                                 =
                                                                 let uu____2448
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2448 in
                                                               uu____2445.FStar_Syntax_Syntax.n in
                                                             (match uu____2444
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2465
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2465
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2474
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2485
                                                                     ->
                                                                    match uu____2485
                                                                    with
                                                                    | 
                                                                    (bv,uu____2489)
                                                                    ->
                                                                    let uu____2490
                                                                    =
                                                                    let uu____2491
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2491
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2490
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2474
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
                                                                    uu____2524
                                                                    ->
                                                                    let uu____2528
                                                                    =
                                                                    let uu____2529
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2529 in
                                                                    failwith
                                                                    uu____2528 in
                                                                    let uu____2532
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2535
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2532,
                                                                    uu____2535)))
                                                              | uu____2545 ->
                                                                  let uu____2546
                                                                    =
                                                                    let uu____2547
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2547 in
                                                                  failwith
                                                                    uu____2546))
                                                    | uu____2552 ->
                                                        let uu____2553 =
                                                          let uu____2554 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2554 in
                                                        failwith uu____2553 in
                                                  (match uu____2332 with
                                                   | (pre,post) ->
                                                       ((let uu____2571 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2573 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2575 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___102_2577
                                                             = ed in
                                                           let uu____2578 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2579 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2580 =
                                                             let uu____2581 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2581) in
                                                           let uu____2587 =
                                                             let uu____2588 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2588) in
                                                           let uu____2594 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2595 =
                                                             let uu____2596 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2596) in
                                                           let uu____2602 =
                                                             let uu____2603 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2603) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2578;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2579;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2580;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2587;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___102_2577.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2594;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2595;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2602;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2609 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2609
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2620
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2620
                                                               then
                                                                 let uu____2621
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2621
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
                                                                    let uu____2631
                                                                    =
                                                                    let uu____2633
                                                                    =
                                                                    let uu____2639
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2639) in
                                                                    Some
                                                                    uu____2633 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2631;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2650
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2650
                                                                 else None in
                                                               let uu____2652
                                                                 =
                                                                 let uu____2654
                                                                   =
                                                                   let uu____2656
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2656 in
                                                                 FStar_List.append
                                                                   uu____2654
                                                                   sigelts' in
                                                               (uu____2652,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t env ses quals lids =
  match ses with
  | {
      FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ
        (lex_t1,[],[],t,uu____2700,uu____2701);
      FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = [];
      FStar_Syntax_Syntax.sigmeta = uu____2703;_}::{
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       FStar_Syntax_Syntax.Sig_datacon
                                                       (lex_top1,[],_t_top,_lex_t_top,_0_29,uu____2707);
                                                     FStar_Syntax_Syntax.sigrng
                                                       = r1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = [];
                                                     FStar_Syntax_Syntax.sigmeta
                                                       = uu____2709;_}::
      {
        FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
          (lex_cons,[],_t_cons,_lex_t_cons,_0_30,uu____2713);
        FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = uu____2715;_}::[]
      when
      ((_0_29 = (Prims.parse_int "0")) && (_0_30 = (Prims.parse_int "0"))) &&
        (((FStar_Ident.lid_equals lex_t1 FStar_Syntax_Const.lex_t_lid) &&
            (FStar_Ident.lid_equals lex_top1 FStar_Syntax_Const.lextop_lid))
           &&
           (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))
      ->
      let u = FStar_Syntax_Syntax.new_univ_name (Some r) in
      let t1 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u)) None r in
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
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
        } in
      let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
      let lex_top_t =
        let uu____2754 =
          let uu____2757 =
            let uu____2758 =
              let uu____2763 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
                  FStar_Syntax_Syntax.Delta_constant None in
              (uu____2763, [FStar_Syntax_Syntax.U_name utop]) in
            FStar_Syntax_Syntax.Tm_uinst uu____2758 in
          FStar_Syntax_Syntax.mk uu____2757 in
        uu____2754 None r1 in
      let lex_top_t1 = FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
      let dc_lextop =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_datacon
               (lex_top1, [utop], lex_top_t1, FStar_Syntax_Const.lex_t_lid,
                 (Prims.parse_int "0"), []));
          FStar_Syntax_Syntax.sigrng = r1;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
        } in
      let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
      let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
      let lex_cons_t =
        let a =
          let uu____2783 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type
                 (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
          FStar_Syntax_Syntax.new_bv (Some r2) uu____2783 in
        let hd1 =
          let uu____2789 = FStar_Syntax_Syntax.bv_to_name a in
          FStar_Syntax_Syntax.new_bv (Some r2) uu____2789 in
        let tl1 =
          let uu____2791 =
            let uu____2792 =
              let uu____2795 =
                let uu____2796 =
                  let uu____2801 =
                    FStar_Syntax_Syntax.fvar
                      (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid
                         r2) FStar_Syntax_Syntax.Delta_constant None in
                  (uu____2801, [FStar_Syntax_Syntax.U_name ucons2]) in
                FStar_Syntax_Syntax.Tm_uinst uu____2796 in
              FStar_Syntax_Syntax.mk uu____2795 in
            uu____2792 None r2 in
          FStar_Syntax_Syntax.new_bv (Some r2) uu____2791 in
        let res =
          let uu____2814 =
            let uu____2817 =
              let uu____2818 =
                let uu____2823 =
                  FStar_Syntax_Syntax.fvar
                    (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid
                       r2) FStar_Syntax_Syntax.Delta_constant None in
                (uu____2823,
                  [FStar_Syntax_Syntax.U_max
                     [FStar_Syntax_Syntax.U_name ucons1;
                     FStar_Syntax_Syntax.U_name ucons2]]) in
              FStar_Syntax_Syntax.Tm_uinst uu____2818 in
            FStar_Syntax_Syntax.mk uu____2817 in
          uu____2814 None r2 in
        let uu____2833 = FStar_Syntax_Syntax.mk_Total res in
        FStar_Syntax_Util.arrow
          [(a, (Some FStar_Syntax_Syntax.imp_tag)); (hd1, None); (tl1, None)]
          uu____2833 in
      let lex_cons_t1 =
        FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2] lex_cons_t in
      let dc_lexcons =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_datacon
               (lex_cons, [ucons1; ucons2], lex_cons_t1,
                 FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), []));
          FStar_Syntax_Syntax.sigrng = r2;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
        } in
      let uu____2855 = FStar_TypeChecker_Env.get_range env in
      {
        FStar_Syntax_Syntax.sigel =
          (FStar_Syntax_Syntax.Sig_bundle ([tc; dc_lextop; dc_lexcons], lids));
        FStar_Syntax_Syntax.sigrng = uu____2855;
        FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
      }
  | uu____2858 ->
      let uu____2860 =
        let uu____2861 =
          let uu____2862 =
            FStar_Syntax_Syntax.mk_sigelt
              (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
          FStar_Syntax_Print.sigelt_to_string uu____2862 in
        FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2861 in
      failwith uu____2860
let tc_assume:
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
            let uu____2883 = FStar_Syntax_Util.type_u () in
            match uu____2883 with
            | (k,uu____2887) ->
                let phi1 =
                  let uu____2889 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2889
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____2891 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____2891 with
                  | (us,phi2) ->
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_assume (lid, us, phi2));
                        FStar_Syntax_Syntax.sigrng = r;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta
                      }))
let tc_inductive:
  FStar_TypeChecker_Env.env ->
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
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let uu____2920 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____2920 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2939 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____2939 FStar_List.flatten in
              ((let uu____2947 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2947
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env2 in
                        if Prims.op_Negation b
                        then
                          let uu____2953 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2959,uu____2960,uu____2961,uu____2962,uu____2963)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2968 -> failwith "Impossible!" in
                          match uu____2953 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2977 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2981,uu____2982,uu____2983,uu____2984,uu____2985)
                        -> lid
                    | uu____2990 -> failwith "Impossible" in
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
                let res =
                  let uu____3001 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Syntax_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____3001
                  then ([sig_bndle], data_ops_ses)
                  else
                    (let is_unopteq =
                       FStar_List.existsb
                         (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                     let ses1 =
                       if is_unopteq
                       then
                         FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume in
                     let uu____3017 =
                       let uu____3019 =
                         let uu____3020 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____3020;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta
                         } in
                       uu____3019 :: ses1 in
                     (uu____3017, data_ops_ses)) in
                (let uu____3026 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive" in
                 ());
                res))
let tc_decl:
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3048 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3061 ->
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
           let uu____3091 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3091 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3116 = FStar_Options.set_options t s in
             match uu____3116 with
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
                ((let uu____3133 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3133 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3139 = cps_and_elaborate env1 ne in
           (match uu____3139 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___103_3160 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___103_3160.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___103_3160.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___103_3160.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___104_3161 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___104_3161.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___104_3161.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___104_3161.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___105_3167 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___105_3167.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___105_3167.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___105_3167.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3173 =
             let uu____3178 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3178 in
           (match uu____3173 with
            | (a,wp_a_src) ->
                let uu____3189 =
                  let uu____3194 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3194 in
                (match uu____3189 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3206 =
                         let uu____3208 =
                           let uu____3209 =
                             let uu____3214 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3214) in
                           FStar_Syntax_Syntax.NT uu____3209 in
                         [uu____3208] in
                       FStar_Syntax_Subst.subst uu____3206 wp_b_tgt in
                     let expected_k =
                       let uu____3218 =
                         let uu____3222 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3223 =
                           let uu____3225 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3225] in
                         uu____3222 :: uu____3223 in
                       let uu____3226 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3218 uu____3226 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3247 =
                           let uu____3248 =
                             let uu____3251 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3252 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3251, uu____3252) in
                           FStar_Errors.Error uu____3248 in
                         raise uu____3247 in
                       let uu____3255 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3255 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3274 =
                             let uu____3275 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3275 in
                           if uu____3274
                           then no_reify eff_name
                           else
                             (let uu____3280 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3281 =
                                let uu____3284 =
                                  let uu____3285 =
                                    let uu____3295 =
                                      let uu____3297 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3298 =
                                        let uu____3300 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3300] in
                                      uu____3297 :: uu____3298 in
                                    (repr, uu____3295) in
                                  FStar_Syntax_Syntax.Tm_app uu____3285 in
                                FStar_Syntax_Syntax.mk uu____3284 in
                              uu____3281 None uu____3280) in
                     let uu____3310 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3325,lift_wp)) ->
                           let uu____3338 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3338)
                       | (Some (what,lift),None ) ->
                           ((let uu____3353 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3353
                             then
                               let uu____3354 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3354
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3357 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3357 with
                             | (lift1,comp,uu____3366) ->
                                 let uu____3367 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3367 with
                                  | (uu____3374,lift_wp,lift_elab) ->
                                      let uu____3377 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3378 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3310 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___106_3401 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___106_3401.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___106_3401.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___106_3401.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___106_3401.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___106_3401.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___106_3401.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___106_3401.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___106_3401.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___106_3401.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___106_3401.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___106_3401.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___106_3401.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___106_3401.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___106_3401.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___106_3401.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___106_3401.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___106_3401.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___106_3401.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___106_3401.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___106_3401.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___106_3401.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___106_3401.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___106_3401.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3405,lift1) ->
                                let uu____3412 =
                                  let uu____3417 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3417 in
                                (match uu____3412 with
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
                                         let uu____3439 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3440 =
                                           let uu____3443 =
                                             let uu____3444 =
                                               let uu____3454 =
                                                 let uu____3456 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3457 =
                                                   let uu____3459 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3459] in
                                                 uu____3456 :: uu____3457 in
                                               (lift_wp1, uu____3454) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3444 in
                                           FStar_Syntax_Syntax.mk uu____3443 in
                                         uu____3440 None uu____3439 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3472 =
                                         let uu____3476 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3477 =
                                           let uu____3479 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3480 =
                                             let uu____3482 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3482] in
                                           uu____3479 :: uu____3480 in
                                         uu____3476 :: uu____3477 in
                                       let uu____3483 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3472
                                         uu____3483 in
                                     let uu____3486 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3486 with
                                      | (expected_k2,uu____3492,uu____3493)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___107_3496 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___107_3496.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___107_3496.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___108_3498 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___108_3498.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___108_3498.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___108_3498.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3511 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3511 with
            | (tps1,c1) ->
                let uu____3520 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3520 with
                 | (tps2,env3,us) ->
                     let uu____3531 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3531 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3545 =
                              let uu____3546 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3546 in
                            match uu____3545 with
                            | (uvs1,t) ->
                                let uu____3559 =
                                  let uu____3567 =
                                    let uu____3570 =
                                      let uu____3571 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3571.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3570) in
                                  match uu____3567 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3581,c4)) -> ([], c4)
                                  | (uu____3605,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3623 -> failwith "Impossible" in
                                (match uu____3559 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3652 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3652 with
                                         | (uu____3655,t1) ->
                                             let uu____3657 =
                                               let uu____3658 =
                                                 let uu____3661 =
                                                   let uu____3662 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3663 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3666 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3662 uu____3663
                                                     uu____3666 in
                                                 (uu____3661, r) in
                                               FStar_Errors.Error uu____3658 in
                                             raise uu____3657)
                                      else ();
                                      (let se1 =
                                         let uu___109_3669 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___109_3669.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___109_3669.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___109_3669.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3679,uu____3680,uu____3681) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_3683  ->
                   match uu___83_3683 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3684 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3687,uu____3688,uu____3689) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_3695  ->
                   match uu___83_3695 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3696 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3703 =
             if uvs = []
             then
               let uu____3704 =
                 let uu____3705 = FStar_Syntax_Util.type_u () in
                 fst uu____3705 in
               check_and_gen env2 t uu____3704
             else
               (let uu____3709 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3709 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3715 =
                        let uu____3716 = FStar_Syntax_Util.type_u () in
                        fst uu____3716 in
                      tc_check_trivial_guard env2 t1 uu____3715 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3720 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3720)) in
           (match uu____3703 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___110_3730 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___110_3730.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___110_3730.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___110_3730.FStar_Syntax_Syntax.sigmeta)
                  } in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____3737 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____3737 with
            | (uu____3744,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit in
           let uu____3752 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3752 with
            | (e1,c,g1) ->
                let uu____3763 =
                  let uu____3767 =
                    let uu____3769 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3769 in
                  let uu____3770 =
                    let uu____3773 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3773) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3767 uu____3770 in
                (match uu____3763 with
                 | (e2,uu____3783,g) ->
                     ((let uu____3786 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3786);
                      (let se1 =
                         let uu___111_3788 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___111_3788.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___111_3788.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___111_3788.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3824 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3824
                 then Some q
                 else
                   (let uu____3833 =
                      let uu____3834 =
                        let uu____3837 =
                          let uu____3838 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3839 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3840 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3838 uu____3839 uu____3840 in
                        (uu____3837, r) in
                      FStar_Errors.Error uu____3834 in
                    raise uu____3833) in
           let uu____3843 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3864  ->
                     fun lb  ->
                       match uu____3864 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3888 =
                             let uu____3894 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3894 with
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
                                   | uu____3938 ->
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
                                  (let uu____3946 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3946, quals_opt1))) in
                           (match uu____3888 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3843 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3999 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___84_4001  ->
                                match uu___84_4001 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____4002 -> false)) in
                      if uu____3999
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____4010 =
                    let uu____4013 =
                      let uu____4014 =
                        let uu____4022 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____4022) in
                      FStar_Syntax_Syntax.Tm_let uu____4014 in
                    FStar_Syntax_Syntax.mk uu____4013 in
                  uu____4010 None r in
                let uu____4044 =
                  let uu____4050 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___112_4054 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___112_4054.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___112_4054.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___112_4054.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___112_4054.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___112_4054.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___112_4054.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___112_4054.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___112_4054.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___112_4054.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___112_4054.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___112_4054.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___112_4054.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___112_4054.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___112_4054.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___112_4054.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___112_4054.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___112_4054.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___112_4054.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___112_4054.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___112_4054.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___112_4054.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___112_4054.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____4050 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4062;
                       FStar_Syntax_Syntax.pos = uu____4063;
                       FStar_Syntax_Syntax.vars = uu____4064;_},uu____4065,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4084,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4089 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___85_4092  ->
                             match uu___85_4092 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4094 =
                                   let uu____4095 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4099 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4099)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4095 in
                                 if uu____4094
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___113_4108 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___113_4108.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___113_4108.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4114 -> failwith "impossible" in
                (match uu____4044 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4141 = log env2 in
                       if uu____4141
                       then
                         let uu____4142 =
                           let uu____4143 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4150 =
                                         let uu____4155 =
                                           let uu____4156 =
                                             let uu____4158 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4158.FStar_Syntax_Syntax.fv_name in
                                           uu____4156.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4155 in
                                       match uu____4150 with
                                       | None  -> true
                                       | uu____4162 -> false in
                                     if should_log
                                     then
                                       let uu____4167 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4168 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4167 uu____4168
                                     else "")) in
                           FStar_All.pipe_right uu____4143
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4142
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
             (fun uu___86_4197  ->
                match uu___86_4197 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4198 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4204) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4208 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4213 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4216 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4229 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4242) ->
          let uu____4247 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4247
          then
            let for_export_bundle se1 uu____4266 =
              match uu____4266 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4289,uu____4290) ->
                       let dec =
                         let uu___114_4296 = se1 in
                         let uu____4297 =
                           let uu____4298 =
                             let uu____4302 =
                               let uu____4305 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4305 in
                             (l, us, uu____4302) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4298 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4297;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___114_4296.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___114_4296.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4315,uu____4316,uu____4317) ->
                       let dec =
                         let uu___115_4321 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___115_4321.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___115_4321.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4324 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4336,uu____4337,uu____4338) ->
          let uu____4339 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4339 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4352 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4352
          then
            ([(let uu___116_4360 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___116_4360.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___116_4360.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4362 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___87_4364  ->
                       match uu___87_4364 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4365 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4368 -> true
                       | uu____4369 -> false)) in
             if uu____4362 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4379 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4382 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4385 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4388 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4391 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4401,uu____4402)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4414 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4414
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4431) ->
          let uu____4436 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4436
          then
            let uu____4441 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___117_4447 = se in
                      let uu____4448 =
                        let uu____4449 =
                          let uu____4453 =
                            let uu____4454 =
                              let uu____4456 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4456.FStar_Syntax_Syntax.fv_name in
                            uu____4454.FStar_Syntax_Syntax.v in
                          (uu____4453, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4449 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4448;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___117_4447.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___117_4447.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4441, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4471 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4480 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4489 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                env)
           | uu____4492 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4493 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4499 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4499) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4500,uu____4501,uu____4502) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_4504  ->
                  match uu___88_4504 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4505 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4506,uu____4507,uu____4508) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_4514  ->
                  match uu___88_4514 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4515 -> false))
          -> env
      | uu____4516 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4552 se =
        match uu____4552 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4582 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4582
              then
                let uu____4583 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4583
              else ());
             (let uu____4585 = tc_decl env1 se in
              match uu____4585 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let env2 =
                    FStar_All.pipe_right ses'1
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  (FStar_Syntax_Unionfind.reset ();
                   (let uu____4622 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4622
                    then
                      let uu____4623 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4626 =
                                 let uu____4627 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4627 "\n" in
                               Prims.strcat s uu____4626) "" ses'1 in
                      FStar_Util.print1 "Checked: %s\n" uu____4623
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses'1;
                   (let uu____4631 =
                      let accum_exports_hidden uu____4649 se1 =
                        match uu____4649 with
                        | (exports1,hidden1) ->
                            let uu____4665 = for_export hidden1 se1 in
                            (match uu____4665 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'1 in
                    match uu____4631 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses'1 ses1), exports1, env2,
                           hidden1), ses_elaborated1))))) in
      let uu____4715 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4715 with
      | (ses1,exports,env1,uu____4741) ->
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
      (let uu____4766 = FStar_Options.debug_any () in
       if uu____4766
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
         let uu___118_4772 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___118_4772.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___118_4772.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___118_4772.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___118_4772.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___118_4772.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___118_4772.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___118_4772.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___118_4772.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___118_4772.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___118_4772.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___118_4772.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___118_4772.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___118_4772.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___118_4772.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___118_4772.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___118_4772.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___118_4772.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___118_4772.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___118_4772.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___118_4772.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___118_4772.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___118_4772.FStar_TypeChecker_Env.qname_and_index)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____4775 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____4775 with
        | (ses,exports,env3) ->
            ((let uu___119_4793 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___119_4793.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___119_4793.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___119_4793.FStar_Syntax_Syntax.is_interface)
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
        let uu____4809 = tc_decls env decls in
        match uu____4809 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___120_4827 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___120_4827.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___120_4827.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___120_4827.FStar_Syntax_Syntax.is_interface)
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
          let uu___121_4841 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___121_4841.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___121_4841.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___121_4841.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___121_4841.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___121_4841.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___121_4841.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___121_4841.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___121_4841.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___121_4841.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___121_4841.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___121_4841.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___121_4841.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___121_4841.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___121_4841.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___121_4841.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___121_4841.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___121_4841.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___121_4841.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___121_4841.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___121_4841.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___121_4841.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs1 t =
          let uu____4852 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____4852 with
          | (univs2,t1) ->
              ((let uu____4858 =
                  let uu____4859 =
                    let uu____4862 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4862 in
                  FStar_All.pipe_left uu____4859
                    (FStar_Options.Other "Exports") in
                if uu____4858
                then
                  let uu____4863 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____4864 =
                    let uu____4865 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____4865
                      (FStar_String.concat ", ") in
                  let uu____4870 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4863 uu____4864 uu____4870
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____4873 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____4873 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____4891 =
             let uu____4892 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____4893 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4892 uu____4893 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4891);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4900) ->
              let uu____4905 =
                let uu____4906 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4906 in
              if uu____4905
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4914,uu____4915) ->
              let t =
                let uu____4923 =
                  let uu____4926 =
                    let uu____4927 =
                      let uu____4935 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____4935) in
                    FStar_Syntax_Syntax.Tm_arrow uu____4927 in
                  FStar_Syntax_Syntax.mk uu____4926 in
                uu____4923 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____4947,uu____4948,uu____4949) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____4955 =
                let uu____4956 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4956 in
              if uu____4955 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4959,lbs),uu____4961,uu____4962) ->
              let uu____4972 =
                let uu____4973 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4973 in
              if uu____4972
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
              let uu____4986 =
                let uu____4987 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4987 in
              if uu____4986
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5001 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5002 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5006 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5007 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5008 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5009 -> () in
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
          let uu___122_5023 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___122_5023.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___122_5023.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5026 =
           let uu____5027 = FStar_Options.lax () in
           Prims.op_Negation uu____5027 in
         if uu____5026 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5033 =
           let uu____5034 = FStar_Options.interactive () in
           Prims.op_Negation uu____5034 in
         if uu____5033
         then
           let uu____5035 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5035 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5045 = tc_partial_modul env modul in
      match uu____5045 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5066 = FStar_Options.debug_any () in
       if uu____5066
       then
         let uu____5067 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5067
       else ());
      (let env1 =
         let uu___123_5071 = env in
         let uu____5072 =
           let uu____5073 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5073 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_5071.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_5071.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_5071.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_5071.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_5071.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_5071.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_5071.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_5071.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_5071.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_5071.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_5071.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_5071.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___123_5071.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___123_5071.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_5071.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_5071.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___123_5071.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___123_5071.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5072;
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_5071.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___123_5071.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_5071.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___123_5071.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_5071.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____5074 = tc_modul env1 m in
       match uu____5074 with
       | (m1,env2) ->
           ((let uu____5082 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5082
             then
               let uu____5083 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5083
             else ());
            (let uu____5086 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5086
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
                       let uu____5113 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5113 with
                       | (univnames1,e) ->
                           let uu___124_5118 = lb in
                           let uu____5119 =
                             let uu____5122 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5122 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___124_5118.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___124_5118.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___124_5118.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___124_5118.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5119
                           } in
                     let uu___125_5123 = se in
                     let uu____5124 =
                       let uu____5125 =
                         let uu____5131 =
                           let uu____5135 = FStar_List.map update lbs in
                           (b, uu____5135) in
                         (uu____5131, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5125 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5124;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___125_5123.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___125_5123.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___125_5123.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5143 -> se in
               let normalized_module =
                 let uu___126_5145 = m1 in
                 let uu____5146 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___126_5145.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5146;
                   FStar_Syntax_Syntax.exports =
                     (uu___126_5145.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___126_5145.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5147 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5147
             else ());
            (m1, env2)))