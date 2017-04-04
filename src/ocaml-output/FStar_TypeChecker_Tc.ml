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
          let uu___86_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___86_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___86_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___86_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___86_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___86_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___86_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___86_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___86_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___86_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___86_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___86_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___86_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___86_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___86_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___86_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___86_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___86_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___86_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___86_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___86_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___86_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___86_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___86_12.FStar_TypeChecker_Env.use_bv_sorts);
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
          let uu___87_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___87_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___87_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___87_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___87_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___87_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___87_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___87_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___87_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___87_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___87_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___87_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___87_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___87_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___87_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___87_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___87_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___87_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___87_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___87_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___87_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___87_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___87_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___87_24.FStar_TypeChecker_Env.use_bv_sorts);
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
          Prims.raise uu____131 in
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
                      let uu___88_257 = ed in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___88_257.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___88_257.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___88_257.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___88_257.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___88_257.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___88_257.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___88_257.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___88_257.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___88_257.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___88_257.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___88_257.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___88_257.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___88_257.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___88_257.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___88_257.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___88_257.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___88_257.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___88_257.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____261 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts) in
                            ([], t1) in
                          let uu___89_279 = ed1 in
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
                            Prims.snd uu____291 in
                          let uu____297 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____298 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____299 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___90_302 = a in
                                 let uu____303 =
                                   let uu____304 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   Prims.snd uu____304 in
                                 let uu____310 =
                                   let uu____311 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   Prims.snd uu____311 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___90_302.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___90_302.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___90_302.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____303;
                                   FStar_Syntax_Syntax.action_typ = uu____310
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___89_279.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___89_279.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___89_279.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___89_279.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___89_279.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___89_279.FStar_Syntax_Syntax.signature);
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
                        Prims.raise uu____339 in
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
                                 FStar_All.pipe_right uu____512 Prims.fst in
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
                                 FStar_All.pipe_right uu____578 Prims.fst in
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
                                         Prims.fst in
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
                                         Prims.fst in
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
                                                 Prims.snd in
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
                                                (Prims.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___91_965 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___91_965.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___91_965.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___91_965.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___91_965.FStar_TypeChecker_Env.qname_and_index)
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
                                             Prims.snd in
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
                                           (Prims.snd
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
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1046 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1046 with
                                     | (act_typ,uu____1051,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env1 act_typ in
                                         ((let uu____1055 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1055
                                           then
                                             let uu____1056 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1057 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1056 uu____1057
                                           else ());
                                          (let uu____1059 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1059 with
                                           | (act_defn,uu____1064,g_a) ->
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
                                               let uu____1068 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1086 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1086 with
                                                      | (bs1,uu____1092) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1099 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1099 in
                                                          let uu____1102 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1102
                                                           with
                                                           | (k1,uu____1109,g)
                                                               -> (k1, g)))
                                                 | uu____1111 ->
                                                     let uu____1112 =
                                                       let uu____1113 =
                                                         let uu____1116 =
                                                           let uu____1117 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1118 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1117
                                                             uu____1118 in
                                                         (uu____1116,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1113 in
                                                     Prims.raise uu____1112 in
                                               (match uu____1068 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1125 =
                                                        let uu____1126 =
                                                          let uu____1127 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1127 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1126 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1125);
                                                     (let act_typ2 =
                                                        let uu____1131 =
                                                          let uu____1132 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1132.FStar_Syntax_Syntax.n in
                                                        match uu____1131 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1149 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1149
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1156
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1156
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1176
                                                                    =
                                                                    let uu____1177
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1177] in
                                                                    let uu____1178
                                                                    =
                                                                    let uu____1184
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1184] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1176;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1178;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1185
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1185))
                                                        | uu____1188 ->
                                                            failwith "" in
                                                      let uu____1191 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1191 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___92_1197 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___92_1197.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___92_1197.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
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
                                 let uu____1213 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1213 in
                               let uu____1216 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1216 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1222 =
                                        let uu____1225 =
                                          let uu____1226 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1226.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1225) in
                                      match uu____1222 with
                                      | ([],uu____1229) -> t1
                                      | (uu____1235,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1236,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1248 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1259 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1259 in
                                      let m =
                                        FStar_List.length (Prims.fst ts1) in
                                      (let uu____1264 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1265 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts1) in
                                             Prims.op_Negation uu____1265))
                                           && (m <> n1) in
                                       if uu____1264
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1274 =
                                           let uu____1275 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1276 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1275 uu____1276 in
                                         failwith uu____1274
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1282 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1282 with
                                      | (univs2,defn) ->
                                          let uu____1287 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1287 with
                                           | (univs',typ) ->
                                               let uu___93_1293 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___93_1293.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___93_1293.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let nunivs = FStar_List.length univs1 in
                                    let ed3 =
                                      let uu___94_1298 = ed2 in
                                      let uu____1299 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1300 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1301 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1302 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1303 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1304 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1305 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1306 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1307 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1308 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1309 =
                                        let uu____1310 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        Prims.snd uu____1310 in
                                      let uu____1316 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1317 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1318 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___94_1298.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___94_1298.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___94_1298.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1299;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1300;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1301;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1302;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1303;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1304;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1305;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1306;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1307;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1308;
                                        FStar_Syntax_Syntax.repr = uu____1309;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1316;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1317;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1318
                                      } in
                                    ((let uu____1321 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1321
                                      then
                                        let uu____1322 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1322
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
      let uu____1326 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1326 with
      | (effect_binders_un,signature_un) ->
          let uu____1336 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1336 with
           | (effect_binders,env1,uu____1347) ->
               let uu____1348 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1348 with
                | (signature,uu____1357) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1366  ->
                           match uu____1366 with
                           | (bv,qual) ->
                               let uu____1373 =
                                 let uu___95_1374 = bv in
                                 let uu____1375 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___95_1374.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___95_1374.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1375
                                 } in
                               (uu____1373, qual)) effect_binders in
                    let uu____1378 =
                      let uu____1383 =
                        let uu____1384 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1384.FStar_Syntax_Syntax.n in
                      match uu____1383 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1392)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1407 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1378 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1424 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1424
                           then
                             let uu____1425 =
                               let uu____1427 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1427 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1425
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders1 in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1437 =
                             FStar_TypeChecker_TcTerm.tc_term env1 t1 in
                           match uu____1437 with
                           | (t2,comp,uu____1445) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1456 =
                           open_and_check ed.FStar_Syntax_Syntax.repr in
                         (match uu____1456 with
                          | (repr,_comp) ->
                              ((let uu____1467 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1467
                                then
                                  let uu____1468 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1468
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
                                  let uu____1474 =
                                    let uu____1475 =
                                      let uu____1476 =
                                        let uu____1486 =
                                          let uu____1490 =
                                            let uu____1493 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1494 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1493, uu____1494) in
                                          [uu____1490] in
                                        (wp_type1, uu____1486) in
                                      FStar_Syntax_Syntax.Tm_app uu____1476 in
                                    mk1 uu____1475 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1474 in
                                let effect_signature =
                                  let binders =
                                    let uu____1509 =
                                      let uu____1512 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1512) in
                                    let uu____1513 =
                                      let uu____1517 =
                                        let uu____1518 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1518
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1517] in
                                    uu____1509 :: uu____1513 in
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
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       (Prims.strcat
                                          (FStar_Ident.text_of_lid
                                             ed.FStar_Syntax_Syntax.mname)
                                          (Prims.strcat "_" name)))
                                    FStar_Range.dummyRange in
                                let elaborate_and_star dmff_env1 item =
                                  let uu____1551 = item in
                                  match uu____1551 with
                                  | (u_item,item1) ->
                                      let uu____1563 = open_and_check item1 in
                                      (match uu____1563 with
                                       | (item2,item_comp) ->
                                           ((let uu____1573 =
                                               let uu____1574 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1574 in
                                             if uu____1573
                                             then
                                               let uu____1575 =
                                                 let uu____1576 =
                                                   let uu____1577 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1578 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1577 uu____1578 in
                                                 FStar_Errors.Err uu____1576 in
                                               Prims.raise uu____1575
                                             else ());
                                            (let uu____1580 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1580 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env1
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env1
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1593 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1593 with
                                | (dmff_env1,uu____1604,bind_wp,bind_elab) ->
                                    let uu____1607 =
                                      elaborate_and_star dmff_env1
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1607 with
                                     | (dmff_env2,uu____1618,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1622 =
                                             let uu____1623 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1623.FStar_Syntax_Syntax.n in
                                           match uu____1622 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1661 =
                                                 let uu____1669 =
                                                   let uu____1672 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1672 in
                                                 match uu____1669 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1711 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1661 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1733 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1733 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1744 =
                                                          let uu____1745 =
                                                            let uu____1755 =
                                                              let uu____1759
                                                                =
                                                                let uu____1762
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    Prims.fst
                                                                    b11) in
                                                                let uu____1763
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1762,
                                                                  uu____1763) in
                                                              [uu____1759] in
                                                            (wp_type1,
                                                              uu____1755) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1745 in
                                                        mk1 uu____1744 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1771 =
                                                      let uu____1781 =
                                                        let uu____1782 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          body1 uu____1782 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1781 in
                                                    (match uu____1771 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1810
                                                           =
                                                           let error_msg =
                                                             let uu____1812 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1813 =
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
                                                                   (lid,uu____1829))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1812
                                                               uu____1813 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1855
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1855
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
                                                               (lid,uu____1861))
                                                               ->
                                                               if
                                                                 Prims.op_Negation
                                                                   (FStar_Syntax_Util.is_pure_effect
                                                                    lid)
                                                               then fail ()
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
                                                             let uu____1881 =
                                                               let uu____1882
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1883
                                                                 =
                                                                 let uu____1884
                                                                   =
                                                                   let uu____1888
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1888,
                                                                    None) in
                                                                 [uu____1884] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1882
                                                                 uu____1883 in
                                                             uu____1881 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1904 =
                                                             let uu____1908 =
                                                               let uu____1912
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1912] in
                                                             b11 ::
                                                               uu____1908 in
                                                           let uu____1915 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1904
                                                             uu____1915
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1925 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1927 =
                                             let uu____1928 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1928.FStar_Syntax_Syntax.n in
                                           match uu____1927 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1966 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1966
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1982 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____1984 =
                                             let uu____1985 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____1985.FStar_Syntax_Syntax.n in
                                           match uu____1984 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2014 =
                                                 let uu____2018 =
                                                   let uu____2020 =
                                                     let uu____2021 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2021 in
                                                   [uu____2020] in
                                                 FStar_List.append uu____2018
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2014 body what
                                           | uu____2022 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2040 =
                                                let uu____2041 =
                                                  let uu____2042 =
                                                    let uu____2052 =
                                                      let uu____2053 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      Prims.snd uu____2053 in
                                                    (t, uu____2052) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2042 in
                                                mk1 uu____2041 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2040) in
                                         let register name item =
                                           let uu____2065 =
                                             let uu____2068 = mk_lid name in
                                             let uu____2069 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders1 item None in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env1 uu____2068 uu____2069 in
                                           match uu____2065 with
                                           | (sigelt,fv) ->
                                               ((let uu____2078 =
                                                   let uu____2080 =
                                                     FStar_ST.read sigelts in
                                                   sigelt :: uu____2080 in
                                                 FStar_ST.write sigelts
                                                   uu____2078);
                                                fv) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2091 =
                                             let uu____2093 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2094 =
                                               FStar_ST.read sigelts in
                                             uu____2093 :: uu____2094 in
                                           FStar_ST.write sigelts uu____2091);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2104 =
                                              let uu____2106 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2107 =
                                                FStar_ST.read sigelts in
                                              uu____2106 :: uu____2107 in
                                            FStar_ST.write sigelts uu____2104);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2117 =
                                               let uu____2119 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2120 =
                                                 FStar_ST.read sigelts in
                                               uu____2119 :: uu____2120 in
                                             FStar_ST.write sigelts
                                               uu____2117);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2130 =
                                                let uu____2132 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2133 =
                                                  FStar_ST.read sigelts in
                                                uu____2132 :: uu____2133 in
                                              FStar_ST.write sigelts
                                                uu____2130);
                                             (let uu____2141 =
                                                FStar_List.fold_left
                                                  (fun uu____2148  ->
                                                     fun action  ->
                                                       match uu____2148 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let uu____2160 =
                                                             elaborate_and_star
                                                               dmff_env3
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn)) in
                                                           (match uu____2160
                                                            with
                                                            | (dmff_env4,action_t,action_wp,action_elab)
                                                                ->
                                                                let name =
                                                                  ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                let action_typ_with_wp
                                                                  =
                                                                  FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env4
                                                                    action_t
                                                                    action_wp in
                                                                let action_elab1
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab in
                                                                let action_typ_with_wp1
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp in
                                                                let uu____2176
                                                                  =
                                                                  let uu____2178
                                                                    =
                                                                    let uu___96_2179
                                                                    = action in
                                                                    let uu____2180
                                                                    =
                                                                    apply_close
                                                                    action_elab1 in
                                                                    let uu____2181
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___96_2179.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___96_2179.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___96_2179.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2180;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2181
                                                                    } in
                                                                  uu____2178
                                                                    ::
                                                                    actions in
                                                                (dmff_env4,
                                                                  uu____2176)))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2141 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2199 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2200 =
                                                        let uu____2202 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2202] in
                                                      uu____2199 ::
                                                        uu____2200 in
                                                    let uu____2203 =
                                                      let uu____2204 =
                                                        let uu____2205 =
                                                          let uu____2206 =
                                                            let uu____2216 =
                                                              let uu____2220
                                                                =
                                                                let uu____2223
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2224
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2223,
                                                                  uu____2224) in
                                                              [uu____2220] in
                                                            (repr,
                                                              uu____2216) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2206 in
                                                        mk1 uu____2205 in
                                                      let uu____2232 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2204
                                                        uu____2232 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2203 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2240 =
                                                    let uu____2245 =
                                                      let uu____2246 =
                                                        let uu____2249 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2249 in
                                                      uu____2246.FStar_Syntax_Syntax.n in
                                                    match uu____2245 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2257)
                                                        ->
                                                        let uu____2284 =
                                                          let uu____2293 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2293
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2324 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2284
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2352 =
                                                               let uu____2353
                                                                 =
                                                                 let uu____2356
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2356 in
                                                               uu____2353.FStar_Syntax_Syntax.n in
                                                             (match uu____2352
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2373
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2373
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2382
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2393
                                                                     ->
                                                                    match uu____2393
                                                                    with
                                                                    | 
                                                                    (bv,uu____2397)
                                                                    ->
                                                                    let uu____2398
                                                                    =
                                                                    let uu____2399
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2399
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2398
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2382
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
                                                                    uu____2432
                                                                    ->
                                                                    let uu____2436
                                                                    =
                                                                    let uu____2437
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2437 in
                                                                    failwith
                                                                    uu____2436 in
                                                                    let uu____2440
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2443
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2440,
                                                                    uu____2443)))
                                                              | uu____2453 ->
                                                                  let uu____2454
                                                                    =
                                                                    let uu____2455
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2455 in
                                                                  failwith
                                                                    uu____2454))
                                                    | uu____2460 ->
                                                        let uu____2461 =
                                                          let uu____2462 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2462 in
                                                        failwith uu____2461 in
                                                  (match uu____2240 with
                                                   | (pre,post) ->
                                                       ((let uu____2479 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2481 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2483 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___97_2485 =
                                                             ed in
                                                           let uu____2486 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2487 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2488 =
                                                             let uu____2489 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2489) in
                                                           let uu____2495 =
                                                             let uu____2496 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2496) in
                                                           let uu____2502 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2503 =
                                                             let uu____2504 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2504) in
                                                           let uu____2510 =
                                                             let uu____2511 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2511) in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2486;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2487;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2488;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2495;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___97_2485.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2502;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2503;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2510;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2517 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2517
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2528
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2528
                                                               then
                                                                 let uu____2529
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2529
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
                                                                    let uu____2539
                                                                    =
                                                                    let uu____2541
                                                                    =
                                                                    let uu____2547
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2547) in
                                                                    Some
                                                                    uu____2541 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2539;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2558
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2558
                                                                 else None in
                                                               let uu____2560
                                                                 =
                                                                 let uu____2562
                                                                   =
                                                                   let uu____2564
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2564 in
                                                                 FStar_List.append
                                                                   uu____2562
                                                                   sigelts' in
                                                               (uu____2560,
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
                (lex_t1,[],[],t,uu____2587,uu____2588,[]);
              FStar_Syntax_Syntax.sigdoc = d;
              FStar_Syntax_Syntax.sigrng = r;_}::{
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     FStar_Syntax_Syntax.Sig_datacon
                                                     (lex_top1,[],_t_top,_lex_t_top,_0_28,[],uu____2594);
                                                   FStar_Syntax_Syntax.sigdoc
                                                     = d1;
                                                   FStar_Syntax_Syntax.sigrng
                                                     = r1;_}::{
                                                                FStar_Syntax_Syntax.sigel
                                                                  =
                                                                  FStar_Syntax_Syntax.Sig_datacon
                                                                  (lex_cons,[],_t_cons,_lex_t_cons,_0_29,[],uu____2600);
                                                                FStar_Syntax_Syntax.sigdoc
                                                                  = d2;
                                                                FStar_Syntax_Syntax.sigrng
                                                                  = r2;_}::[]
              when
              ((_0_28 = (Prims.parse_int "0")) &&
                 (_0_29 = (Prims.parse_int "0")))
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
                         FStar_Syntax_Const.lexcons_lid], []));
                  FStar_Syntax_Syntax.sigdoc = d;
                  FStar_Syntax_Syntax.sigrng = r
                } in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
              let lex_top_t =
                let uu____2648 =
                  let uu____2651 =
                    let uu____2652 =
                      let uu____2657 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2657, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2652 in
                  FStar_Syntax_Syntax.mk uu____2651 in
                uu____2648 None r1 in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_top1, [utop], lex_top_t1,
                         FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"),
                         [], []));
                  FStar_Syntax_Syntax.sigdoc = d1;
                  FStar_Syntax_Syntax.sigrng = r1
                } in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let lex_cons_t =
                let a =
                  let uu____2678 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2678 in
                let hd1 =
                  let uu____2684 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2684 in
                let tl1 =
                  let uu____2686 =
                    let uu____2687 =
                      let uu____2690 =
                        let uu____2691 =
                          let uu____2696 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2696, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2691 in
                      FStar_Syntax_Syntax.mk uu____2690 in
                    uu____2687 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2686 in
                let res =
                  let uu____2709 =
                    let uu____2712 =
                      let uu____2713 =
                        let uu____2718 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2718,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2713 in
                    FStar_Syntax_Syntax.mk uu____2712 in
                  uu____2709 None r2 in
                let uu____2728 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2728 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_cons, [ucons1; ucons2], lex_cons_t1,
                         FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"),
                         [], []));
                  FStar_Syntax_Syntax.sigdoc = d2;
                  FStar_Syntax_Syntax.sigrng = r2
                } in
              let uu____2751 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], [], lids));
                FStar_Syntax_Syntax.sigdoc = None;
                FStar_Syntax_Syntax.sigrng = uu____2751
              }
          | uu____2755 ->
              let uu____2757 =
                let uu____2758 =
                  let uu____2759 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, [], lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2759 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2758 in
              failwith uu____2757
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
            let uu____2770 = FStar_Syntax_Util.type_u () in
            match uu____2770 with
            | (k,uu____2774) ->
                let phi1 =
                  let uu____2776 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2776
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_assume (lid, phi1, quals));
                   FStar_Syntax_Syntax.sigdoc = None;
                   FStar_Syntax_Syntax.sigrng = r
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
          let uu____2787 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2787 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2806 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2806 FStar_List.flatten in
              ((let uu____2814 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2814
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
                          let uu____2820 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2826,uu____2827,uu____2828,uu____2829,uu____2830,uu____2831)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2838 -> failwith "Impossible!" in
                          match uu____2820 with
                          | (lid,r) ->
                              FStar_Errors.report r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2847 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2851,uu____2852,uu____2853,uu____2854,uu____2855,uu____2856)
                        -> lid
                    | uu____2863 -> failwith "Impossible" in
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
                let uu____2869 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____2869
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
                   let uu____2885 =
                     let uu____2887 =
                       let uu____2888 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), quals, lids));
                         FStar_Syntax_Syntax.sigdoc = None;
                         FStar_Syntax_Syntax.sigrng = uu____2888
                       } in
                     uu____2887 :: ses1 in
                   (uu____2885, data_ops_ses))))
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
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses quals lids in ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____2937 = tc_inductive env2 ses quals lids in
           (match uu____2937 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____2962 = FStar_Options.set_options t s in
             match uu____2962 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s1 ->
                 Prims.raise
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
                ((let uu____2979 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____2979 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____2985 = cps_and_elaborate env1 ne in
           (match uu____2985 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___98_3006 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigdoc =
                            (uu___98_3006.FStar_Syntax_Syntax.sigdoc);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___98_3006.FStar_Syntax_Syntax.sigrng)
                        });
                      lift]
                  | None  ->
                      [(let uu___99_3007 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigdoc =
                            (uu___99_3007.FStar_Syntax_Syntax.sigdoc);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___99_3007.FStar_Syntax_Syntax.sigrng)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___100_3013 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigdoc =
                 (uu___100_3013.FStar_Syntax_Syntax.sigdoc);
               FStar_Syntax_Syntax.sigrng =
                 (uu___100_3013.FStar_Syntax_Syntax.sigrng)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3019 =
             let uu____3024 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3024 in
           (match uu____3019 with
            | (a,wp_a_src) ->
                let uu____3035 =
                  let uu____3040 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3040 in
                (match uu____3035 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3052 =
                         let uu____3054 =
                           let uu____3055 =
                             let uu____3060 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3060) in
                           FStar_Syntax_Syntax.NT uu____3055 in
                         [uu____3054] in
                       FStar_Syntax_Subst.subst uu____3052 wp_b_tgt in
                     let expected_k =
                       let uu____3064 =
                         let uu____3068 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3069 =
                           let uu____3071 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3071] in
                         uu____3068 :: uu____3069 in
                       let uu____3072 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3064 uu____3072 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3093 =
                           let uu____3094 =
                             let uu____3097 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3098 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3097, uu____3098) in
                           FStar_Errors.Error uu____3094 in
                         Prims.raise uu____3093 in
                       let uu____3101 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3101 with
                       | None  -> no_reify eff_name
                       | Some ed ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3108 =
                             let uu____3109 =
                               FStar_All.pipe_right
                                 ed.FStar_Syntax_Syntax.qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3109 in
                           if uu____3108
                           then no_reify eff_name
                           else
                             (let uu____3114 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3115 =
                                let uu____3118 =
                                  let uu____3119 =
                                    let uu____3129 =
                                      let uu____3131 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3132 =
                                        let uu____3134 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3134] in
                                      uu____3131 :: uu____3132 in
                                    (repr, uu____3129) in
                                  FStar_Syntax_Syntax.Tm_app uu____3119 in
                                FStar_Syntax_Syntax.mk uu____3118 in
                              uu____3115 None uu____3114) in
                     let uu____3144 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3159,lift_wp)) ->
                           let uu____3172 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3172)
                       | (Some (what,lift),None ) ->
                           ((let uu____3187 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3187
                             then
                               let uu____3188 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3188
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3191 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3191 with
                             | (lift1,comp,uu____3200) ->
                                 let uu____3201 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3201 with
                                  | (uu____3208,lift_wp,lift_elab) ->
                                      let uu____3211 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3212 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3144 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___101_3235 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___101_3235.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___101_3235.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___101_3235.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___101_3235.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___101_3235.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___101_3235.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___101_3235.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___101_3235.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___101_3235.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___101_3235.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___101_3235.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___101_3235.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___101_3235.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___101_3235.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___101_3235.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___101_3235.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___101_3235.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___101_3235.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___101_3235.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___101_3235.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___101_3235.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___101_3235.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___101_3235.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3239,lift1) ->
                                let uu____3246 =
                                  let uu____3251 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3251 in
                                (match uu____3246 with
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
                                         let uu____3273 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3274 =
                                           let uu____3277 =
                                             let uu____3278 =
                                               let uu____3288 =
                                                 let uu____3290 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3291 =
                                                   let uu____3293 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3293] in
                                                 uu____3290 :: uu____3291 in
                                               (lift_wp1, uu____3288) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3278 in
                                           FStar_Syntax_Syntax.mk uu____3277 in
                                         uu____3274 None uu____3273 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3306 =
                                         let uu____3310 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3311 =
                                           let uu____3313 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3314 =
                                             let uu____3316 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3316] in
                                           uu____3313 :: uu____3314 in
                                         uu____3310 :: uu____3311 in
                                       let uu____3317 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3306
                                         uu____3317 in
                                     let uu____3320 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3320 with
                                      | (expected_k2,uu____3326,uu____3327)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___102_3330 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___102_3330.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___102_3330.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___103_3332 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigdoc =
                                (uu___103_3332.FStar_Syntax_Syntax.sigdoc);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___103_3332.FStar_Syntax_Syntax.sigrng)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3348 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3348 with
            | (tps1,c1) ->
                let uu____3357 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3357 with
                 | (tps2,env3,us) ->
                     let uu____3368 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3368 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3382 =
                              let uu____3383 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3383 in
                            match uu____3382 with
                            | (uvs1,t) ->
                                let uu____3396 =
                                  let uu____3404 =
                                    let uu____3407 =
                                      let uu____3408 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3408.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3407) in
                                  match uu____3404 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3418,c4)) -> ([], c4)
                                  | (uu____3442,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3460 -> failwith "Impossible" in
                                (match uu____3396 with
                                 | (tps4,c4) ->
                                     (if
                                        ((FStar_List.length uvs1) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3489 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3489 with
                                         | (uu____3492,t1) ->
                                             let uu____3494 =
                                               let uu____3495 =
                                                 let uu____3498 =
                                                   let uu____3499 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3500 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3503 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3499 uu____3500
                                                     uu____3503 in
                                                 (uu____3498, r) in
                                               FStar_Errors.Error uu____3495 in
                                             Prims.raise uu____3494)
                                      else ();
                                      (let se1 =
                                         let uu___104_3506 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, tags,
                                                  flags));
                                           FStar_Syntax_Syntax.sigdoc =
                                             (uu___104_3506.FStar_Syntax_Syntax.sigdoc);
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___104_3506.FStar_Syntax_Syntax.sigrng)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals)
         |FStar_Syntax_Syntax.Sig_let (_,_,quals,_) when
           FStar_All.pipe_right quals
             (FStar_Util.for_some
                (fun uu___80_3531  ->
                   match uu___80_3531 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3532 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3542 =
             if uvs = []
             then
               let uu____3543 =
                 let uu____3544 = FStar_Syntax_Util.type_u () in
                 Prims.fst uu____3544 in
               check_and_gen env2 t uu____3543
             else
               (let uu____3548 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3548 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3554 =
                        let uu____3555 = FStar_Syntax_Util.type_u () in
                        Prims.fst uu____3555 in
                      tc_check_trivial_guard env2 t1 uu____3554 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3559 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3559)) in
           (match uu____3542 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___105_3569 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (lid, uvs1, t1, quals));
                    FStar_Syntax_Syntax.sigdoc =
                      (uu___105_3569.FStar_Syntax_Syntax.sigdoc);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___105_3569.FStar_Syntax_Syntax.sigrng)
                  } in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi,quals) ->
           let se1 = tc_assume env1 lid phi quals r in ([se1], [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit in
           let uu____3585 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3585 with
            | (e1,c,g1) ->
                let uu____3596 =
                  let uu____3600 =
                    let uu____3602 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3602 in
                  let uu____3603 =
                    let uu____3606 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3606) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3600 uu____3603 in
                (match uu____3596 with
                 | (e2,uu____3616,g) ->
                     ((let uu____3619 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3619);
                      (let se1 =
                         let uu___106_3621 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigdoc =
                             (uu___106_3621.FStar_Syntax_Syntax.sigdoc);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___106_3621.FStar_Syntax_Syntax.sigrng)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,quals,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3660 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3660
                 then Some q
                 else
                   (let uu____3669 =
                      let uu____3670 =
                        let uu____3673 =
                          let uu____3674 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3675 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3676 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3674 uu____3675 uu____3676 in
                        (uu____3673, r) in
                      FStar_Errors.Error uu____3670 in
                    Prims.raise uu____3669) in
           let uu____3679 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3700  ->
                     fun lb  ->
                       match uu____3700 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3724 =
                             let uu____3730 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3730 with
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | Some ((uvs,tval),quals1) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals1 in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____3782 ->
                                       FStar_Errors.warn r
                                         "Annotation from val declaration overrides inline type annotation");
                                  if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inline universes are incoherent with annotation from val declaration",
                                           r))
                                  else ();
                                  (let uu____3790 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3790, quals_opt1))) in
                           (match uu____3724 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [], (if quals = [] then None else Some quals))) in
           (match uu____3679 with
            | (should_generalize,lbs',quals_opt) ->
                let quals1 =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3843 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___81_3845  ->
                                match uu___81_3845 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3846 -> false)) in
                      if uu____3843
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____3854 =
                    let uu____3857 =
                      let uu____3858 =
                        let uu____3866 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((Prims.fst lbs), lbs'1), uu____3866) in
                      FStar_Syntax_Syntax.Tm_let uu____3858 in
                    FStar_Syntax_Syntax.mk uu____3857 in
                  uu____3854 None r in
                let uu____3888 =
                  let uu____3894 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___107_3898 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___107_3898.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___107_3898.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___107_3898.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___107_3898.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___107_3898.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___107_3898.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___107_3898.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___107_3898.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___107_3898.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___107_3898.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___107_3898.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___107_3898.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___107_3898.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___107_3898.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___107_3898.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___107_3898.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___107_3898.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___107_3898.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___107_3898.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___107_3898.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___107_3898.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___107_3898.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____3894 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3906;
                       FStar_Syntax_Syntax.pos = uu____3907;
                       FStar_Syntax_Syntax.vars = uu____3908;_},uu____3909,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals2 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3928,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals1
                        | uu____3933 -> quals1 in
                      let quals3 =
                        FStar_List.choose
                          (fun uu___82_3936  ->
                             match uu___82_3936 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____3938 =
                                   let uu____3939 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____3943 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____3943)
                                          else ();
                                          ok) (Prims.snd lbs1) in
                                   Prims.op_Negation uu____3939 in
                                 if uu____3938
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals2 in
                      ((let uu___108_3952 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let
                               (lbs1, lids, quals3, attrs));
                          FStar_Syntax_Syntax.sigdoc =
                            (uu___108_3952.FStar_Syntax_Syntax.sigdoc);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___108_3952.FStar_Syntax_Syntax.sigrng)
                        }), lbs1)
                  | uu____3959 -> failwith "impossible" in
                (match uu____3888 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (Prims.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              let uu____3985 =
                                FStar_Syntax_Syntax.range_of_fv fv in
                              FStar_TypeChecker_Common.insert_identifier_info
                                (FStar_Util.Inr fv)
                                lb.FStar_Syntax_Syntax.lbtyp uu____3985));
                      (let uu____3987 = log env2 in
                       if uu____3987
                       then
                         let uu____3988 =
                           let uu____3989 =
                             FStar_All.pipe_right (Prims.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____3996 =
                                         let uu____4001 =
                                           let uu____4002 =
                                             let uu____4007 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4007.FStar_Syntax_Syntax.fv_name in
                                           uu____4002.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4001 in
                                       match uu____3996 with
                                       | None  -> true
                                       | uu____4014 -> false in
                                     if should_log
                                     then
                                       let uu____4019 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4020 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4019 uu____4020
                                     else "")) in
                           FStar_All.pipe_right uu____3989
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____3988
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
             (fun uu___83_4049  ->
                match uu___83_4049 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4050 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4058 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4063 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4074) ->
          let uu____4081 = is_abstract quals in
          if uu____4081
          then
            let for_export_bundle se1 uu____4100 =
              match uu____4100 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4123,uu____4124,quals1) ->
                       let dec =
                         let uu___109_4133 = se1 in
                         let uu____4134 =
                           let uu____4135 =
                             let uu____4141 =
                               let uu____4144 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4144 in
                             (l, us, uu____4141,
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New :: quals1)) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4135 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4134;
                           FStar_Syntax_Syntax.sigdoc =
                             (uu___109_4133.FStar_Syntax_Syntax.sigdoc);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___109_4133.FStar_Syntax_Syntax.sigrng)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4155,uu____4156,uu____4157,uu____4158)
                       ->
                       let dec =
                         let uu___110_4164 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (l, us, t, [FStar_Syntax_Syntax.Assumption]));
                           FStar_Syntax_Syntax.sigdoc =
                             (uu___110_4164.FStar_Syntax_Syntax.sigdoc);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___110_4164.FStar_Syntax_Syntax.sigrng)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4168 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4180,uu____4181,quals) ->
          let uu____4185 = is_abstract quals in
          if uu____4185 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals) ->
          let uu____4201 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4201
          then
            ([(let uu___111_4209 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (l, us, t, [FStar_Syntax_Syntax.Assumption]));
                 FStar_Syntax_Syntax.sigdoc =
                   (uu___111_4209.FStar_Syntax_Syntax.sigdoc);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___111_4209.FStar_Syntax_Syntax.sigrng)
               })], (l :: hidden))
          else
            (let uu____4212 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___84_4214  ->
                       match uu___84_4214 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____4217 -> false)) in
             if uu____4212 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4227 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____4237,quals,uu____4239) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4257 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4257
          then ([], hidden)
          else
            (let dec =
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp),
                        [FStar_Syntax_Syntax.Assumption]));
                 FStar_Syntax_Syntax.sigdoc = (se.FStar_Syntax_Syntax.sigdoc);
                 FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid)
               } in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l,quals,uu____4280) ->
          let uu____4287 = is_abstract quals in
          if uu____4287
          then
            let uu____4292 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___112_4298 = se in
                      let uu____4299 =
                        let uu____4300 =
                          let uu____4306 =
                            let uu____4307 =
                              let uu____4312 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4312.FStar_Syntax_Syntax.fv_name in
                            uu____4307.FStar_Syntax_Syntax.v in
                          (uu____4306, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp),
                            (FStar_Syntax_Syntax.Assumption :: quals)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4300 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4299;
                        FStar_Syntax_Syntax.sigdoc =
                          (uu___112_4298.FStar_Syntax_Syntax.sigdoc);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___112_4298.FStar_Syntax_Syntax.sigrng)
                      })) in
            (uu____4292, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4331 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4342 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4353 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                env)
           | uu____4356 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4357 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4363 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4363) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals)
        |FStar_Syntax_Syntax.Sig_let (_,_,quals,_) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___85_4378  ->
                  match uu___85_4378 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4379 -> false))
          -> env
      | uu____4380 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4416 se =
        match uu____4416 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4446 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4446
              then
                let uu____4447 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4447
              else ());
             (let uu____4449 = tc_decl env1 se in
              match uu____4449 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____4475 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4475
                    then
                      let uu____4476 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4479 =
                                 let uu____4480 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4480 "\n" in
                               Prims.strcat s uu____4479) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4476
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4484 =
                      let accum_exports_hidden uu____4502 se1 =
                        match uu____4502 with
                        | (exports1,hidden1) ->
                            let uu____4518 = for_export hidden1 se1 in
                            (match uu____4518 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____4484 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____4568 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4568 with
      | (ses1,exports,env1,uu____4594) ->
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
      (let uu____4619 = FStar_Options.debug_any () in
       if uu____4619
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
         let uu___113_4625 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___113_4625.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___113_4625.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___113_4625.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___113_4625.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___113_4625.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___113_4625.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___113_4625.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___113_4625.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___113_4625.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___113_4625.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___113_4625.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___113_4625.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___113_4625.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___113_4625.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___113_4625.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___113_4625.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___113_4625.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___113_4625.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___113_4625.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___113_4625.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___113_4625.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___113_4625.FStar_TypeChecker_Env.qname_and_index)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____4628 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____4628 with
        | (ses,exports,env3) ->
            ((let uu___114_4646 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___114_4646.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___114_4646.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___114_4646.FStar_Syntax_Syntax.is_interface)
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
        let uu____4662 = tc_decls env decls in
        match uu____4662 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___115_4680 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___115_4680.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___115_4680.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___115_4680.FStar_Syntax_Syntax.is_interface)
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
          let uu___116_4694 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___116_4694.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___116_4694.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___116_4694.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___116_4694.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___116_4694.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___116_4694.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___116_4694.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___116_4694.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___116_4694.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___116_4694.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___116_4694.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___116_4694.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___116_4694.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___116_4694.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___116_4694.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___116_4694.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___116_4694.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___116_4694.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___116_4694.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___116_4694.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___116_4694.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs1 t =
          let uu____4705 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____4705 with
          | (univs2,t1) ->
              ((let uu____4711 =
                  let uu____4712 =
                    let uu____4715 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4715 in
                  FStar_All.pipe_left uu____4712
                    (FStar_Options.Other "Exports") in
                if uu____4711
                then
                  let uu____4716 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____4717 =
                    let uu____4718 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____4718
                      (FStar_String.concat ", ") in
                  let uu____4723 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4716 uu____4717 uu____4723
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____4726 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____4726 Prims.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____4744 =
             let uu____4745 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____4746 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4745 uu____4746 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4744);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4754) ->
              let uu____4761 =
                let uu____4762 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4762 in
              if uu____4761
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4770,uu____4771,uu____4772) ->
              let t =
                let uu____4782 =
                  let uu____4785 =
                    let uu____4786 =
                      let uu____4794 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____4794) in
                    FStar_Syntax_Syntax.Tm_arrow uu____4786 in
                  FStar_Syntax_Syntax.mk uu____4785 in
                uu____4782 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____4806,uu____4807,uu____4808,uu____4809) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t,quals) ->
              let uu____4820 =
                let uu____4821 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4821 in
              if uu____4820 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4824,lbs),uu____4826,quals,uu____4828) ->
              let uu____4840 =
                let uu____4841 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4841 in
              if uu____4840
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
              (l,univs1,binders,comp,quals,flags) ->
              let uu____4861 =
                let uu____4862 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4862 in
              if uu____4861
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
          let uu___117_4895 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___117_4895.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___117_4895.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____4898 =
           let uu____4899 = FStar_Options.lax () in
           Prims.op_Negation uu____4899 in
         if uu____4898 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____4905 =
           let uu____4906 = FStar_Options.interactive () in
           Prims.op_Negation uu____4906 in
         if uu____4905
         then
           let uu____4907 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____4907 Prims.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____4917 = tc_partial_modul env modul in
      match uu____4917 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____4938 = FStar_Options.debug_any () in
       if uu____4938
       then
         let uu____4939 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____4939
       else ());
      (let env1 =
         let uu___118_4943 = env in
         let uu____4944 =
           let uu____4945 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____4945 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___118_4943.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___118_4943.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___118_4943.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___118_4943.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___118_4943.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___118_4943.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___118_4943.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___118_4943.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___118_4943.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___118_4943.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___118_4943.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___118_4943.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___118_4943.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___118_4943.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___118_4943.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___118_4943.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___118_4943.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___118_4943.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____4944;
           FStar_TypeChecker_Env.lax_universes =
             (uu___118_4943.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___118_4943.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___118_4943.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___118_4943.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___118_4943.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____4946 = tc_modul env1 m in
       match uu____4946 with
       | (m1,env2) ->
           ((let uu____4954 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____4954
             then
               let uu____4955 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____4955
             else ());
            (let uu____4958 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____4958
             then
               let normalize_toplevel_lets se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),ids,qs,attrs) ->
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
                       let uu____4988 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____4988 with
                       | (univnames1,e) ->
                           let uu___119_4993 = lb in
                           let uu____4994 =
                             let uu____4997 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____4997 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___119_4993.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___119_4993.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___119_4993.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___119_4993.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4994
                           } in
                     let uu___120_4998 = se in
                     let uu____4999 =
                       let uu____5000 =
                         let uu____5008 =
                           let uu____5012 = FStar_List.map update lbs in
                           (b, uu____5012) in
                         (uu____5008, ids, qs, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5000 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____4999;
                       FStar_Syntax_Syntax.sigdoc =
                         (uu___120_4998.FStar_Syntax_Syntax.sigdoc);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___120_4998.FStar_Syntax_Syntax.sigrng)
                     }
                 | uu____5021 -> se in
               let normalized_module =
                 let uu___121_5023 = m1 in
                 let uu____5024 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___121_5023.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5024;
                   FStar_Syntax_Syntax.exports =
                     (uu___121_5023.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___121_5023.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5025 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5025
             else ());
            (m1, env2)))