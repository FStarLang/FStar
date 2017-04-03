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
          let uu___88_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___88_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___88_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___88_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___88_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___88_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___88_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___88_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___88_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___88_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___88_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___88_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___88_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___88_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___88_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___88_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___88_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___88_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___88_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___88_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___88_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___88_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___88_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___88_12.FStar_TypeChecker_Env.use_bv_sorts);
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
          let uu___89_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___89_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___89_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___89_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___89_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___89_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___89_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___89_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___89_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___89_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___89_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___89_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___89_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___89_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___89_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___89_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___89_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___89_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___89_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___89_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___89_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___89_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___89_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___89_24.FStar_TypeChecker_Env.use_bv_sorts);
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
      let uu____238 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____238 with
      | (effect_params_un,signature_un,opening) ->
          let uu____245 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____245 with
           | (effect_params,env,uu____251) ->
               let uu____252 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____252 with
                | (signature,uu____256) ->
                    let ed1 =
                      let uu___90_258 = ed in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___90_258.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___90_258.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___90_258.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___90_258.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___90_258.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___90_258.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___90_258.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___90_258.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___90_258.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___90_258.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___90_258.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___90_258.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___90_258.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___90_258.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___90_258.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___90_258.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___90_258.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___90_258.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____262 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts) in
                            ([], t1) in
                          let uu___91_280 = ed1 in
                          let uu____281 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____282 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____283 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____284 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____285 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____286 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____287 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____288 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____289 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____290 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____291 =
                            let uu____292 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            Prims.snd uu____292 in
                          let uu____298 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____299 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____300 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___92_303 = a in
                                 let uu____304 =
                                   let uu____305 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   Prims.snd uu____305 in
                                 let uu____311 =
                                   let uu____312 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   Prims.snd uu____312 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___92_303.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___92_303.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___92_303.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____304;
                                   FStar_Syntax_Syntax.action_typ = uu____311
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___91_280.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___91_280.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___91_280.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___91_280.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___91_280.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___91_280.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____281;
                            FStar_Syntax_Syntax.bind_wp = uu____282;
                            FStar_Syntax_Syntax.if_then_else = uu____283;
                            FStar_Syntax_Syntax.ite_wp = uu____284;
                            FStar_Syntax_Syntax.stronger = uu____285;
                            FStar_Syntax_Syntax.close_wp = uu____286;
                            FStar_Syntax_Syntax.assert_p = uu____287;
                            FStar_Syntax_Syntax.assume_p = uu____288;
                            FStar_Syntax_Syntax.null_wp = uu____289;
                            FStar_Syntax_Syntax.trivial = uu____290;
                            FStar_Syntax_Syntax.repr = uu____291;
                            FStar_Syntax_Syntax.return_repr = uu____298;
                            FStar_Syntax_Syntax.bind_repr = uu____299;
                            FStar_Syntax_Syntax.actions = uu____300
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____340 =
                          let uu____341 =
                            let uu____344 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____344, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____341 in
                        Prims.raise uu____340 in
                      let uu____349 =
                        let uu____350 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____350.FStar_Syntax_Syntax.n in
                      match uu____349 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____375)::(wp,uu____377)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____386 -> fail signature1)
                      | uu____387 -> fail signature1 in
                    let uu____388 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____388 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____406 =
                           let uu____407 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____407 with
                           | (signature1,uu____415) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____417 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____417 in
                         ((let uu____419 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____419
                           then
                             let uu____420 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____421 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____422 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____423 =
                               let uu____424 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____424 in
                             let uu____425 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____420 uu____421 uu____422 uu____423
                               uu____425
                           else ());
                          (let check_and_gen' env2 uu____438 k =
                             match uu____438 with
                             | (uu____443,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____451 =
                                 let uu____455 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____456 =
                                   let uu____458 =
                                     let uu____459 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____459 in
                                   [uu____458] in
                                 uu____455 :: uu____456 in
                               let uu____460 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____451 uu____460 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____464 = fresh_effect_signature () in
                             match uu____464 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____478 =
                                     let uu____482 =
                                       let uu____483 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____483 in
                                     [uu____482] in
                                   let uu____484 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____478
                                     uu____484 in
                                 let expected_k =
                                   let uu____490 =
                                     let uu____494 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____495 =
                                       let uu____497 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____498 =
                                         let uu____500 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____501 =
                                           let uu____503 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____504 =
                                             let uu____506 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____506] in
                                           uu____503 :: uu____504 in
                                         uu____500 :: uu____501 in
                                       uu____497 :: uu____498 in
                                     uu____494 :: uu____495 in
                                   let uu____507 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____490
                                     uu____507 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____512 =
                                 let uu____513 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____513 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____512 in
                             let expected_k =
                               let uu____521 =
                                 let uu____525 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____526 =
                                   let uu____528 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____529 =
                                     let uu____531 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____532 =
                                       let uu____534 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____534] in
                                     uu____531 :: uu____532 in
                                   uu____528 :: uu____529 in
                                 uu____525 :: uu____526 in
                               let uu____535 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____521 uu____535 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____542 =
                                 let uu____546 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____547 =
                                   let uu____549 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____549] in
                                 uu____546 :: uu____547 in
                               let uu____550 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____542 uu____550 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____554 = FStar_Syntax_Util.type_u () in
                             match uu____554 with
                             | (t,uu____558) ->
                                 let expected_k =
                                   let uu____562 =
                                     let uu____566 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____567 =
                                       let uu____569 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____570 =
                                         let uu____572 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____572] in
                                       uu____569 :: uu____570 in
                                     uu____566 :: uu____567 in
                                   let uu____573 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____562
                                     uu____573 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____578 =
                                 let uu____579 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____579 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____578 in
                             let b_wp_a =
                               let uu____587 =
                                 let uu____591 =
                                   let uu____592 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____592 in
                                 [uu____591] in
                               let uu____593 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____587 uu____593 in
                             let expected_k =
                               let uu____599 =
                                 let uu____603 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____604 =
                                   let uu____606 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____607 =
                                     let uu____609 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____609] in
                                   uu____606 :: uu____607 in
                                 uu____603 :: uu____604 in
                               let uu____610 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____599 uu____610 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____617 =
                                 let uu____621 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____622 =
                                   let uu____624 =
                                     let uu____625 =
                                       let uu____626 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____626
                                         Prims.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____625 in
                                   let uu____631 =
                                     let uu____633 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____633] in
                                   uu____624 :: uu____631 in
                                 uu____621 :: uu____622 in
                               let uu____634 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____617 uu____634 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____641 =
                                 let uu____645 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____646 =
                                   let uu____648 =
                                     let uu____649 =
                                       let uu____650 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____650
                                         Prims.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____649 in
                                   let uu____655 =
                                     let uu____657 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____657] in
                                   uu____648 :: uu____655 in
                                 uu____645 :: uu____646 in
                               let uu____658 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____641 uu____658 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____665 =
                                 let uu____669 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____669] in
                               let uu____670 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____665 uu____670 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____674 = FStar_Syntax_Util.type_u () in
                             match uu____674 with
                             | (t,uu____678) ->
                                 let expected_k =
                                   let uu____682 =
                                     let uu____686 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____687 =
                                       let uu____689 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____689] in
                                     uu____686 :: uu____687 in
                                   let uu____690 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____682
                                     uu____690 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____693 =
                             let uu____699 =
                               let uu____700 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____700.FStar_Syntax_Syntax.n in
                             match uu____699 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____709 ->
                                 let repr =
                                   let uu____711 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____711 with
                                   | (t,uu____715) ->
                                       let expected_k =
                                         let uu____719 =
                                           let uu____723 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____724 =
                                             let uu____726 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____726] in
                                           uu____723 :: uu____724 in
                                         let uu____727 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____719
                                           uu____727 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____740 =
                                     let uu____743 =
                                       let uu____744 =
                                         let uu____754 =
                                           let uu____756 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____757 =
                                             let uu____759 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____759] in
                                           uu____756 :: uu____757 in
                                         (repr1, uu____754) in
                                       FStar_Syntax_Syntax.Tm_app uu____744 in
                                     FStar_Syntax_Syntax.mk uu____743 in
                                   uu____740 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____778 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____778 wp in
                                 let destruct_repr t =
                                   let uu____789 =
                                     let uu____790 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____790.FStar_Syntax_Syntax.n in
                                   match uu____789 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____799,(t1,uu____801)::(wp,uu____803)::[])
                                       -> (t1, wp)
                                   | uu____837 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____846 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____846
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____847 = fresh_effect_signature () in
                                   match uu____847 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____861 =
                                           let uu____865 =
                                             let uu____866 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____866 in
                                           [uu____865] in
                                         let uu____867 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____861
                                           uu____867 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____873 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____873 in
                                       let wp_g_x =
                                         let uu____877 =
                                           let uu____878 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____879 =
                                             let uu____880 =
                                               let uu____881 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____881 in
                                             [uu____880] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____878 uu____879 in
                                         uu____877 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____892 =
                                             let uu____893 =
                                               let uu____894 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____894
                                                 Prims.snd in
                                             let uu____899 =
                                               let uu____900 =
                                                 let uu____902 =
                                                   let uu____904 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____905 =
                                                     let uu____907 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____908 =
                                                       let uu____910 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____911 =
                                                         let uu____913 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____913] in
                                                       uu____910 :: uu____911 in
                                                     uu____907 :: uu____908 in
                                                   uu____904 :: uu____905 in
                                                 r :: uu____902 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____900 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____893 uu____899 in
                                           uu____892 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____921 =
                                           let uu____925 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____926 =
                                             let uu____928 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____929 =
                                               let uu____931 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____932 =
                                                 let uu____934 =
                                                   let uu____935 =
                                                     let uu____936 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____936 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____935 in
                                                 let uu____937 =
                                                   let uu____939 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____940 =
                                                     let uu____942 =
                                                       let uu____943 =
                                                         let uu____944 =
                                                           let uu____948 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____948] in
                                                         let uu____949 =
                                                           let uu____952 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____952 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____944
                                                           uu____949 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____943 in
                                                     [uu____942] in
                                                   uu____939 :: uu____940 in
                                                 uu____934 :: uu____937 in
                                               uu____931 :: uu____932 in
                                             uu____928 :: uu____929 in
                                           uu____925 :: uu____926 in
                                         let uu____953 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____921
                                           uu____953 in
                                       let uu____956 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____956 with
                                        | (expected_k1,uu____961,uu____962)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (Prims.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___93_966 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___93_966.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___93_966.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___93_966.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___93_966.FStar_TypeChecker_Env.qname_and_index)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____973 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____973 in
                                   let res =
                                     let wp =
                                       let uu____980 =
                                         let uu____981 =
                                           let uu____982 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____982
                                             Prims.snd in
                                         let uu____987 =
                                           let uu____988 =
                                             let uu____990 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____991 =
                                               let uu____993 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____993] in
                                             uu____990 :: uu____991 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____988 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____981 uu____987 in
                                       uu____980 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1001 =
                                       let uu____1005 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1006 =
                                         let uu____1008 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1008] in
                                       uu____1005 :: uu____1006 in
                                     let uu____1009 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1001
                                       uu____1009 in
                                   let uu____1012 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1012 with
                                   | (expected_k1,uu____1020,uu____1021) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (Prims.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1024 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1024 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1036 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1047 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1047 with
                                     | (act_typ,uu____1052,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env1 act_typ in
                                         ((let uu____1056 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1056
                                           then
                                             let uu____1057 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1058 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1057 uu____1058
                                           else ());
                                          (let uu____1060 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1060 with
                                           | (act_defn,uu____1065,g_a) ->
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
                                               let uu____1069 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1087 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1087 with
                                                      | (bs1,uu____1093) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1100 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1100 in
                                                          let uu____1103 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1103
                                                           with
                                                           | (k1,uu____1110,g)
                                                               -> (k1, g)))
                                                 | uu____1112 ->
                                                     let uu____1113 =
                                                       let uu____1114 =
                                                         let uu____1117 =
                                                           let uu____1118 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1119 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1118
                                                             uu____1119 in
                                                         (uu____1117,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1114 in
                                                     Prims.raise uu____1113 in
                                               (match uu____1069 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1126 =
                                                        let uu____1127 =
                                                          let uu____1128 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1128 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1127 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1126);
                                                     (let act_typ2 =
                                                        let uu____1132 =
                                                          let uu____1133 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1133.FStar_Syntax_Syntax.n in
                                                        match uu____1132 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1150 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1150
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1157
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1157
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1177
                                                                    =
                                                                    let uu____1178
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1178] in
                                                                    let uu____1179
                                                                    =
                                                                    let uu____1185
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1185] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1177;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1179;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1186
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1186))
                                                        | uu____1189 ->
                                                            failwith "" in
                                                      let uu____1192 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1192 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___94_1198 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___94_1198.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___94_1198.FStar_Syntax_Syntax.action_unqualified_name);
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
                           match uu____693 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1214 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1214 in
                               let uu____1217 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1217 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1223 =
                                        let uu____1226 =
                                          let uu____1227 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1227.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1226) in
                                      match uu____1223 with
                                      | ([],uu____1230) -> t1
                                      | (uu____1236,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1237,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1249 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1260 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1260 in
                                      let m =
                                        FStar_List.length (Prims.fst ts1) in
                                      (let uu____1265 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1266 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts1) in
                                             Prims.op_Negation uu____1266))
                                           && (m <> n1) in
                                       if uu____1265
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1275 =
                                           let uu____1276 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1277 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1276 uu____1277 in
                                         failwith uu____1275
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1283 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1283 with
                                      | (univs2,defn) ->
                                          let uu____1288 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1288 with
                                           | (univs',typ) ->
                                               let uu___95_1294 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___95_1294.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___95_1294.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let nunivs = FStar_List.length univs1 in
                                    let ed3 =
                                      let uu___96_1299 = ed2 in
                                      let uu____1300 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1301 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1302 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1303 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1304 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1305 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1306 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1307 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1308 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1309 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1310 =
                                        let uu____1311 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        Prims.snd uu____1311 in
                                      let uu____1317 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1318 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1319 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___96_1299.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___96_1299.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___96_1299.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1300;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1301;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1302;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1303;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1304;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1305;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1306;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1307;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1308;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1309;
                                        FStar_Syntax_Syntax.repr = uu____1310;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1317;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1318;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1319
                                      } in
                                    ((let uu____1322 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1322
                                      then
                                        let uu____1323 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1323
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
      let uu____1327 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1327 with
      | (effect_binders_un,signature_un) ->
          let uu____1337 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1337 with
           | (effect_binders,env1,uu____1348) ->
               let uu____1349 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1349 with
                | (signature,uu____1358) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1367  ->
                           match uu____1367 with
                           | (bv,qual) ->
                               let uu____1374 =
                                 let uu___97_1375 = bv in
                                 let uu____1376 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___97_1375.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___97_1375.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1376
                                 } in
                               (uu____1374, qual)) effect_binders in
                    let uu____1379 =
                      let uu____1384 =
                        let uu____1385 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1385.FStar_Syntax_Syntax.n in
                      match uu____1384 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1393)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1408 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1379 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1425 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1425
                           then
                             let uu____1426 =
                               let uu____1428 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1428 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1426
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders1 in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1438 =
                             FStar_TypeChecker_TcTerm.tc_term env1 t1 in
                           match uu____1438 with
                           | (t2,comp,uu____1446) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1457 =
                           open_and_check ed.FStar_Syntax_Syntax.repr in
                         (match uu____1457 with
                          | (repr,_comp) ->
                              ((let uu____1468 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1468
                                then
                                  let uu____1469 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1469
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
                                  let uu____1475 =
                                    let uu____1476 =
                                      let uu____1477 =
                                        let uu____1487 =
                                          let uu____1491 =
                                            let uu____1494 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1495 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1494, uu____1495) in
                                          [uu____1491] in
                                        (wp_type1, uu____1487) in
                                      FStar_Syntax_Syntax.Tm_app uu____1477 in
                                    mk1 uu____1476 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1475 in
                                let effect_signature =
                                  let binders =
                                    let uu____1510 =
                                      let uu____1513 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1513) in
                                    let uu____1514 =
                                      let uu____1518 =
                                        let uu____1519 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1519
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1518] in
                                    uu____1510 :: uu____1514 in
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
                                  let uu____1552 = item in
                                  match uu____1552 with
                                  | (u_item,item1) ->
                                      let uu____1564 = open_and_check item1 in
                                      (match uu____1564 with
                                       | (item2,item_comp) ->
                                           ((let uu____1574 =
                                               let uu____1575 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1575 in
                                             if uu____1574
                                             then
                                               let uu____1576 =
                                                 let uu____1577 =
                                                   let uu____1578 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1579 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1578 uu____1579 in
                                                 FStar_Errors.Err uu____1577 in
                                               Prims.raise uu____1576
                                             else ());
                                            (let uu____1581 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1581 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env1
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env1
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1594 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1594 with
                                | (dmff_env1,uu____1605,bind_wp,bind_elab) ->
                                    let uu____1608 =
                                      elaborate_and_star dmff_env1
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1608 with
                                     | (dmff_env2,uu____1619,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1623 =
                                             let uu____1624 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1624.FStar_Syntax_Syntax.n in
                                           match uu____1623 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1662 =
                                                 let uu____1670 =
                                                   let uu____1673 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1673 in
                                                 match uu____1670 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1712 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1662 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1734 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1734 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1745 =
                                                          let uu____1746 =
                                                            let uu____1756 =
                                                              let uu____1760
                                                                =
                                                                let uu____1763
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    Prims.fst
                                                                    b11) in
                                                                let uu____1764
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1763,
                                                                  uu____1764) in
                                                              [uu____1760] in
                                                            (wp_type1,
                                                              uu____1756) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1746 in
                                                        mk1 uu____1745 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1772 =
                                                      let uu____1782 =
                                                        let uu____1783 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          body1 uu____1783 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1782 in
                                                    (match uu____1772 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1811
                                                           =
                                                           let error_msg =
                                                             let uu____1813 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1814 =
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
                                                                   (lid,uu____1830))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1813
                                                               uu____1814 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1856
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1856
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
                                                               (lid,uu____1862))
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
                                                             let uu____1882 =
                                                               let uu____1883
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1884
                                                                 =
                                                                 let uu____1885
                                                                   =
                                                                   let uu____1889
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1889,
                                                                    None) in
                                                                 [uu____1885] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1883
                                                                 uu____1884 in
                                                             uu____1882 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1905 =
                                                             let uu____1909 =
                                                               let uu____1913
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1913] in
                                                             b11 ::
                                                               uu____1909 in
                                                           let uu____1916 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1905
                                                             uu____1916
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1926 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1928 =
                                             let uu____1929 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1929.FStar_Syntax_Syntax.n in
                                           match uu____1928 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1967 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1967
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1983 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____1985 =
                                             let uu____1986 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____1986.FStar_Syntax_Syntax.n in
                                           match uu____1985 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2015 =
                                                 let uu____2019 =
                                                   let uu____2021 =
                                                     let uu____2022 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2022 in
                                                   [uu____2021] in
                                                 FStar_List.append uu____2019
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2015 body what
                                           | uu____2023 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2041 =
                                                let uu____2042 =
                                                  let uu____2043 =
                                                    let uu____2053 =
                                                      let uu____2054 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      Prims.snd uu____2054 in
                                                    (t, uu____2053) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2043 in
                                                mk1 uu____2042 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2041) in
                                         let register name item =
                                           let uu____2066 =
                                             let uu____2069 = mk_lid name in
                                             let uu____2070 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders1 item None in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env1 uu____2069 uu____2070 in
                                           match uu____2066 with
                                           | (sigelt,fv) ->
                                               ((let uu____2079 =
                                                   let uu____2081 =
                                                     FStar_ST.read sigelts in
                                                   sigelt :: uu____2081 in
                                                 FStar_ST.write sigelts
                                                   uu____2079);
                                                fv) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2092 =
                                             let uu____2094 =
                                               FStar_ST.read sigelts in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: uu____2094 in
                                           FStar_ST.write sigelts uu____2092);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2104 =
                                              let uu____2106 =
                                                FStar_ST.read sigelts in
                                              (FStar_Syntax_Syntax.Sig_pragma
                                                 ((FStar_Syntax_Syntax.SetOptions
                                                     "--admit_smt_queries false"),
                                                   FStar_Range.dummyRange))
                                                :: uu____2106 in
                                            FStar_ST.write sigelts uu____2104);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2116 =
                                               let uu____2118 =
                                                 FStar_ST.read sigelts in
                                               (FStar_Syntax_Syntax.Sig_pragma
                                                  ((FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"),
                                                    FStar_Range.dummyRange))
                                                 :: uu____2118 in
                                             FStar_ST.write sigelts
                                               uu____2116);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2128 =
                                                let uu____2130 =
                                                  FStar_ST.read sigelts in
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   ((FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries false"),
                                                     FStar_Range.dummyRange))
                                                  :: uu____2130 in
                                              FStar_ST.write sigelts
                                                uu____2128);
                                             (let uu____2138 =
                                                FStar_List.fold_left
                                                  (fun uu____2145  ->
                                                     fun action  ->
                                                       match uu____2145 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let uu____2157 =
                                                             elaborate_and_star
                                                               dmff_env3
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn)) in
                                                           (match uu____2157
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
                                                                let uu____2173
                                                                  =
                                                                  let uu____2175
                                                                    =
                                                                    let uu___98_2176
                                                                    = action in
                                                                    let uu____2177
                                                                    =
                                                                    apply_close
                                                                    action_elab1 in
                                                                    let uu____2178
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___98_2176.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___98_2176.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___98_2176.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2177;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2178
                                                                    } in
                                                                  uu____2175
                                                                    ::
                                                                    actions in
                                                                (dmff_env4,
                                                                  uu____2173)))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2138 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2196 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2197 =
                                                        let uu____2199 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2199] in
                                                      uu____2196 ::
                                                        uu____2197 in
                                                    let uu____2200 =
                                                      let uu____2201 =
                                                        let uu____2202 =
                                                          let uu____2203 =
                                                            let uu____2213 =
                                                              let uu____2217
                                                                =
                                                                let uu____2220
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2221
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2220,
                                                                  uu____2221) in
                                                              [uu____2217] in
                                                            (repr,
                                                              uu____2213) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2203 in
                                                        mk1 uu____2202 in
                                                      let uu____2229 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2201
                                                        uu____2229 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2200 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2237 =
                                                    let uu____2242 =
                                                      let uu____2243 =
                                                        let uu____2246 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2246 in
                                                      uu____2243.FStar_Syntax_Syntax.n in
                                                    match uu____2242 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2254)
                                                        ->
                                                        let uu____2281 =
                                                          let uu____2290 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2290
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2321 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2281
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2349 =
                                                               let uu____2350
                                                                 =
                                                                 let uu____2353
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2353 in
                                                               uu____2350.FStar_Syntax_Syntax.n in
                                                             (match uu____2349
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2370
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2370
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2379
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2390
                                                                     ->
                                                                    match uu____2390
                                                                    with
                                                                    | 
                                                                    (bv,uu____2394)
                                                                    ->
                                                                    let uu____2395
                                                                    =
                                                                    let uu____2396
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2396
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2395
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2379
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
                                                                    uu____2429
                                                                    ->
                                                                    let uu____2433
                                                                    =
                                                                    let uu____2434
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2434 in
                                                                    failwith
                                                                    uu____2433 in
                                                                    let uu____2437
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2440
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2437,
                                                                    uu____2440)))
                                                              | uu____2450 ->
                                                                  let uu____2451
                                                                    =
                                                                    let uu____2452
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2452 in
                                                                  failwith
                                                                    uu____2451))
                                                    | uu____2457 ->
                                                        let uu____2458 =
                                                          let uu____2459 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2459 in
                                                        failwith uu____2458 in
                                                  (match uu____2237 with
                                                   | (pre,post) ->
                                                       ((let uu____2476 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2478 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2480 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___99_2482 =
                                                             ed in
                                                           let uu____2483 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2484 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2485 =
                                                             let uu____2486 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2486) in
                                                           let uu____2492 =
                                                             let uu____2493 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2493) in
                                                           let uu____2499 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2500 =
                                                             let uu____2501 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2501) in
                                                           let uu____2507 =
                                                             let uu____2508 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2508) in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2483;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2484;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2485;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2492;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___99_2482.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2499;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2500;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2507;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2514 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2514
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2525
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2525
                                                               then
                                                                 let uu____2526
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2526
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
                                                                    let uu____2536
                                                                    =
                                                                    let uu____2538
                                                                    =
                                                                    let uu____2544
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2544) in
                                                                    Some
                                                                    uu____2538 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2536;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   Some
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    (lift_from_pure,
                                                                    FStar_Range.dummyRange))
                                                                 else None in
                                                               let uu____2556
                                                                 =
                                                                 let uu____2558
                                                                   =
                                                                   let uu____2560
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2560 in
                                                                 FStar_List.append
                                                                   uu____2558
                                                                   sigelts' in
                                                               (uu____2556,
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
          | (FStar_Syntax_Syntax.Sig_inductive_typ
              (lex_t1,[],[],t,uu____2583,uu____2584,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top1,[],_t_top,_lex_t_top,_0_28,[],uu____2589,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_29,[],uu____2594,r2))::[]
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
                FStar_Syntax_Syntax.Sig_inductive_typ
                  (lex_t1, [u], [], t2, [],
                    [FStar_Syntax_Const.lextop_lid;
                    FStar_Syntax_Const.lexcons_lid], [], r) in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
              let lex_top_t =
                let uu____2638 =
                  let uu____2641 =
                    let uu____2642 =
                      let uu____2647 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2647, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2642 in
                  FStar_Syntax_Syntax.mk uu____2641 in
                uu____2638 None r1 in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_top1, [utop], lex_top_t1,
                    FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), [],
                    [], r1) in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let lex_cons_t =
                let a =
                  let uu____2668 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2668 in
                let hd1 =
                  let uu____2674 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2674 in
                let tl1 =
                  let uu____2676 =
                    let uu____2677 =
                      let uu____2680 =
                        let uu____2681 =
                          let uu____2686 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2686, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2681 in
                      FStar_Syntax_Syntax.mk uu____2680 in
                    uu____2677 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2676 in
                let res =
                  let uu____2699 =
                    let uu____2702 =
                      let uu____2703 =
                        let uu____2708 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2708,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2703 in
                    FStar_Syntax_Syntax.mk uu____2702 in
                  uu____2699 None r2 in
                let uu____2718 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2718 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons, [ucons1; ucons2], lex_cons_t1,
                    FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), [],
                    [], r2) in
              let uu____2741 =
                let uu____2749 = FStar_TypeChecker_Env.get_range env in
                ([tc; dc_lextop; dc_lexcons], [], lids, uu____2749) in
              FStar_Syntax_Syntax.Sig_bundle uu____2741
          | uu____2753 ->
              let uu____2755 =
                let uu____2756 =
                  FStar_Syntax_Print.sigelt_to_string
                    (FStar_Syntax_Syntax.Sig_bundle
                       (ses, [], lids, FStar_Range.dummyRange)) in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2756 in
              failwith uu____2755
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
            let uu____2767 = FStar_Syntax_Util.type_u () in
            match uu____2767 with
            | (k,uu____2771) ->
                let phi1 =
                  let uu____2773 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2773
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 FStar_Syntax_Syntax.Sig_assume (lid, phi1, quals, r))
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
          let uu____2784 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2784 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2803 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2803 FStar_List.flatten in
              ((let uu____2811 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2811
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
                          let uu____2817 =
                            match ty with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2823,uu____2824,uu____2825,uu____2826,uu____2827,uu____2828,r)
                                -> (lid, r)
                            | uu____2836 -> failwith "Impossible!" in
                          match uu____2817 with
                          | (lid,r) ->
                              FStar_Errors.report r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2845 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2849,uu____2850,uu____2851,uu____2852,uu____2853,uu____2854,uu____2855)
                        -> lid
                    | uu____2862 -> failwith "Impossible" in
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
                let uu____2868 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____2868
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
                   let uu____2884 =
                     let uu____2886 =
                       let uu____2887 =
                         let uu____2895 =
                           FStar_TypeChecker_Env.get_range env0 in
                         ((FStar_List.append tcs datas), quals, lids,
                           uu____2895) in
                       FStar_Syntax_Syntax.Sig_bundle uu____2887 in
                     uu____2886 :: ses1 in
                   (uu____2884, data_ops_ses))))
and tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (match se with
       | FStar_Syntax_Syntax.Sig_inductive_typ _
         |FStar_Syntax_Syntax.Sig_datacon _ ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses quals lids in
           let uu____2935 = FStar_TypeChecker_Env.push_sigelt env2 se1 in
           ([se1], uu____2935, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____2949 = tc_inductive env2 ses quals lids in
           (match uu____2949 with
            | (ses1,projectors_ses) ->
                let env3 =
                  FStar_List.fold_left
                    (fun env'  ->
                       fun se1  -> FStar_TypeChecker_Env.push_sigelt env' se1)
                    env2 ses1 in
                (ses1, env3, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma (p,r) ->
           let set_options1 t s =
             let uu____2979 = FStar_Options.set_options t s in
             match uu____2979 with
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
                 ([se], env1, []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], env1, []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____2997 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____2997 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env1, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
           let uu____3005 = cps_and_elaborate env1 ne in
           (match uu____3005 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [FStar_Syntax_Syntax.Sig_new_effect (ne1, r); lift]
                  | None  -> [FStar_Syntax_Syntax.Sig_new_effect (ne1, r)] in
                ([], env1, (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect (ne,r) ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 = FStar_Syntax_Syntax.Sig_new_effect (ne1, r) in
           let env2 = FStar_TypeChecker_Env.push_sigelt env1 se1 in
           let uu____3034 =
             FStar_All.pipe_right ne1.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____3045  ->
                     fun a  ->
                       match uu____3045 with
                       | (env3,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne1.FStar_Syntax_Syntax.mname a in
                           let uu____3058 =
                             FStar_TypeChecker_Env.push_sigelt env3 se_let in
                           (uu____3058, (se_let :: ses))) (env2, [se1])) in
           (match uu____3034 with | (env3,ses) -> ([se1], env3, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub1,r) ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3076 =
             let uu____3081 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3081 in
           (match uu____3076 with
            | (a,wp_a_src) ->
                let uu____3093 =
                  let uu____3098 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3098 in
                (match uu____3093 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3111 =
                         let uu____3113 =
                           let uu____3114 =
                             let uu____3119 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3119) in
                           FStar_Syntax_Syntax.NT uu____3114 in
                         [uu____3113] in
                       FStar_Syntax_Subst.subst uu____3111 wp_b_tgt in
                     let expected_k =
                       let uu____3123 =
                         let uu____3127 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3128 =
                           let uu____3130 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3130] in
                         uu____3127 :: uu____3128 in
                       let uu____3131 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3123 uu____3131 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3152 =
                           let uu____3153 =
                             let uu____3156 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3157 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3156, uu____3157) in
                           FStar_Errors.Error uu____3153 in
                         Prims.raise uu____3152 in
                       let uu____3160 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3160 with
                       | None  -> no_reify eff_name
                       | Some ed ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3167 =
                             let uu____3168 =
                               FStar_All.pipe_right
                                 ed.FStar_Syntax_Syntax.qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3168 in
                           if uu____3167
                           then no_reify eff_name
                           else
                             (let uu____3173 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3174 =
                                let uu____3177 =
                                  let uu____3178 =
                                    let uu____3188 =
                                      let uu____3190 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3191 =
                                        let uu____3193 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3193] in
                                      uu____3190 :: uu____3191 in
                                    (repr, uu____3188) in
                                  FStar_Syntax_Syntax.Tm_app uu____3178 in
                                FStar_Syntax_Syntax.mk uu____3177 in
                              uu____3174 None uu____3173) in
                     let uu____3203 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3218,lift_wp)) ->
                           let uu____3231 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3231)
                       | (Some (what,lift),None ) ->
                           ((let uu____3246 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3246
                             then
                               let uu____3247 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3247
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3250 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3250 with
                             | (lift1,comp,uu____3259) ->
                                 let uu____3260 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3260 with
                                  | (uu____3267,lift_wp,lift_elab) ->
                                      let uu____3270 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3271 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3203 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___100_3295 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___100_3295.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___100_3295.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___100_3295.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___100_3295.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___100_3295.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___100_3295.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___100_3295.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___100_3295.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___100_3295.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___100_3295.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___100_3295.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___100_3295.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___100_3295.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___100_3295.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___100_3295.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___100_3295.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___100_3295.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___100_3295.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___100_3295.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___100_3295.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___100_3295.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___100_3295.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___100_3295.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3299,lift1) ->
                                let uu____3306 =
                                  let uu____3311 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3311 in
                                (match uu____3306 with
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
                                         let uu____3333 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3334 =
                                           let uu____3337 =
                                             let uu____3338 =
                                               let uu____3348 =
                                                 let uu____3350 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3351 =
                                                   let uu____3353 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3353] in
                                                 uu____3350 :: uu____3351 in
                                               (lift_wp1, uu____3348) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3338 in
                                           FStar_Syntax_Syntax.mk uu____3337 in
                                         uu____3334 None uu____3333 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3366 =
                                         let uu____3370 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3371 =
                                           let uu____3373 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3374 =
                                             let uu____3376 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3376] in
                                           uu____3373 :: uu____3374 in
                                         uu____3370 :: uu____3371 in
                                       let uu____3377 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3366
                                         uu____3377 in
                                     let uu____3380 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3380 with
                                      | (expected_k2,uu____3386,uu____3387)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let env3 =
                            let uu___101_3390 = env2 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___101_3390.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___101_3390.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___101_3390.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___101_3390.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___101_3390.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___101_3390.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___101_3390.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___101_3390.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___101_3390.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___101_3390.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___101_3390.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___101_3390.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___101_3390.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___101_3390.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___101_3390.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___101_3390.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___101_3390.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___101_3390.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = lax1;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___101_3390.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___101_3390.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___101_3390.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___101_3390.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___101_3390.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let sub2 =
                            let uu___102_3392 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___102_3392.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___102_3392.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            FStar_Syntax_Syntax.Sig_sub_effect (sub2, r) in
                          let env4 =
                            FStar_TypeChecker_Env.push_sigelt env3 se1 in
                          ([se1], env4, []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3411 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3411 with
            | (tps1,c1) ->
                let uu____3421 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3421 with
                 | (tps2,env3,us) ->
                     let uu____3433 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3433 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3448 =
                              let uu____3449 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3449 in
                            match uu____3448 with
                            | (uvs1,t) ->
                                let uu____3463 =
                                  let uu____3471 =
                                    let uu____3474 =
                                      let uu____3475 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3475.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3474) in
                                  match uu____3471 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3485,c4)) -> ([], c4)
                                  | (uu____3509,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3527 -> failwith "Impossible" in
                                (match uu____3463 with
                                 | (tps4,c4) ->
                                     (if
                                        ((FStar_List.length uvs1) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3557 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3557 with
                                         | (uu____3560,t1) ->
                                             let uu____3562 =
                                               let uu____3563 =
                                                 let uu____3566 =
                                                   let uu____3567 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3568 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3571 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3567 uu____3568
                                                     uu____3571 in
                                                 (uu____3566, r) in
                                               FStar_Errors.Error uu____3563 in
                                             Prims.raise uu____3562)
                                      else ();
                                      (let se1 =
                                         FStar_Syntax_Syntax.Sig_effect_abbrev
                                           (lid, uvs1, tps4, c4, tags, flags,
                                             r) in
                                       let env4 =
                                         FStar_TypeChecker_Env.push_sigelt
                                           env0 se1 in
                                       ([se1], env4, [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals,_)
         |FStar_Syntax_Syntax.Sig_let (_,_,_,quals,_) when
           FStar_All.pipe_right quals
             (FStar_Util.for_some
                (fun uu___81_3601  ->
                   match uu___81_3601 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3602 -> false))
           -> ([], env1, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3613 =
             if uvs = []
             then
               let uu____3614 =
                 let uu____3615 = FStar_Syntax_Util.type_u () in
                 Prims.fst uu____3615 in
               check_and_gen env2 t uu____3614
             else
               (let uu____3619 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3619 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3625 =
                        let uu____3626 = FStar_Syntax_Util.type_u () in
                        Prims.fst uu____3626 in
                      tc_check_trivial_guard env2 t1 uu____3625 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3630 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3630)) in
           (match uu____3613 with
            | (uvs1,t1) ->
                let se1 =
                  FStar_Syntax_Syntax.Sig_declare_typ
                    (lid, uvs1, t1, quals, r) in
                let env3 = FStar_TypeChecker_Env.push_sigelt env2 se1 in
                ([se1], env3, []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi,quals,r) ->
           let se1 = tc_assume env1 lid phi quals r in
           let env2 = FStar_TypeChecker_Env.push_sigelt env1 se1 in
           ([se1], env2, [])
       | FStar_Syntax_Syntax.Sig_main (e,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit in
           let uu____3660 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3660 with
            | (e1,c,g1) ->
                let uu____3672 =
                  let uu____3676 =
                    let uu____3678 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3678 in
                  let uu____3679 =
                    let uu____3682 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3682) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3676 uu____3679 in
                (match uu____3672 with
                 | (e2,uu____3693,g) ->
                     ((let uu____3696 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3696);
                      (let se1 = FStar_Syntax_Syntax.Sig_main (e2, r) in
                       let env4 = FStar_TypeChecker_Env.push_sigelt env3 se1 in
                       ([se1], env4, [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,r,lids,quals,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3738 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3738
                 then Some q
                 else
                   (let uu____3747 =
                      let uu____3748 =
                        let uu____3751 =
                          let uu____3752 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3753 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3754 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3752 uu____3753 uu____3754 in
                        (uu____3751, r) in
                      FStar_Errors.Error uu____3748 in
                    Prims.raise uu____3747) in
           let uu____3757 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3778  ->
                     fun lb  ->
                       match uu____3778 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3802 =
                             let uu____3808 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3808 with
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
                                   | uu____3860 ->
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
                                  (let uu____3868 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3868, quals_opt1))) in
                           (match uu____3802 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [], (if quals = [] then None else Some quals))) in
           (match uu____3757 with
            | (should_generalize,lbs',quals_opt) ->
                let quals1 =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3922 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___82_3924  ->
                                match uu___82_3924 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3925 -> false)) in
                      if uu____3922
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____3933 =
                    let uu____3936 =
                      let uu____3937 =
                        let uu____3945 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((Prims.fst lbs), lbs'1), uu____3945) in
                      FStar_Syntax_Syntax.Tm_let uu____3937 in
                    FStar_Syntax_Syntax.mk uu____3936 in
                  uu____3933 None r in
                let uu____3967 =
                  let uu____3973 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___103_3977 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___103_3977.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___103_3977.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___103_3977.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___103_3977.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___103_3977.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___103_3977.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___103_3977.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___103_3977.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___103_3977.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___103_3977.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___103_3977.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___103_3977.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___103_3977.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___103_3977.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___103_3977.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___103_3977.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___103_3977.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___103_3977.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___103_3977.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___103_3977.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___103_3977.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___103_3977.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____3973 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3985;
                       FStar_Syntax_Syntax.pos = uu____3986;
                       FStar_Syntax_Syntax.vars = uu____3987;_},uu____3988,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals2 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4007,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals1
                        | uu____4012 -> quals1 in
                      let quals3 =
                        FStar_List.choose
                          (fun uu___83_4015  ->
                             match uu___83_4015 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4017 =
                                   let uu____4018 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4022 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4022)
                                          else ();
                                          ok) (Prims.snd lbs1) in
                                   Prims.op_Negation uu____4018 in
                                 if uu____4017
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals2 in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs1, r, lids, quals3, attrs)), lbs1)
                  | uu____4037 -> failwith "impossible" in
                (match uu____3967 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (Prims.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              let uu____4064 =
                                FStar_Syntax_Syntax.range_of_fv fv in
                              FStar_TypeChecker_Common.insert_identifier_info
                                (FStar_Util.Inr fv)
                                lb.FStar_Syntax_Syntax.lbtyp uu____4064));
                      (let uu____4066 = log env2 in
                       if uu____4066
                       then
                         let uu____4067 =
                           let uu____4068 =
                             FStar_All.pipe_right (Prims.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4075 =
                                         let uu____4080 =
                                           let uu____4081 =
                                             let uu____4086 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4086.FStar_Syntax_Syntax.fv_name in
                                           uu____4081.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4080 in
                                       match uu____4075 with
                                       | None  -> true
                                       | uu____4093 -> false in
                                     if should_log
                                     then
                                       let uu____4098 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4099 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4098 uu____4099
                                     else "")) in
                           FStar_All.pipe_right uu____4068
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4067
                       else ());
                      (let env3 = FStar_TypeChecker_Env.push_sigelt env2 se1 in
                       ([se1], env3, []))))))
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
             (fun uu___84_4129  ->
                match uu___84_4129 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4130 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4138 -> false in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____4143 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4156,r) ->
          let uu____4164 = is_abstract quals in
          if uu____4164
          then
            let for_export_bundle se1 uu____4183 =
              match uu____4183 with
              | (out,hidden1) ->
                  (match se1 with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4206,uu____4207,quals1,r1) ->
                       let dec =
                         let uu____4217 =
                           let uu____4224 =
                             let uu____4227 = FStar_Syntax_Syntax.mk_Total t in
                             FStar_Syntax_Util.arrow bs uu____4227 in
                           (l, us, uu____4224,
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New :: quals1), r1) in
                         FStar_Syntax_Syntax.Sig_declare_typ uu____4217 in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4238,uu____4239,uu____4240,uu____4241,r1)
                       ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, us, t, [FStar_Syntax_Syntax.Assumption], r1) in
                       ((dec :: out), (l :: hidden1))
                   | uu____4251 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume
          (uu____4263,uu____4264,quals,uu____4266) ->
          let uu____4269 = is_abstract quals in
          if uu____4269 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____4286 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4286
          then
            ([FStar_Syntax_Syntax.Sig_declare_typ
                (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
              hidden))
          else
            (let uu____4296 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___85_4298  ->
                       match uu___85_4298 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____4301 -> false)) in
             if uu____4296 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4311 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____4323,uu____4324,quals,uu____4326) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4344 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4344
          then ([], hidden)
          else
            (let dec =
               FStar_Syntax_Syntax.Sig_declare_typ
                 (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                   (lb.FStar_Syntax_Syntax.lbunivs),
                   (lb.FStar_Syntax_Syntax.lbtyp),
                   [FStar_Syntax_Syntax.Assumption],
                   (FStar_Ident.range_of_lid lid)) in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____4368) ->
          let uu____4375 = is_abstract quals in
          if uu____4375
          then
            let uu____4380 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu____4386 =
                        let uu____4393 =
                          let uu____4394 =
                            let uu____4399 =
                              FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                            uu____4399.FStar_Syntax_Syntax.fv_name in
                          uu____4394.FStar_Syntax_Syntax.v in
                        (uu____4393, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp),
                          (FStar_Syntax_Syntax.Assumption :: quals), r) in
                      FStar_Syntax_Syntax.Sig_declare_typ uu____4386)) in
            (uu____4380, hidden)
          else ([se], hidden)
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4447 se =
        match uu____4447 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4477 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4477
              then
                let uu____4478 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4478
              else ());
             (let uu____4480 = tc_decl env1 se in
              match uu____4480 with
              | (ses',env2,ses_elaborated) ->
                  ((let uu____4504 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4504
                    then
                      let uu____4505 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4508 =
                                 let uu____4509 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4509 "\n" in
                               Prims.strcat s uu____4508) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4505
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4513 =
                      let accum_exports_hidden uu____4531 se1 =
                        match uu____4531 with
                        | (exports1,hidden1) ->
                            let uu____4547 = for_export hidden1 se1 in
                            (match uu____4547 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____4513 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____4597 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4597 with
      | (ses1,exports,env1,uu____4623) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let prepare_env_for_tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let msg = Prims.strcat "Internals for " name in
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
      (let env1 =
         FStar_TypeChecker_Env.set_current_module env
           modul.FStar_Syntax_Syntax.name in
       env1)
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
      (let uu____4659 = FStar_Options.debug_any () in
       if uu____4659
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let env1 = prepare_env_for_tc_decls env modul in
       let uu____4662 = tc_decls env1 modul.FStar_Syntax_Syntax.declarations in
       match uu____4662 with
       | (ses,exports,env2) ->
           ((let uu___104_4680 = modul in
             {
               FStar_Syntax_Syntax.name =
                 (uu___104_4680.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___104_4680.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___104_4680.FStar_Syntax_Syntax.is_interface);
               FStar_Syntax_Syntax.lax_deserialized =
                 (uu___104_4680.FStar_Syntax_Syntax.lax_deserialized)
             }), exports, env2))
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
        let uu____4696 = tc_decls env decls in
        match uu____4696 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___105_4714 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___105_4714.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___105_4714.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___105_4714.FStar_Syntax_Syntax.is_interface);
                FStar_Syntax_Syntax.lax_deserialized =
                  (uu___105_4714.FStar_Syntax_Syntax.lax_deserialized)
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
          let uu___106_4728 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___106_4728.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___106_4728.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___106_4728.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___106_4728.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___106_4728.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___106_4728.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___106_4728.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___106_4728.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___106_4728.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___106_4728.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___106_4728.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___106_4728.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___106_4728.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___106_4728.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___106_4728.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___106_4728.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___106_4728.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___106_4728.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___106_4728.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___106_4728.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___106_4728.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs1 t =
          let uu____4739 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____4739 with
          | (univs2,t1) ->
              ((let uu____4745 =
                  let uu____4746 =
                    let uu____4749 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4749 in
                  FStar_All.pipe_left uu____4746
                    (FStar_Options.Other "Exports") in
                if uu____4745
                then
                  let uu____4750 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____4751 =
                    let uu____4752 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____4752
                      (FStar_String.concat ", ") in
                  let uu____4757 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4750 uu____4751 uu____4757
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____4760 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____4760 Prims.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____4778 =
             let uu____4779 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____4780 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4779 uu____4780 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4778);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt uu___86_4785 =
          match uu___86_4785 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4788,uu____4789)
              ->
              let uu____4796 =
                let uu____4797 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4797 in
              if uu____4796
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4805,uu____4806,uu____4807,r) ->
              let t =
                let uu____4818 =
                  let uu____4821 =
                    let uu____4822 =
                      let uu____4830 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____4830) in
                    FStar_Syntax_Syntax.Tm_arrow uu____4822 in
                  FStar_Syntax_Syntax.mk uu____4821 in
                uu____4818 None r in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____4842,uu____4843,uu____4844,uu____4845,uu____4846)
              -> check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t,quals,uu____4855)
              ->
              let uu____4858 =
                let uu____4859 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4859 in
              if uu____4858 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4862,lbs),uu____4864,uu____4865,quals,uu____4867) ->
              let uu____4879 =
                let uu____4880 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4880 in
              if uu____4879
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
              (l,univs1,binders,comp,quals,flags,r) ->
              let uu____4901 =
                let uu____4902 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4902 in
              if uu____4901
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None r in
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
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let env1 = FStar_TypeChecker_Env.finish_module env modul in
      (let uu____4933 =
         let uu____4934 = FStar_Options.lax () in
         Prims.op_Negation uu____4934 in
       if uu____4933
       then check_exports env1 modul modul.FStar_Syntax_Syntax.exports
       else ());
      (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
        (Prims.strcat "Ending modul "
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str);
      (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
        env1 modul;
      (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
      (let uu____4940 =
         let uu____4941 = FStar_Options.interactive () in
         Prims.op_Negation uu____4941 in
       if uu____4940
       then
         let uu____4942 = FStar_Options.restore_cmd_line_options true in
         FStar_All.pipe_right uu____4942 Prims.ignore
       else ());
      (modul, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____4952 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.lax_deserialized
        then
          let uu____4957 = tc_partial_modul env modul in
          match uu____4957 with
          | (modul1,non_private_decls,env1) ->
              let modul2 =
                let uu___107_4970 = modul1 in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___107_4970.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations =
                    (uu___107_4970.FStar_Syntax_Syntax.declarations);
                  FStar_Syntax_Syntax.exports = non_private_decls;
                  FStar_Syntax_Syntax.is_interface =
                    (modul1.FStar_Syntax_Syntax.is_interface);
                  FStar_Syntax_Syntax.lax_deserialized =
                    (uu___107_4970.FStar_Syntax_Syntax.lax_deserialized)
                } in
              (modul2, env1)
        else
          (FStar_Util.print_string "Tc: module is deserialized\n";
           if Prims.op_Negation env.FStar_TypeChecker_Env.lax
           then failwith "Impossible, expected lax flag in the env"
           else ();
           (let env1 = prepare_env_for_tc_decls env modul in
            let uu____4976 =
              FStar_List.fold_left
                (fun env2  ->
                   fun s  -> FStar_TypeChecker_Env.push_sigelt env2 s) env1
                modul.FStar_Syntax_Syntax.declarations in
            (modul, uu____4976))) in
      match uu____4952 with
      | (modul1,env1) -> finish_partial_modul env1 modul1
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____4992 = FStar_Options.debug_any () in
       if uu____4992
       then
         let uu____4993 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____4993
       else ());
      (let env1 =
         let uu___108_4997 = env in
         let uu____4998 =
           let uu____4999 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____4999 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___108_4997.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___108_4997.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___108_4997.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___108_4997.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___108_4997.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___108_4997.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___108_4997.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___108_4997.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___108_4997.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___108_4997.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___108_4997.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___108_4997.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___108_4997.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___108_4997.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___108_4997.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___108_4997.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___108_4997.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___108_4997.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____4998;
           FStar_TypeChecker_Env.lax_universes =
             (uu___108_4997.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___108_4997.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___108_4997.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___108_4997.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___108_4997.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____5000 = tc_modul env1 m in
       match uu____5000 with
       | (m1,env2) ->
           ((let uu____5008 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5008
             then
               let uu____5009 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5009
             else ());
            (let uu____5012 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5012
             then
               let normalize_toplevel_lets uu___87_5016 =
                 match uu___87_5016 with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),r,ids,qs,attrs) ->
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
                       let uu____5043 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5043 with
                       | (univnames1,e) ->
                           let uu___109_5048 = lb in
                           let uu____5049 =
                             let uu____5052 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5052 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___109_5048.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___109_5048.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___109_5048.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___109_5048.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5049
                           } in
                     let uu____5053 =
                       let uu____5062 =
                         let uu____5066 = FStar_List.map update lbs in
                         (b, uu____5066) in
                       (uu____5062, r, ids, qs, attrs) in
                     FStar_Syntax_Syntax.Sig_let uu____5053
                 | se -> se in
               let normalized_module =
                 let uu___110_5077 = m1 in
                 let uu____5078 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___110_5077.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5078;
                   FStar_Syntax_Syntax.exports =
                     (uu___110_5077.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___110_5077.FStar_Syntax_Syntax.is_interface);
                   FStar_Syntax_Syntax.lax_deserialized =
                     (uu___110_5077.FStar_Syntax_Syntax.lax_deserialized)
                 } in
               let uu____5079 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5079
             else ());
            (m1, env2)))