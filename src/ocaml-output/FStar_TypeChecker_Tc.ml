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
          let uu___83_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___83_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___83_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___83_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___83_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___83_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___83_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___83_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___83_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___83_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___83_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___83_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___83_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___83_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___83_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___83_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___83_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___83_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___83_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___83_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___83_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___83_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___83_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___83_12.FStar_TypeChecker_Env.use_bv_sorts);
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
          let uu___84_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___84_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___84_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___84_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___84_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___84_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___84_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___84_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___84_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___84_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___84_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___84_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___84_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___84_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___84_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___84_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___84_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___84_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___84_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___84_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___84_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___84_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___84_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___84_24.FStar_TypeChecker_Env.use_bv_sorts);
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
        | (t,c,g) ->
            (FStar_ST.write t.FStar_Syntax_Syntax.tk
               (Some ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t)
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
  let t = tc_check_trivial_guard env t k in
  let uu____108 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t in
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
        let s = FStar_Syntax_Subst.compress s in
        match s.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs = FStar_Syntax_Subst.open_binders bs in
            (match bs with
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
                    let ed =
                      let uu___85_258 = ed in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___85_258.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___85_258.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___85_258.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___85_258.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___85_258.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___85_258.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___85_258.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___85_258.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___85_258.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___85_258.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___85_258.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___85_258.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___85_258.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___85_258.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___85_258.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___85_258.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___85_258.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___85_258.FStar_Syntax_Syntax.actions)
                      } in
                    let ed =
                      match effect_params with
                      | [] -> ed
                      | uu____262 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts) in
                            ([], t1) in
                          let uu___86_280 = ed in
                          let uu____281 = op ed.FStar_Syntax_Syntax.ret_wp in
                          let uu____282 = op ed.FStar_Syntax_Syntax.bind_wp in
                          let uu____283 =
                            op ed.FStar_Syntax_Syntax.if_then_else in
                          let uu____284 = op ed.FStar_Syntax_Syntax.ite_wp in
                          let uu____285 = op ed.FStar_Syntax_Syntax.stronger in
                          let uu____286 = op ed.FStar_Syntax_Syntax.close_wp in
                          let uu____287 = op ed.FStar_Syntax_Syntax.assert_p in
                          let uu____288 = op ed.FStar_Syntax_Syntax.assume_p in
                          let uu____289 = op ed.FStar_Syntax_Syntax.null_wp in
                          let uu____290 = op ed.FStar_Syntax_Syntax.trivial in
                          let uu____291 =
                            let uu____292 =
                              op ([], (ed.FStar_Syntax_Syntax.repr)) in
                            Prims.snd uu____292 in
                          let uu____298 =
                            op ed.FStar_Syntax_Syntax.return_repr in
                          let uu____299 = op ed.FStar_Syntax_Syntax.bind_repr in
                          let uu____300 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___87_303 = a in
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
                                     (uu___87_303.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___87_303.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___87_303.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____304;
                                   FStar_Syntax_Syntax.action_typ = uu____311
                                 }) ed.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___86_280.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___86_280.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___86_280.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___86_280.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___86_280.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___86_280.FStar_Syntax_Syntax.signature);
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
                    let wp_with_fresh_result_type env mname signature =
                      let fail t =
                        let uu____340 =
                          let uu____341 =
                            let uu____344 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env mname t in
                            (uu____344, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____341 in
                        Prims.raise uu____340 in
                      let uu____349 =
                        let uu____350 = FStar_Syntax_Subst.compress signature in
                        uu____350.FStar_Syntax_Syntax.n in
                      match uu____349 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs = FStar_Syntax_Subst.open_binders bs in
                          (match bs with
                           | (a,uu____375)::(wp,uu____377)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____386 -> fail signature)
                      | uu____387 -> fail signature in
                    let uu____388 =
                      wp_with_fresh_result_type env
                        ed.FStar_Syntax_Syntax.mname
                        ed.FStar_Syntax_Syntax.signature in
                    (match uu____388 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____406 =
                           let uu____407 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____407 with
                           | (signature,uu____415) ->
                               wp_with_fresh_result_type env
                                 ed.FStar_Syntax_Syntax.mname signature in
                         let env =
                           let uu____417 =
                             FStar_Syntax_Syntax.new_bv None
                               ed.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____417 in
                         ((let uu____419 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____419
                           then
                             let uu____420 =
                               FStar_Syntax_Print.lid_to_string
                                 ed.FStar_Syntax_Syntax.mname in
                             let uu____421 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed.FStar_Syntax_Syntax.binders in
                             let uu____422 =
                               FStar_Syntax_Print.term_to_string
                                 ed.FStar_Syntax_Syntax.signature in
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
                          (let check_and_gen' env uu____438 k =
                             match uu____438 with
                             | (uu____443,t) -> check_and_gen env t k in
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
                             check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp
                               expected_k in
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
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else =
                             let p =
                               let uu____512 =
                                 let uu____513 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____513 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname))
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
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.if_then_else expected_k in
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
                             check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp
                               expected_k in
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
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.stronger expected_k in
                           let close_wp =
                             let b =
                               let uu____578 =
                                 let uu____579 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____579 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname))
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
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.close_wp expected_k in
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
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assert_p expected_k in
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
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____665 =
                                 let uu____669 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____669] in
                               let uu____670 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____665 uu____670 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.null_wp expected_k in
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
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____693 =
                             let uu____699 =
                               let uu____700 =
                                 FStar_Syntax_Subst.compress
                                   ed.FStar_Syntax_Syntax.repr in
                               uu____700.FStar_Syntax_Syntax.n in
                             match uu____699 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed.FStar_Syntax_Syntax.repr),
                                   (ed.FStar_Syntax_Syntax.bind_repr),
                                   (ed.FStar_Syntax_Syntax.return_repr),
                                   (ed.FStar_Syntax_Syntax.actions))
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
                                       tc_check_trivial_guard env
                                         ed.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env repr in
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
                                         (repr, uu____754) in
                                       FStar_Syntax_Syntax.Tm_app uu____744 in
                                     FStar_Syntax_Syntax.mk uu____743 in
                                   uu____740 None FStar_Range.dummyRange in
                                 let mk_repr a wp =
                                   let uu____778 =
                                     FStar_Syntax_Syntax.bv_to_name a in
                                   mk_repr' uu____778 wp in
                                 let destruct_repr t =
                                   let uu____789 =
                                     let uu____790 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____790.FStar_Syntax_Syntax.n in
                                   match uu____789 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____799,(t,uu____801)::(wp,uu____803)::[])
                                       -> (t, wp)
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
                                           env expected_k in
                                       (match uu____956 with
                                        | (expected_k,uu____961,uu____962) ->
                                            let env =
                                              FStar_TypeChecker_Env.set_range
                                                env
                                                (Prims.snd
                                                   ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env =
                                              let uu___88_966 = env in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___88_966.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___88_966.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___88_966.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___88_966.FStar_TypeChecker_Env.qname_and_index)
                                              } in
                                            let br =
                                              check_and_gen' env
                                                ed.FStar_Syntax_Syntax.bind_repr
                                                expected_k in
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
                                       env expected_k in
                                   match uu____1012 with
                                   | (expected_k,uu____1020,uu____1021) ->
                                       let env =
                                         FStar_TypeChecker_Env.set_range env
                                           (Prims.snd
                                              ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1024 =
                                         check_and_gen' env
                                           ed.FStar_Syntax_Syntax.return_repr
                                           expected_k in
                                       (match uu____1024 with
                                        | (univs,repr) ->
                                            (match univs with
                                             | [] -> ([], repr)
                                             | uu____1036 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1047 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1047 with
                                     | (act_typ,uu____1052,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env act_typ in
                                         ((let uu____1056 =
                                             FStar_TypeChecker_Env.debug env
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
                                               let act_defn =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant]
                                                   env act_defn in
                                               let act_typ =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant;
                                                   FStar_TypeChecker_Normalize.Eager_unfolding;
                                                   FStar_TypeChecker_Normalize.Beta]
                                                   env act_typ in
                                               let uu____1069 =
                                                 let act_typ =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ in
                                                 match act_typ.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1087 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1087 with
                                                      | (bs,uu____1093) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1100 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs uu____1100 in
                                                          let uu____1103 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env k in
                                                          (match uu____1103
                                                           with
                                                           | (k,uu____1110,g)
                                                               -> (k, g)))
                                                 | uu____1112 ->
                                                     let uu____1113 =
                                                       let uu____1114 =
                                                         let uu____1117 =
                                                           let uu____1118 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ in
                                                           let uu____1119 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1118
                                                             uu____1119 in
                                                         (uu____1117,
                                                           (act_defn.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1114 in
                                                     Prims.raise uu____1113 in
                                               (match uu____1069 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env act_typ
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
                                                        env uu____1126);
                                                     (let act_typ =
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
                                                             | (bs,c) ->
                                                                 let uu____1157
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c) in
                                                                 (match uu____1157
                                                                  with
                                                                  | (a,wp) ->
                                                                    let c =
                                                                    let uu____1177
                                                                    =
                                                                    let uu____1178
                                                                    =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env a in
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
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1179;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1186
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs
                                                                    uu____1186))
                                                        | uu____1189 ->
                                                            failwith "" in
                                                      let uu____1192 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env act_defn in
                                                      match uu____1192 with
                                                      | (univs,act_defn) ->
                                                          let act_typ =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env act_typ in
                                                          let uu___89_1198 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___89_1198.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___89_1198.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs;
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____693 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1214 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed.FStar_Syntax_Syntax.binders uu____1214 in
                               let uu____1217 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1217 with
                                | (univs,t) ->
                                    let signature =
                                      let uu____1223 =
                                        let uu____1226 =
                                          let uu____1227 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1227.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1226) in
                                      match uu____1223 with
                                      | ([],uu____1230) -> t
                                      | (uu____1236,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1237,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1249 -> failwith "Impossible" in
                                    let close n ts =
                                      let ts =
                                        let uu____1260 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs uu____1260 in
                                      let m =
                                        FStar_List.length (Prims.fst ts) in
                                      (let uu____1265 =
                                         ((n >= (Prims.parse_int "0")) &&
                                            (let uu____1266 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts) in
                                             Prims.op_Negation uu____1266))
                                           && (m <> n) in
                                       if uu____1265
                                       then
                                         let error =
                                           if m < n
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1275 =
                                           let uu____1276 =
                                             FStar_Util.string_of_int n in
                                           let uu____1277 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1276 uu____1277 in
                                         failwith uu____1275
                                       else ());
                                      ts in
                                    let close_action act =
                                      let uu____1283 =
                                        close (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1283 with
                                      | (univs,defn) ->
                                          let uu____1288 =
                                            close (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1288 with
                                           | (univs',typ) ->
                                               let uu___90_1294 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___90_1294.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___90_1294.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs;
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let nunivs = FStar_List.length univs in
                                    let ed =
                                      let uu___91_1299 = ed in
                                      let uu____1300 =
                                        close (Prims.parse_int "0") return_wp in
                                      let uu____1301 =
                                        close (Prims.parse_int "1") bind_wp in
                                      let uu____1302 =
                                        close (Prims.parse_int "0")
                                          if_then_else in
                                      let uu____1303 =
                                        close (Prims.parse_int "0") ite_wp in
                                      let uu____1304 =
                                        close (Prims.parse_int "0") stronger in
                                      let uu____1305 =
                                        close (Prims.parse_int "1") close_wp in
                                      let uu____1306 =
                                        close (Prims.parse_int "0") assert_p in
                                      let uu____1307 =
                                        close (Prims.parse_int "0") assume_p in
                                      let uu____1308 =
                                        close (Prims.parse_int "0") null_wp in
                                      let uu____1309 =
                                        close (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1310 =
                                        let uu____1311 =
                                          close (Prims.parse_int "0")
                                            ([], repr) in
                                        Prims.snd uu____1311 in
                                      let uu____1317 =
                                        close (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1318 =
                                        close (Prims.parse_int "1") bind_repr in
                                      let uu____1319 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___91_1299.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___91_1299.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___91_1299.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature;
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
                                        (FStar_TypeChecker_Env.debug env
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1322
                                      then
                                        let uu____1323 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed in
                                        FStar_Util.print_string uu____1323
                                      else ());
                                     ed)))))))
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
           | (effect_binders,env,uu____1348) ->
               let uu____1349 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____1349 with
                | (signature,uu____1358) ->
                    let effect_binders =
                      FStar_List.map
                        (fun uu____1367  ->
                           match uu____1367 with
                           | (bv,qual) ->
                               let uu____1374 =
                                 let uu___92_1375 = bv in
                                 let uu____1376 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___92_1375.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___92_1375.FStar_Syntax_Syntax.index);
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
                         let a =
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
                           let subst =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders in
                           let t = FStar_Syntax_Subst.subst subst t in
                           let uu____1438 =
                             FStar_TypeChecker_TcTerm.tc_term env t in
                           match uu____1438 with
                           | (t,comp,uu____1446) -> (t, comp) in
                         let mk x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1457 =
                           open_and_check ed.FStar_Syntax_Syntax.repr in
                         (match uu____1457 with
                          | (repr,_comp) ->
                              ((let uu____1468 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "ED") in
                                if uu____1468
                                then
                                  let uu____1469 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1469
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type = recheck_debug "*" env wp_type in
                                let wp_a =
                                  let uu____1475 =
                                    let uu____1476 =
                                      let uu____1477 =
                                        let uu____1487 =
                                          let uu____1491 =
                                            let uu____1494 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            let uu____1495 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1494, uu____1495) in
                                          [uu____1491] in
                                        (wp_type, uu____1487) in
                                      FStar_Syntax_Syntax.Tm_app uu____1477 in
                                    mk uu____1476 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env
                                    uu____1475 in
                                let effect_signature =
                                  let binders =
                                    let uu____1510 =
                                      let uu____1513 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a, uu____1513) in
                                    let uu____1514 =
                                      let uu____1518 =
                                        let uu____1519 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1519
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1518] in
                                    uu____1510 :: uu____1514 in
                                  let binders =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders, effect_marker)) in
                                let effect_signature =
                                  recheck_debug
                                    "turned into the effect signature" env
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
                                let elaborate_and_star dmff_env item =
                                  let uu____1552 = item in
                                  match uu____1552 with
                                  | (u_item,item) ->
                                      let uu____1564 = open_and_check item in
                                      (match uu____1564 with
                                       | (item,item_comp) ->
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
                                                       item in
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
                                                 dmff_env item in
                                             match uu____1581 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp =
                                                   recheck_debug "*" env
                                                     item_wp in
                                                 let item_elab =
                                                   recheck_debug "_" env
                                                     item_elab in
                                                 (dmff_env, item_t, item_wp,
                                                   item_elab)))) in
                                let uu____1594 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1594 with
                                | (dmff_env,uu____1605,bind_wp,bind_elab) ->
                                    let uu____1608 =
                                      elaborate_and_star dmff_env
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1608 with
                                     | (dmff_env,uu____1619,return_wp,return_elab)
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
                                                 | (b1::b2::[],body) ->
                                                     (b1, b2, body)
                                                 | uu____1712 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1662 with
                                                | (b1,b2,body) ->
                                                    let env0 =
                                                      let uu____1734 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1734 [b1; b2] in
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
                                                                    b1) in
                                                                let uu____1764
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1763,
                                                                  uu____1764) in
                                                              [uu____1760] in
                                                            (wp_type,
                                                              uu____1756) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1746 in
                                                        mk uu____1745 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1772 =
                                                      let uu____1782 =
                                                        let uu____1783 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          body uu____1783 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1782 in
                                                    (match uu____1772 with
                                                     | (bs,body,what') ->
                                                         let fail uu____1811
                                                           =
                                                           let error_msg =
                                                             let uu____1813 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body in
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
                                                                    env
                                                                    lc.FStar_Syntax_Syntax.res_typ
                                                                    FStar_Syntax_Util.ktype0 in
                                                                 (match g_opt
                                                                  with
                                                                  | Some g'
                                                                    ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env g'
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
                                                               (Prims.fst b2).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp" None
                                                               pure_wp_type in
                                                           let body =
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
                                                                    [b2] body
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
                                                             b1 :: uu____1909 in
                                                           let uu____1916 =
                                                             FStar_Syntax_Util.abs
                                                               bs body what in
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
                                         let return_wp =
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
                                         let bind_wp =
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
                                                       mk
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
                                                effect_binders)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2041 =
                                                let uu____2042 =
                                                  let uu____2043 =
                                                    let uu____2053 =
                                                      let uu____2054 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders in
                                                      Prims.snd uu____2054 in
                                                    (t, uu____2053) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2043 in
                                                mk uu____2042 in
                                              FStar_Syntax_Subst.close
                                                effect_binders uu____2041) in
                                         let register name item =
                                           let uu____2066 =
                                             let uu____2069 = mk_lid name in
                                             let uu____2070 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders item None in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env uu____2069 uu____2070 in
                                           match uu____2066 with
                                           | (sigelt,fv) ->
                                               ((let uu____2079 =
                                                   let uu____2081 =
                                                     FStar_ST.read sigelts in
                                                   sigelt :: uu____2081 in
                                                 FStar_ST.write sigelts
                                                   uu____2079);
                                                fv) in
                                         let lift_from_pure_wp =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp =
                                           register "return_wp" return_wp in
                                         ((let uu____2092 =
                                             let uu____2094 =
                                               FStar_ST.read sigelts in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: uu____2094 in
                                           FStar_ST.write sigelts uu____2092);
                                          (let return_elab =
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
                                           (let bind_wp =
                                              register "bind_wp" bind_wp in
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
                                            (let bind_elab =
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
                                                       | (dmff_env,actions)
                                                           ->
                                                           let uu____2157 =
                                                             elaborate_and_star
                                                               dmff_env
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn)) in
                                                           (match uu____2157
                                                            with
                                                            | (dmff_env,action_t,action_wp,action_elab)
                                                                ->
                                                                let name =
                                                                  ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                let action_typ_with_wp
                                                                  =
                                                                  FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env
                                                                    action_t
                                                                    action_wp in
                                                                let action_elab
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab in
                                                                let action_typ_with_wp
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
                                                                    let uu___93_2176
                                                                    = action in
                                                                    let uu____2177
                                                                    =
                                                                    apply_close
                                                                    action_elab in
                                                                    let uu____2178
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___93_2176.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___93_2176.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___93_2176.FStar_Syntax_Syntax.action_univs);
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
                                                                (dmff_env,
                                                                  uu____2173)))
                                                  (dmff_env, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2138 with
                                              | (dmff_env,actions) ->
                                                  let actions =
                                                    FStar_List.rev actions in
                                                  let repr =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2196 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a in
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
                                                                    a in
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
                                                        mk uu____2202 in
                                                      let uu____2229 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env uu____2201
                                                        uu____2229 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2200 None in
                                                  let repr =
                                                    recheck_debug "FC" env
                                                      repr in
                                                  let repr =
                                                    register "repr" repr in
                                                  let uu____2237 =
                                                    let uu____2242 =
                                                      let uu____2243 =
                                                        let uu____2246 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2246 in
                                                      uu____2243.FStar_Syntax_Syntax.n in
                                                    match uu____2242 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow,uu____2254)
                                                        ->
                                                        let uu____2281 =
                                                          let uu____2290 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow in
                                                          match uu____2290
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2321 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2281
                                                         with
                                                         | (type_param,effect_param,arrow)
                                                             ->
                                                             let uu____2349 =
                                                               let uu____2350
                                                                 =
                                                                 let uu____2353
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow in
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
                                                                   (wp_binders,c)
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
                                                                    type_param)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2395
                                                                    Prims.op_Negation)
                                                                    wp_binders in
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
                                                                    arrow in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2434 in
                                                                    failwith
                                                                    uu____2433 in
                                                                    let uu____2437
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c in
                                                                    let uu____2440
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
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
                                                                    arrow in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2452 in
                                                                  failwith
                                                                    uu____2451))
                                                    | uu____2457 ->
                                                        let uu____2458 =
                                                          let uu____2459 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type in
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
                                                             wp_type in
                                                         ());
                                                        (let ed =
                                                           let uu___94_2482 =
                                                             ed in
                                                           let uu____2483 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders in
                                                           let uu____2484 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders
                                                               effect_signature in
                                                           let uu____2485 =
                                                             let uu____2486 =
                                                               apply_close
                                                                 return_wp in
                                                             ([], uu____2486) in
                                                           let uu____2492 =
                                                             let uu____2493 =
                                                               apply_close
                                                                 bind_wp in
                                                             ([], uu____2493) in
                                                           let uu____2499 =
                                                             apply_close repr in
                                                           let uu____2500 =
                                                             let uu____2501 =
                                                               apply_close
                                                                 return_elab in
                                                             ([], uu____2501) in
                                                           let uu____2507 =
                                                             let uu____2508 =
                                                               apply_close
                                                                 bind_elab in
                                                             ([], uu____2508) in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.univs);
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
                                                               (uu___94_2482.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___94_2482.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2499;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2500;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2507;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions
                                                           } in
                                                         let uu____2514 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env
                                                             effect_binders a
                                                             wp_a ed in
                                                         match uu____2514
                                                         with
                                                         | (sigelts',ed) ->
                                                             ((let uu____2525
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2525
                                                               then
                                                                 let uu____2526
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed in
                                                                 FStar_Util.print_string
                                                                   uu____2526
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders)
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
                                                                    lift_from_pure_wp in
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
                                                                    (ed.FStar_Syntax_Syntax.mname);
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
                                                                 ed,
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
              (lex_t,[],[],t,uu____2583,uu____2584,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top,[],_t_top,_lex_t_top,_0_28,[],uu____2589,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_29,[],uu____2594,r2))::[]
              when
              ((_0_28 = (Prims.parse_int "0")) &&
                 (_0_29 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top
                       FStar_Syntax_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Syntax_Const.lexcons_lid))
              ->
              let u = FStar_Syntax_Syntax.new_univ_name (Some r) in
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r in
              let t = FStar_Syntax_Subst.close_univ_vars [u] t in
              let tc =
                FStar_Syntax_Syntax.Sig_inductive_typ
                  (lex_t, [u], [], t, [],
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
              let lex_top_t =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_top, [utop], lex_top_t, FStar_Syntax_Const.lex_t_lid,
                    (Prims.parse_int "0"), [], [], r1) in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let lex_cons_t =
                let a =
                  let uu____2668 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2668 in
                let hd =
                  let uu____2674 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2674 in
                let tl =
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
                  (hd, None);
                  (tl, None)] uu____2718 in
              let lex_cons_t =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons, [ucons1; ucons2], lex_cons_t,
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
            let env = FStar_TypeChecker_Env.set_range env r in
            let uu____2767 = FStar_Syntax_Util.type_u () in
            match uu____2767 with
            | (k,uu____2771) ->
                let phi =
                  let uu____2773 = tc_check_trivial_guard env phi k in
                  FStar_All.pipe_right uu____2773
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env) in
                (FStar_TypeChecker_Util.check_uvars r phi;
                 FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r))
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
                  (let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env in
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
                   let ses =
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
                     uu____2886 :: ses in
                   (uu____2884, data_ops_ses))))
and tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun se  ->
      let env = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (match se with
       | FStar_Syntax_Syntax.Sig_inductive_typ _
         |FStar_Syntax_Syntax.Sig_datacon _ ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let se = tc_lex_t env ses quals lids in
           let uu____2935 = FStar_TypeChecker_Env.push_sigelt env se in
           ([se], uu____2935, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____2949 = tc_inductive env ses quals lids in
           (match uu____2949 with
            | (ses,projectors_ses) ->
                let env =
                  FStar_List.fold_left
                    (fun env'  ->
                       fun se  -> FStar_TypeChecker_Env.push_sigelt env' se)
                    env ses in
                (ses, env, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma (p,r) ->
           let set_options t s =
             let uu____2979 = FStar_Options.set_options t s in
             match uu____2979 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s), r)) in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], env, []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options FStar_Options.Set o; ([se], env, []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____2997 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____2997 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options FStar_Options.Reset s);
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
           let uu____3005 = cps_and_elaborate env ne in
           (match uu____3005 with
            | (ses,ne,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [FStar_Syntax_Syntax.Sig_new_effect (ne, r); lift]
                  | None  -> [FStar_Syntax_Syntax.Sig_new_effect (ne, r)] in
                ([], env, (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect (ne,r) ->
           let ne = tc_eff_decl env ne in
           let se = FStar_Syntax_Syntax.Sig_new_effect (ne, r) in
           let env = FStar_TypeChecker_Env.push_sigelt env se in
           let uu____3034 =
             FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____3045  ->
                     fun a  ->
                       match uu____3045 with
                       | (env,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne.FStar_Syntax_Syntax.mname a in
                           let uu____3058 =
                             FStar_TypeChecker_Env.push_sigelt env se_let in
                           (uu____3058, (se_let :: ses))) (env, [se])) in
           (match uu____3034 with | (env,ses) -> ([se], env, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub,r) ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub.FStar_Syntax_Syntax.target in
           let uu____3076 =
             let uu____3081 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____3081 in
           (match uu____3076 with
            | (a,wp_a_src) ->
                let uu____3093 =
                  let uu____3098 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub.FStar_Syntax_Syntax.target in
                  monad_signature env sub.FStar_Syntax_Syntax.target
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
                     let repr_type eff_name a wp =
                       let no_reify l =
                         let uu____3152 =
                           let uu____3153 =
                             let uu____3156 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3157 =
                               FStar_TypeChecker_Env.get_range env in
                             (uu____3156, uu____3157) in
                           FStar_Errors.Error uu____3153 in
                         Prims.raise uu____3152 in
                       let uu____3160 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____3160 with
                       | None  -> no_reify eff_name
                       | Some ed ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
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
                                FStar_TypeChecker_Env.get_range env in
                              let uu____3174 =
                                let uu____3177 =
                                  let uu____3178 =
                                    let uu____3188 =
                                      let uu____3190 =
                                        FStar_Syntax_Syntax.as_arg a in
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
                       match ((sub.FStar_Syntax_Syntax.lift),
                               (sub.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3218,lift_wp)) ->
                           let uu____3231 =
                             check_and_gen env lift_wp expected_k in
                           (lift, uu____3231)
                       | (Some (what,lift),None ) ->
                           ((let uu____3246 =
                               FStar_TypeChecker_Env.debug env
                                 (FStar_Options.Other "ED") in
                             if uu____3246
                             then
                               let uu____3247 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3247
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3250 =
                               FStar_TypeChecker_TcTerm.tc_term env lift in
                             match uu____3250 with
                             | (lift,comp,uu____3259) ->
                                 let uu____3260 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift in
                                 (match uu____3260 with
                                  | (uu____3267,lift_wp,lift_elab) ->
                                      let uu____3270 =
                                        recheck_debug "lift-wp" env lift_wp in
                                      let uu____3271 =
                                        recheck_debug "lift-elab" env
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3203 with
                      | (lift,lift_wp) ->
                          let lax = env.FStar_TypeChecker_Env.lax in
                          let env =
                            let uu___95_3295 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___95_3295.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___95_3295.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___95_3295.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___95_3295.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___95_3295.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___95_3295.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___95_3295.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___95_3295.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___95_3295.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___95_3295.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___95_3295.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___95_3295.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___95_3295.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___95_3295.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___95_3295.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___95_3295.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___95_3295.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___95_3295.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___95_3295.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___95_3295.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___95_3295.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___95_3295.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___95_3295.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift =
                            match lift with
                            | None  -> None
                            | Some (uu____3299,lift) ->
                                let uu____3306 =
                                  let uu____3311 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env sub.FStar_Syntax_Syntax.source in
                                  monad_signature env
                                    sub.FStar_Syntax_Syntax.source uu____3311 in
                                (match uu____3306 with
                                 | (a,wp_a_src) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub.FStar_Syntax_Syntax.source a_typ
                                         wp_a_typ in
                                     let repr_result =
                                       let lift_wp =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env (Prims.snd lift_wp) in
                                       let lift_wp_a =
                                         let uu____3333 =
                                           FStar_TypeChecker_Env.get_range
                                             env in
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
                                               (lift_wp, uu____3348) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3338 in
                                           FStar_Syntax_Syntax.mk uu____3337 in
                                         uu____3334 None uu____3333 in
                                       repr_type
                                         sub.FStar_Syntax_Syntax.target a_typ
                                         lift_wp_a in
                                     let expected_k =
                                       let uu____3366 =
                                         let uu____3370 =
                                           FStar_Syntax_Syntax.mk_binder a in
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
                                         env expected_k in
                                     (match uu____3380 with
                                      | (expected_k,uu____3386,uu____3387) ->
                                          let lift =
                                            check_and_gen env lift expected_k in
                                          Some lift)) in
                          let env =
                            let uu___96_3390 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___96_3390.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___96_3390.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___96_3390.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___96_3390.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___96_3390.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___96_3390.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___96_3390.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___96_3390.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___96_3390.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___96_3390.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___96_3390.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___96_3390.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___96_3390.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___96_3390.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___96_3390.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___96_3390.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___96_3390.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___96_3390.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = lax;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___96_3390.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___96_3390.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___96_3390.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___96_3390.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___96_3390.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let sub =
                            let uu___97_3392 = sub in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___97_3392.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___97_3392.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift
                            } in
                          let se =
                            FStar_Syntax_Syntax.Sig_sub_effect (sub, r) in
                          let env = FStar_TypeChecker_Env.push_sigelt env se in
                          ([se], env, []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env in
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____3411 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3411 with
            | (tps,c) ->
                let uu____3421 = FStar_TypeChecker_TcTerm.tc_tparams env tps in
                (match uu____3421 with
                 | (tps,env,us) ->
                     let uu____3433 = FStar_TypeChecker_TcTerm.tc_comp env c in
                     (match uu____3433 with
                      | (c,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env g;
                           (let tps = FStar_Syntax_Subst.close_binders tps in
                            let c = FStar_Syntax_Subst.close_comp tps c in
                            let uu____3448 =
                              let uu____3449 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3449 in
                            match uu____3448 with
                            | (uvs,t) ->
                                let uu____3463 =
                                  let uu____3471 =
                                    let uu____3474 =
                                      let uu____3475 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3475.FStar_Syntax_Syntax.n in
                                    (tps, uu____3474) in
                                  match uu____3471 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3485,c)) -> ([], c)
                                  | (uu____3509,FStar_Syntax_Syntax.Tm_arrow
                                     (tps,c)) -> (tps, c)
                                  | uu____3527 -> failwith "Impossible" in
                                (match uu____3463 with
                                 | (tps,c) ->
                                     (if
                                        ((FStar_List.length uvs) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3557 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs t in
                                         match uu____3557 with
                                         | (uu____3560,t) ->
                                             let uu____3562 =
                                               let uu____3563 =
                                                 let uu____3566 =
                                                   let uu____3567 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3568 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length uvs)
                                                       FStar_Util.string_of_int in
                                                   let uu____3571 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3567 uu____3568
                                                     uu____3571 in
                                                 (uu____3566, r) in
                                               FStar_Errors.Error uu____3563 in
                                             Prims.raise uu____3562)
                                      else ();
                                      (let se =
                                         FStar_Syntax_Syntax.Sig_effect_abbrev
                                           (lid, uvs, tps, c, tags, flags, r) in
                                       let env =
                                         FStar_TypeChecker_Env.push_sigelt
                                           env0 se in
                                       ([se], env, [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals,_)
         |FStar_Syntax_Syntax.Sig_let (_,_,_,quals,_) when
           FStar_All.pipe_right quals
             (FStar_Util.for_some
                (fun uu___77_3601  ->
                   match uu___77_3601 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3602 -> false))
           -> ([], env, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____3613 =
             if uvs = []
             then
               let uu____3614 =
                 let uu____3615 = FStar_Syntax_Util.type_u () in
                 Prims.fst uu____3615 in
               check_and_gen env t uu____3614
             else
               (let uu____3619 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3619 with
                | (uvs,t) ->
                    let t =
                      let uu____3625 =
                        let uu____3626 = FStar_Syntax_Util.type_u () in
                        Prims.fst uu____3626 in
                      tc_check_trivial_guard env t uu____3625 in
                    let t =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env t in
                    let uu____3630 = FStar_Syntax_Subst.close_univ_vars uvs t in
                    (uvs, uu____3630)) in
           (match uu____3613 with
            | (uvs,t) ->
                let se =
                  FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) in
                let env = FStar_TypeChecker_Env.push_sigelt env se in
                ([se], env, []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi,quals,r) ->
           let se = tc_assume env lid phi quals r in
           let env = FStar_TypeChecker_Env.push_sigelt env se in
           ([se], env, [])
       | FStar_Syntax_Syntax.Sig_main (e,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let env =
             FStar_TypeChecker_Env.set_expected_typ env
               FStar_TypeChecker_Common.t_unit in
           let uu____3660 = FStar_TypeChecker_TcTerm.tc_term env e in
           (match uu____3660 with
            | (e,c,g1) ->
                let uu____3672 =
                  let uu____3676 =
                    let uu____3678 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3678 in
                  let uu____3679 =
                    let uu____3682 = c.FStar_Syntax_Syntax.comp () in
                    (e, uu____3682) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env
                    uu____3676 uu____3679 in
                (match uu____3672 with
                 | (e,uu____3693,g) ->
                     ((let uu____3696 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env
                         uu____3696);
                      (let se = FStar_Syntax_Syntax.Sig_main (e, r) in
                       let env = FStar_TypeChecker_Env.push_sigelt env se in
                       ([se], env, [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,r,lids,quals,attrs) ->
           let env = FStar_TypeChecker_Env.set_range env r in
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
                       | (gen,lbs,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3802 =
                             let uu____3808 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3808 with
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen, lb, quals_opt)
                             | Some ((uvs,tval),quals) ->
                                 let quals_opt =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
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
                                   (false, uu____3868, quals_opt))) in
                           (match uu____3802 with
                            | (gen,lb,quals_opt) ->
                                (gen, (lb :: lbs), quals_opt)))
                  (true, [], (if quals = [] then None else Some quals))) in
           (match uu____3757 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3922 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___78_3924  ->
                                match uu___78_3924 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3925 -> false)) in
                      if uu____3922
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs' = FStar_List.rev lbs' in
                let e =
                  let uu____3933 =
                    let uu____3936 =
                      let uu____3937 =
                        let uu____3945 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((Prims.fst lbs), lbs'), uu____3945) in
                      FStar_Syntax_Syntax.Tm_let uu____3937 in
                    FStar_Syntax_Syntax.mk uu____3936 in
                  uu____3933 None r in
                let uu____3967 =
                  let uu____3973 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___98_3977 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___98_3977.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___98_3977.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___98_3977.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___98_3977.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___98_3977.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___98_3977.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___98_3977.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___98_3977.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___98_3977.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___98_3977.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___98_3977.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___98_3977.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___98_3977.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___98_3977.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___98_3977.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___98_3977.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___98_3977.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___98_3977.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___98_3977.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___98_3977.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___98_3977.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___98_3977.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____3973 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs,e);
                       FStar_Syntax_Syntax.tk = uu____3985;
                       FStar_Syntax_Syntax.pos = uu____3986;
                       FStar_Syntax_Syntax.vars = uu____3987;_},uu____3988,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals =
                        match e.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4007,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4012 -> quals in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs, r, lids, quals, attrs)), lbs)
                  | uu____4022 -> failwith "impossible" in
                (match uu____3967 with
                 | (se,lbs) ->
                     ((let uu____4045 = log env in
                       if uu____4045
                       then
                         let uu____4046 =
                           let uu____4047 =
                             FStar_All.pipe_right (Prims.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4054 =
                                         let uu____4059 =
                                           let uu____4060 =
                                             let uu____4065 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4065.FStar_Syntax_Syntax.fv_name in
                                           uu____4060.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env uu____4059 in
                                       match uu____4054 with
                                       | None  -> true
                                       | uu____4072 -> false in
                                     if should_log
                                     then
                                       let uu____4077 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4078 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4077 uu____4078
                                     else "")) in
                           FStar_All.pipe_right uu____4047
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4046
                       else ());
                      (let env = FStar_TypeChecker_Env.push_sigelt env se in
                       ([se], env, []))))))
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
             (fun uu___79_4108  ->
                match uu___79_4108 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4109 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4117 -> false in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____4122 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4135,r) ->
          let uu____4143 = is_abstract quals in
          if uu____4143
          then
            let for_export_bundle se uu____4162 =
              match uu____4162 with
              | (out,hidden) ->
                  (match se with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4185,uu____4186,quals,r) ->
                       let dec =
                         let uu____4196 =
                           let uu____4203 =
                             let uu____4206 = FStar_Syntax_Syntax.mk_Total t in
                             FStar_Syntax_Util.arrow bs uu____4206 in
                           (l, us, uu____4203,
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New :: quals), r) in
                         FStar_Syntax_Syntax.Sig_declare_typ uu____4196 in
                       ((dec :: out), hidden)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4217,uu____4218,uu____4219,uu____4220,r)
                       ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, us, t, [FStar_Syntax_Syntax.Assumption], r) in
                       ((dec :: out), (l :: hidden))
                   | uu____4230 -> (out, hidden)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume
          (uu____4242,uu____4243,quals,uu____4245) ->
          let uu____4248 = is_abstract quals in
          if uu____4248 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____4265 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4265
          then
            ([FStar_Syntax_Syntax.Sig_declare_typ
                (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
              hidden))
          else
            (let uu____4275 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___80_4277  ->
                       match uu___80_4277 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____4280 -> false)) in
             if uu____4275 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4290 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____4302,uu____4303,quals,uu____4305) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4323 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4323
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
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____4347) ->
          let uu____4354 = is_abstract quals in
          if uu____4354
          then
            let uu____4359 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu____4365 =
                        let uu____4372 =
                          let uu____4373 =
                            let uu____4378 =
                              FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                            uu____4378.FStar_Syntax_Syntax.fv_name in
                          uu____4373.FStar_Syntax_Syntax.v in
                        (uu____4372, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp),
                          (FStar_Syntax_Syntax.Assumption :: quals), r) in
                      FStar_Syntax_Syntax.Sig_declare_typ uu____4365)) in
            (uu____4359, hidden)
          else ([se], hidden)
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4426 se =
        match uu____4426 with
        | (ses,exports,env,hidden) ->
            ((let uu____4456 =
                FStar_TypeChecker_Env.debug env FStar_Options.Low in
              if uu____4456
              then
                let uu____4457 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4457
              else ());
             (let uu____4459 = tc_decl env se in
              match uu____4459 with
              | (ses',env,ses_elaborated) ->
                  ((let uu____4483 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4483
                    then
                      let uu____4484 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se  ->
                               let uu____4487 =
                                 let uu____4488 =
                                   FStar_Syntax_Print.sigelt_to_string se in
                                 Prims.strcat uu____4488 "\n" in
                               Prims.strcat s uu____4487) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4484
                    else ());
                   FStar_List.iter
                     (fun se  ->
                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env se) ses';
                   (let uu____4492 =
                      let accum_exports_hidden uu____4510 se =
                        match uu____4510 with
                        | (exports,hidden) ->
                            let uu____4526 = for_export hidden se in
                            (match uu____4526 with
                             | (se_exported,hidden) ->
                                 ((FStar_List.rev_append se_exported exports),
                                   hidden)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____4492 with
                    | (exports,hidden) ->
                        (((FStar_List.rev_append ses' ses), exports, env,
                           hidden), ses_elaborated))))) in
      let uu____4576 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4576 with
      | (ses,exports,env,uu____4602) ->
          ((FStar_List.rev_append ses []),
            (FStar_List.rev_append exports []), env)
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
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____4627 = FStar_Options.debug_any () in
       if uu____4627
       then
         FStar_Util.print3 "%s %s of %s\n" action label
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
       let msg = Prims.strcat "Internals for " name in
       let env =
         let uu___99_4633 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___99_4633.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___99_4633.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___99_4633.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___99_4633.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___99_4633.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___99_4633.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___99_4633.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___99_4633.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___99_4633.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___99_4633.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___99_4633.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___99_4633.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___99_4633.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___99_4633.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___99_4633.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___99_4633.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___99_4633.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___99_4633.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___99_4633.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___99_4633.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___99_4633.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___99_4633.FStar_TypeChecker_Env.qname_and_index)
         } in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env =
          FStar_TypeChecker_Env.set_current_module env
            modul.FStar_Syntax_Syntax.name in
        let uu____4636 = tc_decls env modul.FStar_Syntax_Syntax.declarations in
        match uu____4636 with
        | (ses,exports,env) ->
            ((let uu___100_4654 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___100_4654.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___100_4654.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___100_4654.FStar_Syntax_Syntax.is_interface)
              }), exports, env)))
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
        let uu____4670 = tc_decls env decls in
        match uu____4670 with
        | (ses,exports,env) ->
            let modul =
              let uu___101_4688 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___101_4688.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___101_4688.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___101_4688.FStar_Syntax_Syntax.is_interface)
              } in
            (modul, exports, env)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env =
          let uu___102_4702 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___102_4702.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___102_4702.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___102_4702.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___102_4702.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___102_4702.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___102_4702.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___102_4702.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___102_4702.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___102_4702.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___102_4702.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___102_4702.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___102_4702.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___102_4702.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___102_4702.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___102_4702.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___102_4702.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___102_4702.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___102_4702.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___102_4702.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___102_4702.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___102_4702.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs t =
          let uu____4713 = FStar_Syntax_Subst.open_univ_vars univs t in
          match uu____4713 with
          | (univs,t) ->
              ((let uu____4719 =
                  let uu____4720 =
                    let uu____4723 =
                      FStar_TypeChecker_Env.set_current_module env
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4723 in
                  FStar_All.pipe_left uu____4720
                    (FStar_Options.Other "Exports") in
                if uu____4719
                then
                  let uu____4724 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____4725 =
                    let uu____4726 =
                      FStar_All.pipe_right univs
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____4726
                      (FStar_String.concat ", ") in
                  let uu____4731 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4724 uu____4725 uu____4731
                else ());
               (let env = FStar_TypeChecker_Env.push_univ_vars env univs in
                let uu____4734 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env t in
                FStar_All.pipe_right uu____4734 Prims.ignore)) in
        let check_term lid univs t =
          (let uu____4752 =
             let uu____4753 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____4754 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4753 uu____4754 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4752);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt uu___81_4759 =
          match uu___81_4759 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4762,uu____4763)
              ->
              let uu____4770 =
                let uu____4771 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4771 in
              if uu____4770
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs,binders,typ,uu____4779,uu____4780,uu____4781,r) ->
              let t =
                let uu____4792 =
                  let uu____4795 =
                    let uu____4796 =
                      let uu____4804 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____4804) in
                    FStar_Syntax_Syntax.Tm_arrow uu____4796 in
                  FStar_Syntax_Syntax.mk uu____4795 in
                uu____4792 None r in
              check_term l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs,t,uu____4816,uu____4817,uu____4818,uu____4819,uu____4820)
              -> check_term l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs,t,quals,uu____4829)
              ->
              let uu____4832 =
                let uu____4833 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4833 in
              if uu____4832 then check_term l univs t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4836,lbs),uu____4838,uu____4839,quals,uu____4841) ->
              let uu____4853 =
                let uu____4854 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4854 in
              if uu____4853
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs,binders,comp,quals,flags,r) ->
              let uu____4875 =
                let uu____4876 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4876 in
              if uu____4875
              then
                let arrow =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None r in
                check_term l univs arrow
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
        let modul =
          let uu___103_4909 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___103_4909.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___103_4909.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env = FStar_TypeChecker_Env.finish_module env modul in
        (let uu____4912 =
           let uu____4913 = FStar_Options.lax () in
           Prims.op_Negation uu____4913 in
         if uu____4912 then check_exports env modul exports else ());
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env modul;
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____4919 =
           let uu____4920 = FStar_Options.interactive () in
           Prims.op_Negation uu____4920 in
         if uu____4919
         then
           let uu____4921 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____4921 Prims.ignore
         else ());
        (modul, env)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____4931 = tc_partial_modul env modul in
      match uu____4931 with
      | (modul,non_private_decls,env) ->
          finish_partial_modul env modul non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____4952 = FStar_Options.debug_any () in
       if uu____4952
       then
         let uu____4953 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____4953
       else ());
      (let env =
         let uu___104_4957 = env in
         let uu____4958 =
           let uu____4959 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____4959 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___104_4957.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___104_4957.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___104_4957.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___104_4957.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___104_4957.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___104_4957.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___104_4957.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___104_4957.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___104_4957.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___104_4957.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___104_4957.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___104_4957.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___104_4957.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___104_4957.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___104_4957.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___104_4957.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___104_4957.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___104_4957.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____4958;
           FStar_TypeChecker_Env.lax_universes =
             (uu___104_4957.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___104_4957.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___104_4957.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___104_4957.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___104_4957.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____4960 = tc_modul env m in
       match uu____4960 with
       | (m,env) ->
           ((let uu____4968 =
               FStar_Options.dump_module
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____4968
             then
               let uu____4969 = FStar_Syntax_Print.modul_to_string m in
               FStar_Util.print1 "%s\n" uu____4969
             else ());
            (let uu____4972 =
               (FStar_Options.dump_module
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____4972
             then
               let normalize_toplevel_lets uu___82_4976 =
                 match uu___82_4976 with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),r,ids,qs,attrs) ->
                     let n =
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
                       let uu____5003 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5003 with
                       | (univnames,e) ->
                           let uu___105_5008 = lb in
                           let uu____5009 =
                             let uu____5012 =
                               FStar_TypeChecker_Env.push_univ_vars env
                                 univnames in
                             n uu____5012 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___105_5008.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___105_5008.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___105_5008.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___105_5008.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5009
                           } in
                     let uu____5013 =
                       let uu____5022 =
                         let uu____5026 = FStar_List.map update lbs in
                         (b, uu____5026) in
                       (uu____5022, r, ids, qs, attrs) in
                     FStar_Syntax_Syntax.Sig_let uu____5013
                 | se -> se in
               let normalized_module =
                 let uu___106_5037 = m in
                 let uu____5038 =
                   FStar_List.map normalize_toplevel_lets
                     m.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___106_5037.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5038;
                   FStar_Syntax_Syntax.exports =
                     (uu___106_5037.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___106_5037.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5039 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5039
             else ());
            (m, env)))