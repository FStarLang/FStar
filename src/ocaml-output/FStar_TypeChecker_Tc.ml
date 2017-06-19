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
          let uu___90_14 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___90_14.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___90_14.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___90_14.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___90_14.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___90_14.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___90_14.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___90_14.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___90_14.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___90_14.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___90_14.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___90_14.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___90_14.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___90_14.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___90_14.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___90_14.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___90_14.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___90_14.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___90_14.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___90_14.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___90_14.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___90_14.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___90_14.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___90_14.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___90_14.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___90_14.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___90_14.FStar_TypeChecker_Env.is_native_tactic)
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
          let uu___91_26 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___91_26.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___91_26.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___91_26.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___91_26.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___91_26.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___91_26.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___91_26.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___91_26.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___91_26.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___91_26.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___91_26.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___91_26.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___91_26.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___91_26.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___91_26.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___91_26.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___91_26.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___91_26.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___91_26.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___91_26.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___91_26.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___91_26.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___91_26.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___91_26.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___91_26.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___91_26.FStar_TypeChecker_Env.is_native_tactic)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____33 =
         let uu____34 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____34 in
       Prims.op_Negation uu____33)
let is_native_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____48) ->
            let uu____53 =
              let uu____54 = FStar_Syntax_Subst.compress h' in
              uu____54.FStar_Syntax_Syntax.n in
            (match uu____53 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.tactic_lid
                 -> env.FStar_TypeChecker_Env.is_native_tactic tac_lid
             | uu____58 -> false)
        | uu____59 -> false
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____72 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____72 with
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
        (let uu____97 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____97
         then
           let uu____98 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____98
         else ());
        (let uu____100 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____100 with
         | (t',uu____105,uu____106) ->
             ((let uu____108 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____108
               then
                 let uu____109 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____109
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
        let uu____123 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____123
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____149 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____149)
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
        let fail uu____174 =
          let uu____175 =
            let uu____176 =
              let uu____179 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____179, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____176 in
          raise uu____175 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____207)::(wp,uu____209)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____218 -> fail ())
        | uu____219 -> fail ()
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____281 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____281 with
      | (effect_params_un,signature_un,opening) ->
          let uu____288 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____288 with
           | (effect_params,env,uu____294) ->
               let uu____295 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____295 with
                | (signature,uu____299) ->
                    let ed1 =
                      let uu___92_301 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___92_301.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___92_301.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___92_301.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___92_301.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___92_301.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___92_301.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___92_301.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___92_301.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___92_301.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___92_301.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___92_301.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___92_301.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___92_301.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___92_301.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___92_301.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___92_301.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___92_301.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____305 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
                          let uu___93_323 = ed1 in
                          let uu____324 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____325 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____326 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____327 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____328 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____329 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____330 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____331 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____332 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____333 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____334 =
                            let uu____335 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____335 in
                          let uu____341 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____342 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____343 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___94_346 = a in
                                 let uu____347 =
                                   let uu____348 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____348 in
                                 let uu____354 =
                                   let uu____355 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____355 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___94_346.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___94_346.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___94_346.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___94_346.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____347;
                                   FStar_Syntax_Syntax.action_typ = uu____354
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___93_323.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___93_323.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___93_323.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___93_323.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___93_323.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____324;
                            FStar_Syntax_Syntax.bind_wp = uu____325;
                            FStar_Syntax_Syntax.if_then_else = uu____326;
                            FStar_Syntax_Syntax.ite_wp = uu____327;
                            FStar_Syntax_Syntax.stronger = uu____328;
                            FStar_Syntax_Syntax.close_wp = uu____329;
                            FStar_Syntax_Syntax.assert_p = uu____330;
                            FStar_Syntax_Syntax.assume_p = uu____331;
                            FStar_Syntax_Syntax.null_wp = uu____332;
                            FStar_Syntax_Syntax.trivial = uu____333;
                            FStar_Syntax_Syntax.repr = uu____334;
                            FStar_Syntax_Syntax.return_repr = uu____341;
                            FStar_Syntax_Syntax.bind_repr = uu____342;
                            FStar_Syntax_Syntax.actions = uu____343
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____383 =
                          let uu____384 =
                            let uu____387 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____387, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____384 in
                        raise uu____383 in
                      let uu____392 =
                        let uu____393 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____393.FStar_Syntax_Syntax.n in
                      match uu____392 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____418)::(wp,uu____420)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____429 -> fail signature1)
                      | uu____430 -> fail signature1 in
                    let uu____431 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____431 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____449 =
                           let uu____450 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____450 with
                           | (signature1,uu____458) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____460 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____460 in
                         ((let uu____462 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____462
                           then
                             let uu____463 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____464 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____465 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____466 =
                               let uu____467 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____467 in
                             let uu____468 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____463 uu____464 uu____465 uu____466
                               uu____468
                           else ());
                          (let check_and_gen' env2 uu____481 k =
                             match uu____481 with
                             | (uu____486,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____494 =
                                 let uu____498 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____499 =
                                   let uu____501 =
                                     let uu____502 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____502 in
                                   [uu____501] in
                                 uu____498 :: uu____499 in
                               let uu____503 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____494 uu____503 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____507 = fresh_effect_signature () in
                             match uu____507 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____521 =
                                     let uu____525 =
                                       let uu____526 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____526 in
                                     [uu____525] in
                                   let uu____527 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____521
                                     uu____527 in
                                 let expected_k =
                                   let uu____533 =
                                     let uu____537 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____538 =
                                       let uu____540 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____541 =
                                         let uu____543 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____544 =
                                           let uu____546 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____547 =
                                             let uu____549 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____549] in
                                           uu____546 :: uu____547 in
                                         uu____543 :: uu____544 in
                                       uu____540 :: uu____541 in
                                     uu____537 :: uu____538 in
                                   let uu____550 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____533
                                     uu____550 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____555 =
                                 let uu____556 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____556
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____555 in
                             let expected_k =
                               let uu____564 =
                                 let uu____568 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____569 =
                                   let uu____571 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____572 =
                                     let uu____574 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____575 =
                                       let uu____577 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____577] in
                                     uu____574 :: uu____575 in
                                   uu____571 :: uu____572 in
                                 uu____568 :: uu____569 in
                               let uu____578 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____564 uu____578 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____585 =
                                 let uu____589 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____590 =
                                   let uu____592 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____592] in
                                 uu____589 :: uu____590 in
                               let uu____593 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____585 uu____593 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____597 = FStar_Syntax_Util.type_u () in
                             match uu____597 with
                             | (t,uu____601) ->
                                 let expected_k =
                                   let uu____605 =
                                     let uu____609 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____610 =
                                       let uu____612 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____613 =
                                         let uu____615 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____615] in
                                       uu____612 :: uu____613 in
                                     uu____609 :: uu____610 in
                                   let uu____616 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____605
                                     uu____616 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____621 =
                                 let uu____622 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____622
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____621 in
                             let b_wp_a =
                               let uu____630 =
                                 let uu____634 =
                                   let uu____635 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____635 in
                                 [uu____634] in
                               let uu____636 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____630 uu____636 in
                             let expected_k =
                               let uu____642 =
                                 let uu____646 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____647 =
                                   let uu____649 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____650 =
                                     let uu____652 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____652] in
                                   uu____649 :: uu____650 in
                                 uu____646 :: uu____647 in
                               let uu____653 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____642 uu____653 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____660 =
                                 let uu____664 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____665 =
                                   let uu____667 =
                                     let uu____668 =
                                       let uu____669 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____669
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____668 in
                                   let uu____674 =
                                     let uu____676 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____676] in
                                   uu____667 :: uu____674 in
                                 uu____664 :: uu____665 in
                               let uu____677 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____660 uu____677 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____684 =
                                 let uu____688 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____689 =
                                   let uu____691 =
                                     let uu____692 =
                                       let uu____693 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____693
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____692 in
                                   let uu____698 =
                                     let uu____700 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____700] in
                                   uu____691 :: uu____698 in
                                 uu____688 :: uu____689 in
                               let uu____701 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____684 uu____701 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____708 =
                                 let uu____712 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____712] in
                               let uu____713 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____708 uu____713 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____717 = FStar_Syntax_Util.type_u () in
                             match uu____717 with
                             | (t,uu____721) ->
                                 let expected_k =
                                   let uu____725 =
                                     let uu____729 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____730 =
                                       let uu____732 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____732] in
                                     uu____729 :: uu____730 in
                                   let uu____733 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____725
                                     uu____733 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____736 =
                             let uu____742 =
                               let uu____743 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____743.FStar_Syntax_Syntax.n in
                             match uu____742 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____752 ->
                                 let repr =
                                   let uu____754 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____754 with
                                   | (t,uu____758) ->
                                       let expected_k =
                                         let uu____762 =
                                           let uu____766 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____767 =
                                             let uu____769 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____769] in
                                           uu____766 :: uu____767 in
                                         let uu____770 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____762
                                           uu____770 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____783 =
                                     let uu____786 =
                                       let uu____787 =
                                         let uu____797 =
                                           let uu____799 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____800 =
                                             let uu____802 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____802] in
                                           uu____799 :: uu____800 in
                                         (repr1, uu____797) in
                                       FStar_Syntax_Syntax.Tm_app uu____787 in
                                     FStar_Syntax_Syntax.mk uu____786 in
                                   uu____783 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____821 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____821 wp in
                                 let destruct_repr t =
                                   let uu____832 =
                                     let uu____833 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____833.FStar_Syntax_Syntax.n in
                                   match uu____832 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____842,(t1,uu____844)::(wp,uu____846)::[])
                                       -> (t1, wp)
                                   | uu____880 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____889 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____889
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____890 = fresh_effect_signature () in
                                   match uu____890 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____904 =
                                           let uu____908 =
                                             let uu____909 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____909 in
                                           [uu____908] in
                                         let uu____910 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____904
                                           uu____910 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____916 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____916 in
                                       let wp_g_x =
                                         let uu____920 =
                                           let uu____921 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____922 =
                                             let uu____923 =
                                               let uu____924 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____924 in
                                             [uu____923] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____921 uu____922 in
                                         uu____920 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____935 =
                                             let uu____936 =
                                               let uu____937 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____937
                                                 FStar_Pervasives.snd in
                                             let uu____942 =
                                               let uu____943 =
                                                 let uu____945 =
                                                   let uu____947 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____948 =
                                                     let uu____950 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____951 =
                                                       let uu____953 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____954 =
                                                         let uu____956 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____956] in
                                                       uu____953 :: uu____954 in
                                                     uu____950 :: uu____951 in
                                                   uu____947 :: uu____948 in
                                                 r :: uu____945 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____943 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____936 uu____942 in
                                           uu____935 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____964 =
                                           let uu____968 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____969 =
                                             let uu____971 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____972 =
                                               let uu____974 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____975 =
                                                 let uu____977 =
                                                   let uu____978 =
                                                     let uu____979 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____979 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____978 in
                                                 let uu____980 =
                                                   let uu____982 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____983 =
                                                     let uu____985 =
                                                       let uu____986 =
                                                         let uu____987 =
                                                           let uu____991 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____991] in
                                                         let uu____992 =
                                                           let uu____995 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____995 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____987
                                                           uu____992 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____986 in
                                                     [uu____985] in
                                                   uu____982 :: uu____983 in
                                                 uu____977 :: uu____980 in
                                               uu____974 :: uu____975 in
                                             uu____971 :: uu____972 in
                                           uu____968 :: uu____969 in
                                         let uu____996 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____964
                                           uu____996 in
                                       let uu____999 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____999 with
                                        | (expected_k1,uu____1004,uu____1005)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___95_1009 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___95_1009.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___95_1009.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___95_1009.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___95_1009.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___95_1009.FStar_TypeChecker_Env.is_native_tactic)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1016 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____1016 in
                                   let res =
                                     let wp =
                                       let uu____1023 =
                                         let uu____1024 =
                                           let uu____1025 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1025
                                             FStar_Pervasives.snd in
                                         let uu____1030 =
                                           let uu____1031 =
                                             let uu____1033 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1034 =
                                               let uu____1036 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1036] in
                                             uu____1033 :: uu____1034 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1031 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1024 uu____1030 in
                                       uu____1023 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1044 =
                                       let uu____1048 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1049 =
                                         let uu____1051 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1051] in
                                       uu____1048 :: uu____1049 in
                                     let uu____1052 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1044
                                       uu____1052 in
                                   let uu____1055 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1055 with
                                   | (expected_k1,uu____1063,uu____1064) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1067 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1067 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1079 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1099 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1099 with
                                     | (act_typ,uu____1104,g_t) ->
                                         let env' =
                                           let uu___96_1107 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___96_1107.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___96_1107.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___96_1107.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___96_1107.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___96_1107.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___96_1107.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___96_1107.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___96_1107.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___96_1107.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___96_1107.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___96_1107.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___96_1107.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___96_1107.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___96_1107.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___96_1107.FStar_TypeChecker_Env.is_native_tactic)
                                           } in
                                         ((let uu____1109 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1109
                                           then
                                             let uu____1110 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1111 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1110 uu____1111
                                           else ());
                                          (let uu____1113 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1113 with
                                           | (act_defn,uu____1118,g_a) ->
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
                                               let uu____1122 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1140 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1140 with
                                                      | (bs1,uu____1146) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1153 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1153 in
                                                          let uu____1156 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1156
                                                           with
                                                           | (k1,uu____1163,g)
                                                               -> (k1, g)))
                                                 | uu____1165 ->
                                                     let uu____1166 =
                                                       let uu____1167 =
                                                         let uu____1170 =
                                                           let uu____1171 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1172 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1171
                                                             uu____1172 in
                                                         (uu____1170,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1167 in
                                                     raise uu____1166 in
                                               (match uu____1122 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1179 =
                                                        let uu____1180 =
                                                          let uu____1181 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1181 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1180 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1179);
                                                     (let act_typ2 =
                                                        let uu____1185 =
                                                          let uu____1186 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1186.FStar_Syntax_Syntax.n in
                                                        match uu____1185 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1203 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1203
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1210
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1210
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1230
                                                                    =
                                                                    let uu____1231
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1231] in
                                                                    let uu____1232
                                                                    =
                                                                    let uu____1238
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1238] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1230;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1232;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1239
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1239))
                                                        | uu____1242 ->
                                                            failwith "" in
                                                      let uu____1245 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1245 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___97_1251 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___97_1251.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___97_1251.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___97_1251.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____736 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1267 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1267 in
                               let uu____1270 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1270 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1276 =
                                        let uu____1279 =
                                          let uu____1280 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1280.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1279) in
                                      match uu____1276 with
                                      | ([],uu____1283) -> t1
                                      | (uu____1289,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1290,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1302 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1313 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1313 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1319 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1320 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1320))
                                           && (m <> n1) in
                                       if uu____1319
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1334 =
                                           let uu____1335 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1336 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1335 uu____1336 in
                                         failwith uu____1334
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1342 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1342 with
                                      | (univs2,defn) ->
                                          let uu____1347 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1347 with
                                           | (univs',typ) ->
                                               let uu___98_1353 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___98_1353.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___98_1353.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___98_1353.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___99_1356 = ed2 in
                                      let uu____1357 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1358 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1359 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1360 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1361 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1362 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1363 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1364 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1365 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1366 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1367 =
                                        let uu____1368 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1368 in
                                      let uu____1374 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1375 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1376 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___99_1356.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___99_1356.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1357;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1358;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1359;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1360;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1361;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1362;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1363;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1364;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1365;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1366;
                                        FStar_Syntax_Syntax.repr = uu____1367;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1374;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1375;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1376
                                      } in
                                    ((let uu____1379 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1379
                                      then
                                        let uu____1380 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1380
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
      let uu____1384 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1384 with
      | (effect_binders_un,signature_un) ->
          let uu____1394 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1394 with
           | (effect_binders,env1,uu____1405) ->
               let uu____1406 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1406 with
                | (signature,uu____1415) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1424  ->
                           match uu____1424 with
                           | (bv,qual) ->
                               let uu____1431 =
                                 let uu___100_1432 = bv in
                                 let uu____1433 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___100_1432.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___100_1432.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1433
                                 } in
                               (uu____1431, qual)) effect_binders in
                    let uu____1436 =
                      let uu____1441 =
                        let uu____1442 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1442.FStar_Syntax_Syntax.n in
                      match uu____1441 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1450)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1465 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1436 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1482 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1482
                           then
                             let uu____1483 =
                               let uu____1485 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1485 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1483
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1509 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1509 with
                           | (t2,comp,uu____1517) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1528 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1528 with
                          | (repr,_comp) ->
                              ((let uu____1541 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1541
                                then
                                  let uu____1542 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1542
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
                                  let uu____1548 =
                                    let uu____1549 =
                                      let uu____1550 =
                                        let uu____1560 =
                                          let uu____1564 =
                                            let uu____1567 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1568 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1567, uu____1568) in
                                          [uu____1564] in
                                        (wp_type1, uu____1560) in
                                      FStar_Syntax_Syntax.Tm_app uu____1550 in
                                    mk1 uu____1549 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1548 in
                                let effect_signature =
                                  let binders =
                                    let uu____1583 =
                                      let uu____1586 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1586) in
                                    let uu____1587 =
                                      let uu____1591 =
                                        let uu____1592 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1592
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1591] in
                                    uu____1583 :: uu____1587 in
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
                                  let uu____1635 = item in
                                  match uu____1635 with
                                  | (u_item,item1) ->
                                      let uu____1647 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1647 with
                                       | (item2,item_comp) ->
                                           ((let uu____1657 =
                                               let uu____1658 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1658 in
                                             if uu____1657
                                             then
                                               let uu____1659 =
                                                 let uu____1660 =
                                                   let uu____1661 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1662 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1661 uu____1662 in
                                                 FStar_Errors.Err uu____1660 in
                                               raise uu____1659
                                             else ());
                                            (let uu____1664 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1664 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1677 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1677 with
                                | (dmff_env1,uu____1690,bind_wp,bind_elab) ->
                                    let uu____1693 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1693 with
                                     | (dmff_env2,uu____1706,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1710 =
                                             let uu____1711 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1711.FStar_Syntax_Syntax.n in
                                           match uu____1710 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1749 =
                                                 let uu____1757 =
                                                   let uu____1760 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1760 in
                                                 match uu____1757 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1799 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1749 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1821 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1821 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1832 =
                                                          let uu____1833 =
                                                            let uu____1843 =
                                                              let uu____1847
                                                                =
                                                                let uu____1850
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1851
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1850,
                                                                  uu____1851) in
                                                              [uu____1847] in
                                                            (wp_type1,
                                                              uu____1843) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1833 in
                                                        mk1 uu____1832 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1859 =
                                                      let uu____1869 =
                                                        let uu____1870 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1870 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1869 in
                                                    (match uu____1859 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1898
                                                           =
                                                           let error_msg =
                                                             let uu____1900 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1901 =
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
                                                                   (lid,uu____1917))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1900
                                                               uu____1901 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1943
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1943
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
                                                               (lid,uu____1949))
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
                                                             let uu____1969 =
                                                               let uu____1970
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1971
                                                                 =
                                                                 let uu____1972
                                                                   =
                                                                   let uu____1976
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1976,
                                                                    None) in
                                                                 [uu____1972] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1970
                                                                 uu____1971 in
                                                             uu____1969 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1992 =
                                                             let uu____1993 =
                                                               let uu____1997
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1997] in
                                                             b11 ::
                                                               uu____1993 in
                                                           let uu____2000 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1992
                                                             uu____2000
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____2010 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2012 =
                                             let uu____2013 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2013.FStar_Syntax_Syntax.n in
                                           match uu____2012 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2051 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2051
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2067 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2069 =
                                             let uu____2070 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2070.FStar_Syntax_Syntax.n in
                                           match uu____2069 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2099 =
                                                 let uu____2100 =
                                                   let uu____2102 =
                                                     let uu____2103 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2103 in
                                                   [uu____2102] in
                                                 FStar_List.append uu____2100
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2099 body what
                                           | uu____2104 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2124 =
                                                let uu____2125 =
                                                  let uu____2126 =
                                                    let uu____2136 =
                                                      let uu____2137 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2137 in
                                                    (t, uu____2136) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2126 in
                                                mk1 uu____2125 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2124) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2160 = f a2 in
                                               [uu____2160]
                                           | x::xs ->
                                               let uu____2164 =
                                                 apply_last1 f xs in
                                               x :: uu____2164 in
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
                                           let uu____2179 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2179 with
                                           | Some (_us,_t) ->
                                               ((let uu____2196 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2196
                                                 then
                                                   let uu____2197 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2197
                                                 else ());
                                                (let uu____2199 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2199))
                                           | None  ->
                                               let uu____2204 =
                                                 let uu____2207 = mk_lid name in
                                                 let uu____2208 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2207 uu____2208 in
                                               (match uu____2204 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2217 =
                                                        let uu____2219 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2219 in
                                                      FStar_ST.write sigelts
                                                        uu____2217);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2230 =
                                             let uu____2232 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2233 =
                                               FStar_ST.read sigelts in
                                             uu____2232 :: uu____2233 in
                                           FStar_ST.write sigelts uu____2230);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2243 =
                                              let uu____2245 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2246 =
                                                FStar_ST.read sigelts in
                                              uu____2245 :: uu____2246 in
                                            FStar_ST.write sigelts uu____2243);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2256 =
                                               let uu____2258 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2259 =
                                                 FStar_ST.read sigelts in
                                               uu____2258 :: uu____2259 in
                                             FStar_ST.write sigelts
                                               uu____2256);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2269 =
                                                let uu____2271 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2272 =
                                                  FStar_ST.read sigelts in
                                                uu____2271 :: uu____2272 in
                                              FStar_ST.write sigelts
                                                uu____2269);
                                             (let uu____2280 =
                                                FStar_List.fold_left
                                                  (fun uu____2287  ->
                                                     fun action  ->
                                                       match uu____2287 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2300 =
                                                             let uu____2304 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2304
                                                               params_un in
                                                           (match uu____2300
                                                            with
                                                            | (action_params,env',uu____2310)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2319
                                                                     ->
                                                                    match uu____2319
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2326
                                                                    =
                                                                    let uu___101_2327
                                                                    = bv in
                                                                    let uu____2328
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___101_2327.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___101_2327.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2328
                                                                    } in
                                                                    (uu____2326,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2332
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2332
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
                                                                    uu____2358
                                                                    ->
                                                                    let uu____2359
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2359 in
                                                                    ((
                                                                    let uu____2363
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2363
                                                                    then
                                                                    let uu____2364
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2365
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2366
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2367
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2364
                                                                    uu____2365
                                                                    uu____2366
                                                                    uu____2367
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
                                                                    let uu____2371
                                                                    =
                                                                    let uu____2373
                                                                    =
                                                                    let uu___102_2374
                                                                    = action in
                                                                    let uu____2375
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2376
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___102_2374.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___102_2374.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___102_2374.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2375;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2376
                                                                    } in
                                                                    uu____2373
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2371))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2280 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2396 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2397 =
                                                        let uu____2399 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2399] in
                                                      uu____2396 ::
                                                        uu____2397 in
                                                    let uu____2400 =
                                                      let uu____2401 =
                                                        let uu____2402 =
                                                          let uu____2403 =
                                                            let uu____2413 =
                                                              let uu____2417
                                                                =
                                                                let uu____2420
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2421
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2420,
                                                                  uu____2421) in
                                                              [uu____2417] in
                                                            (repr,
                                                              uu____2413) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2403 in
                                                        mk1 uu____2402 in
                                                      let uu____2429 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2401
                                                        uu____2429 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2400 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2437 =
                                                    let uu____2442 =
                                                      let uu____2443 =
                                                        let uu____2446 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2446 in
                                                      uu____2443.FStar_Syntax_Syntax.n in
                                                    match uu____2442 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2454)
                                                        ->
                                                        let uu____2481 =
                                                          let uu____2490 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2490
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2521 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2481
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2549 =
                                                               let uu____2550
                                                                 =
                                                                 let uu____2553
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2553 in
                                                               uu____2550.FStar_Syntax_Syntax.n in
                                                             (match uu____2549
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2570
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2570
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2579
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2590
                                                                     ->
                                                                    match uu____2590
                                                                    with
                                                                    | 
                                                                    (bv,uu____2594)
                                                                    ->
                                                                    let uu____2595
                                                                    =
                                                                    let uu____2596
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2596
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2595
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2579
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
                                                                    uu____2629
                                                                    ->
                                                                    let uu____2633
                                                                    =
                                                                    let uu____2634
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2634 in
                                                                    failwith
                                                                    uu____2633 in
                                                                    let uu____2637
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2640
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2637,
                                                                    uu____2640)))
                                                              | uu____2650 ->
                                                                  let uu____2651
                                                                    =
                                                                    let uu____2652
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2652 in
                                                                  failwith
                                                                    uu____2651))
                                                    | uu____2657 ->
                                                        let uu____2658 =
                                                          let uu____2659 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2659 in
                                                        failwith uu____2658 in
                                                  (match uu____2437 with
                                                   | (pre,post) ->
                                                       ((let uu____2676 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2678 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2680 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___103_2682
                                                             = ed in
                                                           let uu____2683 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2684 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2685 =
                                                             let uu____2686 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2686) in
                                                           let uu____2692 =
                                                             let uu____2693 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2693) in
                                                           let uu____2699 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2700 =
                                                             let uu____2701 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2701) in
                                                           let uu____2707 =
                                                             let uu____2708 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2708) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2683;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2684;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2685;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2692;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___103_2682.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2699;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2700;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2707;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2714 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2714
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2725
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2725
                                                               then
                                                                 let uu____2726
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2726
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
                                                                    let uu____2738
                                                                    =
                                                                    let uu____2740
                                                                    =
                                                                    let uu____2746
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2746) in
                                                                    Some
                                                                    uu____2740 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2738;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2757
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2757
                                                                 else None in
                                                               let uu____2759
                                                                 =
                                                                 let uu____2761
                                                                   =
                                                                   let uu____2763
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2763 in
                                                                 FStar_List.append
                                                                   uu____2761
                                                                   sigelts' in
                                                               (uu____2759,
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
                (lex_t1,[],[],t,uu____2786,uu____2787);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2789;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2793);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2795;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2799);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2801;_}::[]
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
                let uu____2840 =
                  let uu____2843 =
                    let uu____2844 =
                      let uu____2849 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2849, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2844 in
                  FStar_Syntax_Syntax.mk uu____2843 in
                uu____2840 None r1 in
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
                  let uu____2869 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2869 in
                let hd1 =
                  let uu____2875 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2875 in
                let tl1 =
                  let uu____2877 =
                    let uu____2878 =
                      let uu____2881 =
                        let uu____2882 =
                          let uu____2887 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2887, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2882 in
                      FStar_Syntax_Syntax.mk uu____2881 in
                    uu____2878 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2877 in
                let res =
                  let uu____2900 =
                    let uu____2903 =
                      let uu____2904 =
                        let uu____2909 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2909,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2904 in
                    FStar_Syntax_Syntax.mk uu____2903 in
                  uu____2900 None r2 in
                let uu____2919 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2919 in
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
              let uu____2941 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2941;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2944 ->
              let uu____2946 =
                let uu____2947 =
                  let uu____2948 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2948 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2947 in
              failwith uu____2946
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
            let uu____2958 = FStar_Syntax_Util.type_u () in
            match uu____2958 with
            | (k,uu____2962) ->
                let phi1 =
                  let uu____2964 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2964
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
          let uu____2974 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2974 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2993 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2993 FStar_List.flatten in
              ((let uu____3001 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____3001
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
                          let uu____3007 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____3013,uu____3014,uu____3015,uu____3016,uu____3017)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____3022 -> failwith "Impossible!" in
                          match uu____3007 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____3031 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____3035,uu____3036,uu____3037,uu____3038,uu____3039)
                        -> lid
                    | uu____3044 -> failwith "Impossible" in
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
                let uu____3050 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____3050
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
                   let uu____3068 =
                     let uu____3070 =
                       let uu____3071 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____3071;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____3070 :: ses1 in
                   (uu____3068, data_ops_ses))))
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3089 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3102 ->
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
           let uu____3132 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3132 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3157 = FStar_Options.set_options t s in
             match uu____3157 with
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
                ((let uu____3174 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3174 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3180 = cps_and_elaborate env1 ne in
           (match uu____3180 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___104_3201 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___104_3201.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___104_3201.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___104_3201.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___105_3202 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___105_3202.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_3202.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_3202.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___106_3208 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___106_3208.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___106_3208.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___106_3208.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3214 =
             let uu____3219 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3219 in
           (match uu____3214 with
            | (a,wp_a_src) ->
                let uu____3230 =
                  let uu____3235 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3235 in
                (match uu____3230 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3247 =
                         let uu____3249 =
                           let uu____3250 =
                             let uu____3255 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3255) in
                           FStar_Syntax_Syntax.NT uu____3250 in
                         [uu____3249] in
                       FStar_Syntax_Subst.subst uu____3247 wp_b_tgt in
                     let expected_k =
                       let uu____3259 =
                         let uu____3263 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3264 =
                           let uu____3266 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3266] in
                         uu____3263 :: uu____3264 in
                       let uu____3267 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3259 uu____3267 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3288 =
                           let uu____3289 =
                             let uu____3292 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3293 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3292, uu____3293) in
                           FStar_Errors.Error uu____3289 in
                         raise uu____3288 in
                       let uu____3296 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3296 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3315 =
                             let uu____3316 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3316 in
                           if uu____3315
                           then no_reify eff_name
                           else
                             (let uu____3321 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3322 =
                                let uu____3325 =
                                  let uu____3326 =
                                    let uu____3336 =
                                      let uu____3338 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3339 =
                                        let uu____3341 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3341] in
                                      uu____3338 :: uu____3339 in
                                    (repr, uu____3336) in
                                  FStar_Syntax_Syntax.Tm_app uu____3326 in
                                FStar_Syntax_Syntax.mk uu____3325 in
                              uu____3322 None uu____3321) in
                     let uu____3351 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3366,lift_wp)) ->
                           let uu____3379 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3379)
                       | (Some (what,lift),None ) ->
                           ((let uu____3394 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3394
                             then
                               let uu____3395 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3395
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3398 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3398 with
                             | (lift1,comp,uu____3407) ->
                                 let uu____3408 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3408 with
                                  | (uu____3415,lift_wp,lift_elab) ->
                                      let uu____3418 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3419 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3351 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___107_3442 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___107_3442.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___107_3442.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___107_3442.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___107_3442.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___107_3442.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___107_3442.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___107_3442.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___107_3442.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___107_3442.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___107_3442.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___107_3442.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___107_3442.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___107_3442.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___107_3442.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___107_3442.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___107_3442.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___107_3442.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___107_3442.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___107_3442.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___107_3442.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___107_3442.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___107_3442.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___107_3442.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___107_3442.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___107_3442.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___107_3442.FStar_TypeChecker_Env.is_native_tactic)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3446,lift1) ->
                                let uu____3453 =
                                  let uu____3458 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3458 in
                                (match uu____3453 with
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
                                         let uu____3480 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3481 =
                                           let uu____3484 =
                                             let uu____3485 =
                                               let uu____3495 =
                                                 let uu____3497 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3498 =
                                                   let uu____3500 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3500] in
                                                 uu____3497 :: uu____3498 in
                                               (lift_wp1, uu____3495) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3485 in
                                           FStar_Syntax_Syntax.mk uu____3484 in
                                         uu____3481 None uu____3480 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3513 =
                                         let uu____3517 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3518 =
                                           let uu____3520 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3521 =
                                             let uu____3523 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3523] in
                                           uu____3520 :: uu____3521 in
                                         uu____3517 :: uu____3518 in
                                       let uu____3524 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3513
                                         uu____3524 in
                                     let uu____3527 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3527 with
                                      | (expected_k2,uu____3533,uu____3534)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___108_3537 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___108_3537.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___108_3537.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___109_3539 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___109_3539.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___109_3539.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___109_3539.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3552 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3552 with
            | (tps1,c1) ->
                let uu____3561 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3561 with
                 | (tps2,env3,us) ->
                     let uu____3572 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3572 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3586 =
                              let uu____3587 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3587 in
                            match uu____3586 with
                            | (uvs1,t) ->
                                let uu____3600 =
                                  let uu____3608 =
                                    let uu____3611 =
                                      let uu____3612 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3612.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3611) in
                                  match uu____3608 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3622,c4)) -> ([], c4)
                                  | (uu____3646,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3664 -> failwith "Impossible" in
                                (match uu____3600 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3695 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3695 with
                                         | (uu____3698,t1) ->
                                             let uu____3700 =
                                               let uu____3701 =
                                                 let uu____3704 =
                                                   let uu____3705 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3706 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3711 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3705 uu____3706
                                                     uu____3711 in
                                                 (uu____3704, r) in
                                               FStar_Errors.Error uu____3701 in
                                             raise uu____3700)
                                      else ();
                                      (let se1 =
                                         let uu___110_3714 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___110_3714.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___110_3714.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___110_3714.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3724,uu____3725,uu____3726) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___84_3728  ->
                   match uu___84_3728 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3729 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3732,uu____3733,uu____3734) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___84_3740  ->
                   match uu___84_3740 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3741 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3748 =
             if uvs = []
             then
               let uu____3749 =
                 let uu____3750 = FStar_Syntax_Util.type_u () in
                 fst uu____3750 in
               check_and_gen env2 t uu____3749
             else
               (let uu____3754 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3754 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3760 =
                        let uu____3761 = FStar_Syntax_Util.type_u () in
                        fst uu____3761 in
                      tc_check_trivial_guard env2 t1 uu____3760 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3765 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3765)) in
           (match uu____3748 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___111_3775 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___111_3775.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___111_3775.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___111_3775.FStar_Syntax_Syntax.sigmeta)
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
           let uu____3787 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3787 with
            | (e1,c,g1) ->
                let uu____3798 =
                  let uu____3802 =
                    let uu____3804 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3804 in
                  let uu____3805 =
                    let uu____3808 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3808) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3802 uu____3805 in
                (match uu____3798 with
                 | (e2,uu____3818,g) ->
                     ((let uu____3821 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3821);
                      (let se1 =
                         let uu___112_3823 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___112_3823.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___112_3823.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___112_3823.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3859 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3859
                 then Some q
                 else
                   (let uu____3872 =
                      let uu____3873 =
                        let uu____3876 =
                          let uu____3877 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3878 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3879 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3877 uu____3878 uu____3879 in
                        (uu____3876, r) in
                      FStar_Errors.Error uu____3873 in
                    raise uu____3872) in
           let uu____3882 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3903  ->
                     fun lb  ->
                       match uu____3903 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3927 =
                             let uu____3933 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3933 with
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
                                   | uu____3985 ->
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
                                  (let uu____3997 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3997, quals_opt1))) in
                           (match uu____3927 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3882 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____4050 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___85_4052  ->
                                match uu___85_4052 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____4053 -> false)) in
                      if uu____4050
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____4061 =
                    let uu____4064 =
                      let uu____4065 =
                        let uu____4073 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____4073) in
                      FStar_Syntax_Syntax.Tm_let uu____4065 in
                    FStar_Syntax_Syntax.mk uu____4064 in
                  uu____4061 None r in
                let uu____4095 =
                  let uu____4101 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___113_4105 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___113_4105.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___113_4105.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___113_4105.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___113_4105.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___113_4105.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___113_4105.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___113_4105.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___113_4105.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___113_4105.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___113_4105.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___113_4105.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___113_4105.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___113_4105.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___113_4105.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___113_4105.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___113_4105.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___113_4105.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___113_4105.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___113_4105.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___113_4105.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___113_4105.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___113_4105.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___113_4105.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___113_4105.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___113_4105.FStar_TypeChecker_Env.is_native_tactic)
                       }) e in
                  match uu____4101 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4113;
                       FStar_Syntax_Syntax.pos = uu____4114;
                       FStar_Syntax_Syntax.vars = uu____4115;_},uu____4116,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4135,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4140 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___86_4143  ->
                             match uu___86_4143 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4145 =
                                   let uu____4146 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4150 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4150)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4146 in
                                 if uu____4145
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___114_4159 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___114_4159.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___114_4159.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4165 -> failwith "impossible" in
                (match uu____4095 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4192 = log env2 in
                       if uu____4192
                       then
                         let uu____4193 =
                           let uu____4194 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4201 =
                                         let uu____4206 =
                                           let uu____4207 =
                                             let uu____4212 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4212.FStar_Syntax_Syntax.fv_name in
                                           uu____4207.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4206 in
                                       match uu____4201 with
                                       | None  -> true
                                       | uu____4219 -> false in
                                     if should_log
                                     then
                                       let uu____4224 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4225 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4224 uu____4225
                                     else "")) in
                           FStar_All.pipe_right uu____4194
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4193
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4249 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____4249 with
                              | (bs1,c1) ->
                                  let uu____4254 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____4254
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4264 =
                                            let uu____4265 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____4265.FStar_Syntax_Syntax.n in
                                          (match uu____4264 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4284 =
                                                 let uu____4285 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____4285.FStar_Syntax_Syntax.n in
                                               (match uu____4284 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4295 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4295 in
                                                    let uu____4296 =
                                                      let uu____4297 =
                                                        let uu____4298 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4298 args in
                                                      uu____4297 None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4296 u
                                                | uu____4303 -> c1)
                                           | uu____4304 -> c1)
                                      | uu____4305 -> c1 in
                                    let uu___115_4306 = t1 in
                                    let uu____4307 =
                                      let uu____4308 =
                                        let uu____4316 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4316) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4308 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4307;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___115_4306.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___115_4306.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___115_4306.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4338 =
                               let uu____4339 = FStar_Syntax_Subst.compress h in
                               uu____4339.FStar_Syntax_Syntax.n in
                             (match uu____4338 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4349 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4349 in
                                  let uu____4350 =
                                    let uu____4351 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4351
                                      args in
                                  uu____4350 None t1.FStar_Syntax_Syntax.pos
                              | uu____4356 -> t1)
                         | uu____4357 -> t1 in
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
                           let uu____4388 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4388 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4397 =
                                  FStar_Syntax_Syntax.bv_to_name (fst x) in
                                (uu____4397, (snd x))) bs in
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
                           let uu____4429 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4429 in
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
                         let uu___116_4460 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___117_4467 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___117_4467.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___117_4467.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___117_4467.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___117_4467.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids, attrs));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___116_4460.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___116_4460.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___116_4460.FStar_Syntax_Syntax.sigmeta)
                         } in
                       let tactic_decls =
                         match snd lbs1 with
                         | hd1::[] ->
                             let uu____4477 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4477 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4497 =
                                    let uu____4498 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4498.FStar_Syntax_Syntax.n in
                                  (match uu____4497 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4522 =
                                           let uu____4527 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4527.FStar_Syntax_Syntax.fv_name in
                                         uu____4522.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4532 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4532 in
                                       let uu____4533 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____4534 =
                                              let uu____4535 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4535 in
                                            Prims.op_Negation uu____4534) in
                                       if uu____4533
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl (fst lbs1)
                                             hd1 bs assm_lid comp in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4558 -> None))
                         | uu____4561 -> None in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4574 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4574
                             then
                               let uu____4575 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4576 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4575 uu____4576
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
             (fun uu___87_4609  ->
                match uu___87_4609 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4610 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4616) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4620 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4625 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4628 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4641 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4654) ->
          let uu____4659 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4659
          then
            let for_export_bundle se1 uu____4678 =
              match uu____4678 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4701,uu____4702) ->
                       let dec =
                         let uu___118_4708 = se1 in
                         let uu____4709 =
                           let uu____4710 =
                             let uu____4714 =
                               let uu____4717 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4717 in
                             (l, us, uu____4714) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4710 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4709;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___118_4708.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___118_4708.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4727,uu____4728,uu____4729) ->
                       let dec =
                         let uu___119_4733 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___119_4733.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___119_4733.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4736 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4748,uu____4749) ->
          let uu____4750 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4750 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4763 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4763
          then
            ([(let uu___120_4771 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___120_4771.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___120_4771.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4773 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___88_4775  ->
                       match uu___88_4775 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4776 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4779 -> true
                       | uu____4780 -> false)) in
             if uu____4773 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4790 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4793 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4796 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4799 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4802 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4812,uu____4813)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4829 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4829
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4850) ->
          let uu____4855 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4855
          then
            let uu____4860 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___121_4866 = se in
                      let uu____4867 =
                        let uu____4868 =
                          let uu____4872 =
                            let uu____4873 =
                              let uu____4878 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4878.FStar_Syntax_Syntax.fv_name in
                            uu____4873.FStar_Syntax_Syntax.v in
                          (uu____4872, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4868 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4867;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___121_4866.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___121_4866.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4860, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4898 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4907 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4916 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4919 = FStar_Options.using_facts_from () in
                 match uu____4919 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4931 =
                         let uu____4936 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4936 [([], false)] in
                       [uu____4931] in
                     let uu___122_4964 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_4964.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_4964.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_4964.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_4964.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_4964.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_4964.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_4964.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_4964.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_4964.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_4964.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_4964.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_4964.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_4964.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_4964.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_4964.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_4964.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_4964.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_4964.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___122_4964.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_4964.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_4964.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_4964.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_4964.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___122_4964.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___122_4964.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_4964.FStar_TypeChecker_Env.is_native_tactic)
                     }
                 | None  -> env))
           | uu____4966 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4967 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4973 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4973) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4974,uu____4975,uu____4976) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___89_4978  ->
                  match uu___89_4978 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4979 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4980,uu____4981,uu____4982) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___89_4988  ->
                  match uu___89_4988 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4989 -> false))
          -> env
      | uu____4990 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____5028 se =
        match uu____5028 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5058 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____5058
              then
                let uu____5059 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5059
              else ());
             (let uu____5061 = tc_decl env1 se in
              match uu____5061 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____5087 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____5087
                    then
                      let uu____5088 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____5091 =
                                 let uu____5092 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____5092 "\n" in
                               Prims.strcat s uu____5091) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____5088
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____5096 =
                      let accum_exports_hidden uu____5114 se1 =
                        match uu____5114 with
                        | (exports1,hidden1) ->
                            let uu____5130 = for_export hidden1 se1 in
                            (match uu____5130 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____5096 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____5180 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____5180 with
      | (ses1,exports,env1,uu____5206) ->
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
      (let uu____5233 = FStar_Options.debug_any () in
       if uu____5233
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
         let uu___123_5239 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_5239.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_5239.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_5239.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_5239.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_5239.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_5239.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_5239.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_5239.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_5239.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_5239.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_5239.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_5239.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___123_5239.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___123_5239.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_5239.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_5239.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___123_5239.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_5239.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___123_5239.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_5239.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___123_5239.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_5239.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___123_5239.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___123_5239.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___123_5239.FStar_TypeChecker_Env.is_native_tactic)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____5242 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5242 with
        | (ses,exports,env3) ->
            ((let uu___124_5260 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___124_5260.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___124_5260.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___124_5260.FStar_Syntax_Syntax.is_interface)
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
        let uu____5279 = tc_decls env decls in
        match uu____5279 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___125_5297 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___125_5297.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___125_5297.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___125_5297.FStar_Syntax_Syntax.is_interface)
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
          let uu___126_5314 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___126_5314.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___126_5314.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___126_5314.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___126_5314.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___126_5314.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___126_5314.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___126_5314.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___126_5314.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___126_5314.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___126_5314.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___126_5314.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___126_5314.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___126_5314.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___126_5314.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___126_5314.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___126_5314.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___126_5314.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___126_5314.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___126_5314.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___126_5314.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___126_5314.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___126_5314.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___126_5314.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___126_5314.FStar_TypeChecker_Env.is_native_tactic)
          } in
        let check_term lid univs1 t =
          let uu____5325 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5325 with
          | (univs2,t1) ->
              ((let uu____5331 =
                  let uu____5332 =
                    let uu____5335 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5335 in
                  FStar_All.pipe_left uu____5332
                    (FStar_Options.Other "Exports") in
                if uu____5331
                then
                  let uu____5336 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5337 =
                    let uu____5338 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5338
                      (FStar_String.concat ", ") in
                  let uu____5343 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5336 uu____5337 uu____5343
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5346 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5346 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5364 =
             let uu____5365 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5366 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5365 uu____5366 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5364);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5373) ->
              let uu____5378 =
                let uu____5379 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5379 in
              if uu____5378
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5387,uu____5388) ->
              let t =
                let uu____5396 =
                  let uu____5399 =
                    let uu____5400 =
                      let uu____5408 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5408) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5400 in
                  FStar_Syntax_Syntax.mk uu____5399 in
                uu____5396 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5420,uu____5421,uu____5422) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5428 =
                let uu____5429 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5429 in
              if uu____5428 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5432,lbs),uu____5434,uu____5435) ->
              let uu____5445 =
                let uu____5446 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5446 in
              if uu____5445
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
              let uu____5463 =
                let uu____5464 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5464 in
              if uu____5463
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5478 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5479 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5482 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5483 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5484 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5485 -> () in
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
          let uu___127_5502 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___127_5502.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___127_5502.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5505 =
           let uu____5506 = FStar_Options.lax () in
           Prims.op_Negation uu____5506 in
         if uu____5505 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5512 =
           let uu____5513 = FStar_Options.interactive () in
           Prims.op_Negation uu____5513 in
         if uu____5512
         then
           let uu____5514 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5514 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5526 = tc_partial_modul env modul in
      match uu____5526 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5549 = FStar_Options.debug_any () in
       if uu____5549
       then
         let uu____5550 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5550
       else ());
      (let env1 =
         let uu___128_5554 = env in
         let uu____5555 =
           let uu____5556 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5556 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___128_5554.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___128_5554.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___128_5554.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___128_5554.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___128_5554.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___128_5554.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___128_5554.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___128_5554.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___128_5554.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___128_5554.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___128_5554.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___128_5554.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___128_5554.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___128_5554.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___128_5554.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___128_5554.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___128_5554.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___128_5554.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5555;
           FStar_TypeChecker_Env.lax_universes =
             (uu___128_5554.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___128_5554.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___128_5554.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___128_5554.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___128_5554.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___128_5554.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___128_5554.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___128_5554.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____5557 = tc_modul env1 m in
       match uu____5557 with
       | (m1,env2) ->
           ((let uu____5565 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5565
             then
               let uu____5566 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5566
             else ());
            (let uu____5569 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5569
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
                       let uu____5596 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5596 with
                       | (univnames1,e) ->
                           let uu___129_5601 = lb in
                           let uu____5602 =
                             let uu____5605 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5605 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___129_5601.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___129_5601.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___129_5601.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___129_5601.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5602
                           } in
                     let uu___130_5606 = se in
                     let uu____5607 =
                       let uu____5608 =
                         let uu____5614 =
                           let uu____5618 = FStar_List.map update lbs in
                           (b, uu____5618) in
                         (uu____5614, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5608 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5607;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___130_5606.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___130_5606.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___130_5606.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5626 -> se in
               let normalized_module =
                 let uu___131_5628 = m1 in
                 let uu____5629 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___131_5628.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5629;
                   FStar_Syntax_Syntax.exports =
                     (uu___131_5628.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___131_5628.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5630 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5630
             else ());
            (m1, env2)))