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
                                     let uu____1093 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1093 with
                                     | (act_typ,uu____1098,g_t) ->
                                         let env' =
                                           let uu___96_1101 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___96_1101.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___96_1101.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___96_1101.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___96_1101.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___96_1101.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___96_1101.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___96_1101.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___96_1101.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___96_1101.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___96_1101.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___96_1101.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___96_1101.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___96_1101.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___96_1101.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___96_1101.FStar_TypeChecker_Env.is_native_tactic)
                                           } in
                                         ((let uu____1103 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1103
                                           then
                                             let uu____1104 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1105 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1104 uu____1105
                                           else ());
                                          (let uu____1107 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1107 with
                                           | (act_defn,uu____1112,g_a) ->
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
                                               let uu____1116 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1134 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1134 with
                                                      | (bs1,uu____1140) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1147 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1147 in
                                                          let uu____1150 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1150
                                                           with
                                                           | (k1,uu____1157,g)
                                                               -> (k1, g)))
                                                 | uu____1159 ->
                                                     let uu____1160 =
                                                       let uu____1161 =
                                                         let uu____1164 =
                                                           let uu____1165 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1166 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1165
                                                             uu____1166 in
                                                         (uu____1164,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1161 in
                                                     raise uu____1160 in
                                               (match uu____1116 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1173 =
                                                        let uu____1174 =
                                                          let uu____1175 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1175 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1174 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1173);
                                                     (let act_typ2 =
                                                        let uu____1179 =
                                                          let uu____1180 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1180.FStar_Syntax_Syntax.n in
                                                        match uu____1179 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1197 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1197
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1204
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1204
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1224
                                                                    =
                                                                    let uu____1225
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1225] in
                                                                    let uu____1226
                                                                    =
                                                                    let uu____1232
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1232] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1224;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1226;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1233
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1233))
                                                        | uu____1236 ->
                                                            failwith "" in
                                                      let uu____1239 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1239 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___97_1245 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___97_1245.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___97_1245.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___97_1245.FStar_Syntax_Syntax.action_params);
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
                                 let uu____1261 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1261 in
                               let uu____1264 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1264 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1270 =
                                        let uu____1273 =
                                          let uu____1274 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1274.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1273) in
                                      match uu____1270 with
                                      | ([],uu____1277) -> t1
                                      | (uu____1283,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1284,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1296 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1307 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1307 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1313 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1314 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1314))
                                           && (m <> n1) in
                                       if uu____1313
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1328 =
                                           let uu____1329 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1330 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1329 uu____1330 in
                                         failwith uu____1328
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1336 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1336 with
                                      | (univs2,defn) ->
                                          let uu____1341 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1341 with
                                           | (univs',typ) ->
                                               let uu___98_1347 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___98_1347.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___98_1347.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___98_1347.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___99_1350 = ed2 in
                                      let uu____1351 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1352 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1353 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1354 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1355 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1356 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1357 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1358 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1359 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1360 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1361 =
                                        let uu____1362 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1362 in
                                      let uu____1368 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1369 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1370 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___99_1350.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___99_1350.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1351;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1352;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1353;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1354;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1355;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1356;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1357;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1358;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1359;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1360;
                                        FStar_Syntax_Syntax.repr = uu____1361;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1368;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1369;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1370
                                      } in
                                    ((let uu____1373 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1373
                                      then
                                        let uu____1374 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1374
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
      let uu____1378 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1378 with
      | (effect_binders_un,signature_un) ->
          let uu____1388 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1388 with
           | (effect_binders,env1,uu____1399) ->
               let uu____1400 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1400 with
                | (signature,uu____1409) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1418  ->
                           match uu____1418 with
                           | (bv,qual) ->
                               let uu____1425 =
                                 let uu___100_1426 = bv in
                                 let uu____1427 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___100_1426.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___100_1426.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1427
                                 } in
                               (uu____1425, qual)) effect_binders in
                    let uu____1430 =
                      let uu____1435 =
                        let uu____1436 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1436.FStar_Syntax_Syntax.n in
                      match uu____1435 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1444)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1459 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1430 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1476 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1476
                           then
                             let uu____1477 =
                               let uu____1479 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1479 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1477
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1503 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1503 with
                           | (t2,comp,uu____1511) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1522 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1522 with
                          | (repr,_comp) ->
                              ((let uu____1535 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1535
                                then
                                  let uu____1536 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1536
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
                                  let uu____1542 =
                                    let uu____1543 =
                                      let uu____1544 =
                                        let uu____1554 =
                                          let uu____1558 =
                                            let uu____1561 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1562 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1561, uu____1562) in
                                          [uu____1558] in
                                        (wp_type1, uu____1554) in
                                      FStar_Syntax_Syntax.Tm_app uu____1544 in
                                    mk1 uu____1543 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1542 in
                                let effect_signature =
                                  let binders =
                                    let uu____1577 =
                                      let uu____1580 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1580) in
                                    let uu____1581 =
                                      let uu____1585 =
                                        let uu____1586 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1586
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1585] in
                                    uu____1577 :: uu____1581 in
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
                                  let uu____1629 = item in
                                  match uu____1629 with
                                  | (u_item,item1) ->
                                      let uu____1641 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1641 with
                                       | (item2,item_comp) ->
                                           ((let uu____1651 =
                                               let uu____1652 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1652 in
                                             if uu____1651
                                             then
                                               let uu____1653 =
                                                 let uu____1654 =
                                                   let uu____1655 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1656 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1655 uu____1656 in
                                                 FStar_Errors.Err uu____1654 in
                                               raise uu____1653
                                             else ());
                                            (let uu____1658 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1658 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1671 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1671 with
                                | (dmff_env1,uu____1684,bind_wp,bind_elab) ->
                                    let uu____1687 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1687 with
                                     | (dmff_env2,uu____1700,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1704 =
                                             let uu____1705 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1705.FStar_Syntax_Syntax.n in
                                           match uu____1704 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1743 =
                                                 let uu____1751 =
                                                   let uu____1754 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1754 in
                                                 match uu____1751 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1793 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1743 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1815 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1815 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1826 =
                                                          let uu____1827 =
                                                            let uu____1837 =
                                                              let uu____1841
                                                                =
                                                                let uu____1844
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1845
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1844,
                                                                  uu____1845) in
                                                              [uu____1841] in
                                                            (wp_type1,
                                                              uu____1837) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1827 in
                                                        mk1 uu____1826 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1853 =
                                                      let uu____1863 =
                                                        let uu____1864 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1864 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1863 in
                                                    (match uu____1853 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1892
                                                           =
                                                           let error_msg =
                                                             let uu____1894 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1895 =
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
                                                                   (lid,uu____1911))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1894
                                                               uu____1895 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1937
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1937
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
                                                               (lid,uu____1943))
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
                                                             let uu____1963 =
                                                               let uu____1964
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1965
                                                                 =
                                                                 let uu____1966
                                                                   =
                                                                   let uu____1970
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1970,
                                                                    None) in
                                                                 [uu____1966] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1964
                                                                 uu____1965 in
                                                             uu____1963 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1986 =
                                                             let uu____1987 =
                                                               let uu____1991
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1991] in
                                                             b11 ::
                                                               uu____1987 in
                                                           let uu____1994 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1986
                                                             uu____1994
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____2004 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2006 =
                                             let uu____2007 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2007.FStar_Syntax_Syntax.n in
                                           match uu____2006 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2045 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2045
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2061 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2063 =
                                             let uu____2064 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2064.FStar_Syntax_Syntax.n in
                                           match uu____2063 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2093 =
                                                 let uu____2094 =
                                                   let uu____2096 =
                                                     let uu____2097 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2097 in
                                                   [uu____2096] in
                                                 FStar_List.append uu____2094
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2093 body what
                                           | uu____2098 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2118 =
                                                let uu____2119 =
                                                  let uu____2120 =
                                                    let uu____2130 =
                                                      let uu____2131 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2131 in
                                                    (t, uu____2130) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2120 in
                                                mk1 uu____2119 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2118) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2154 = f a2 in
                                               [uu____2154]
                                           | x::xs ->
                                               let uu____2158 =
                                                 apply_last1 f xs in
                                               x :: uu____2158 in
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
                                           let uu____2173 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2173 with
                                           | Some (_us,_t) ->
                                               ((let uu____2190 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2190
                                                 then
                                                   let uu____2191 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2191
                                                 else ());
                                                (let uu____2193 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2193))
                                           | None  ->
                                               let uu____2198 =
                                                 let uu____2201 = mk_lid name in
                                                 let uu____2202 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2201 uu____2202 in
                                               (match uu____2198 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2211 =
                                                        let uu____2213 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2213 in
                                                      FStar_ST.write sigelts
                                                        uu____2211);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2224 =
                                             let uu____2226 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2227 =
                                               FStar_ST.read sigelts in
                                             uu____2226 :: uu____2227 in
                                           FStar_ST.write sigelts uu____2224);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2237 =
                                              let uu____2239 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2240 =
                                                FStar_ST.read sigelts in
                                              uu____2239 :: uu____2240 in
                                            FStar_ST.write sigelts uu____2237);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2250 =
                                               let uu____2252 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2253 =
                                                 FStar_ST.read sigelts in
                                               uu____2252 :: uu____2253 in
                                             FStar_ST.write sigelts
                                               uu____2250);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2263 =
                                                let uu____2265 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2266 =
                                                  FStar_ST.read sigelts in
                                                uu____2265 :: uu____2266 in
                                              FStar_ST.write sigelts
                                                uu____2263);
                                             (let uu____2274 =
                                                FStar_List.fold_left
                                                  (fun uu____2281  ->
                                                     fun action  ->
                                                       match uu____2281 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2294 =
                                                             let uu____2298 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2298
                                                               params_un in
                                                           (match uu____2294
                                                            with
                                                            | (action_params,env',uu____2304)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2313
                                                                     ->
                                                                    match uu____2313
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2320
                                                                    =
                                                                    let uu___101_2321
                                                                    = bv in
                                                                    let uu____2322
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___101_2321.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___101_2321.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2322
                                                                    } in
                                                                    (uu____2320,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2326
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2326
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
                                                                    uu____2352
                                                                    ->
                                                                    let uu____2353
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2353 in
                                                                    ((
                                                                    let uu____2357
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2357
                                                                    then
                                                                    let uu____2358
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2359
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2360
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2361
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2358
                                                                    uu____2359
                                                                    uu____2360
                                                                    uu____2361
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
                                                                    let uu____2365
                                                                    =
                                                                    let uu____2367
                                                                    =
                                                                    let uu___102_2368
                                                                    = action in
                                                                    let uu____2369
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2370
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___102_2368.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___102_2368.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___102_2368.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2369;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2370
                                                                    } in
                                                                    uu____2367
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2365))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2274 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2390 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2391 =
                                                        let uu____2393 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2393] in
                                                      uu____2390 ::
                                                        uu____2391 in
                                                    let uu____2394 =
                                                      let uu____2395 =
                                                        let uu____2396 =
                                                          let uu____2397 =
                                                            let uu____2407 =
                                                              let uu____2411
                                                                =
                                                                let uu____2414
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2415
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2414,
                                                                  uu____2415) in
                                                              [uu____2411] in
                                                            (repr,
                                                              uu____2407) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2397 in
                                                        mk1 uu____2396 in
                                                      let uu____2423 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2395
                                                        uu____2423 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2394 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2431 =
                                                    let uu____2436 =
                                                      let uu____2437 =
                                                        let uu____2440 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2440 in
                                                      uu____2437.FStar_Syntax_Syntax.n in
                                                    match uu____2436 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2448)
                                                        ->
                                                        let uu____2475 =
                                                          let uu____2484 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2484
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2515 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2475
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2543 =
                                                               let uu____2544
                                                                 =
                                                                 let uu____2547
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2547 in
                                                               uu____2544.FStar_Syntax_Syntax.n in
                                                             (match uu____2543
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2564
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2564
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2573
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2584
                                                                     ->
                                                                    match uu____2584
                                                                    with
                                                                    | 
                                                                    (bv,uu____2588)
                                                                    ->
                                                                    let uu____2589
                                                                    =
                                                                    let uu____2590
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2590
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2589
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2573
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
                                                                    uu____2623
                                                                    ->
                                                                    let uu____2627
                                                                    =
                                                                    let uu____2628
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2628 in
                                                                    failwith
                                                                    uu____2627 in
                                                                    let uu____2631
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2634
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2631,
                                                                    uu____2634)))
                                                              | uu____2644 ->
                                                                  let uu____2645
                                                                    =
                                                                    let uu____2646
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2646 in
                                                                  failwith
                                                                    uu____2645))
                                                    | uu____2651 ->
                                                        let uu____2652 =
                                                          let uu____2653 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2653 in
                                                        failwith uu____2652 in
                                                  (match uu____2431 with
                                                   | (pre,post) ->
                                                       ((let uu____2670 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2672 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2674 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___103_2676
                                                             = ed in
                                                           let uu____2677 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2678 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2679 =
                                                             let uu____2680 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2680) in
                                                           let uu____2686 =
                                                             let uu____2687 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2687) in
                                                           let uu____2693 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2694 =
                                                             let uu____2695 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2695) in
                                                           let uu____2701 =
                                                             let uu____2702 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2702) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2677;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2678;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2679;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2686;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___103_2676.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2693;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2694;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2701;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2708 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2708
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2719
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2719
                                                               then
                                                                 let uu____2720
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2720
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
                                                                    let uu____2732
                                                                    =
                                                                    let uu____2734
                                                                    =
                                                                    let uu____2740
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2740) in
                                                                    Some
                                                                    uu____2734 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2732;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2751
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2751
                                                                 else None in
                                                               let uu____2753
                                                                 =
                                                                 let uu____2755
                                                                   =
                                                                   let uu____2757
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2757 in
                                                                 FStar_List.append
                                                                   uu____2755
                                                                   sigelts' in
                                                               (uu____2753,
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
                (lex_t1,[],[],t,uu____2780,uu____2781);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2783;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2787);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2789;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2793);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2795;_}::[]
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
                let uu____2834 =
                  let uu____2837 =
                    let uu____2838 =
                      let uu____2843 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2843, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2838 in
                  FStar_Syntax_Syntax.mk uu____2837 in
                uu____2834 None r1 in
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
                  let uu____2863 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2863 in
                let hd1 =
                  let uu____2869 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2869 in
                let tl1 =
                  let uu____2871 =
                    let uu____2872 =
                      let uu____2875 =
                        let uu____2876 =
                          let uu____2881 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2881, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2876 in
                      FStar_Syntax_Syntax.mk uu____2875 in
                    uu____2872 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2871 in
                let res =
                  let uu____2894 =
                    let uu____2897 =
                      let uu____2898 =
                        let uu____2903 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2903,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2898 in
                    FStar_Syntax_Syntax.mk uu____2897 in
                  uu____2894 None r2 in
                let uu____2913 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2913 in
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
              let uu____2935 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2935;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2938 ->
              let uu____2940 =
                let uu____2941 =
                  let uu____2942 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2942 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2941 in
              failwith uu____2940
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
            let uu____2952 = FStar_Syntax_Util.type_u () in
            match uu____2952 with
            | (k,uu____2956) ->
                let phi1 =
                  let uu____2958 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2958
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
          let uu____2968 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2968 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2987 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2987 FStar_List.flatten in
              ((let uu____2995 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2995
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
                          let uu____3001 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____3007,uu____3008,uu____3009,uu____3010,uu____3011)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____3016 -> failwith "Impossible!" in
                          match uu____3001 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____3025 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____3029,uu____3030,uu____3031,uu____3032,uu____3033)
                        -> lid
                    | uu____3038 -> failwith "Impossible" in
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
                let uu____3044 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____3044
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
                   let uu____3062 =
                     let uu____3064 =
                       let uu____3065 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____3065;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____3064 :: ses1 in
                   (uu____3062, data_ops_ses))))
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3083 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3096 ->
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
           let uu____3126 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3126 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3151 = FStar_Options.set_options t s in
             match uu____3151 with
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
                ((let uu____3168 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3168 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3174 = cps_and_elaborate env1 ne in
           (match uu____3174 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___104_3195 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___104_3195.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___104_3195.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___104_3195.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___105_3196 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___105_3196.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_3196.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_3196.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___106_3202 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___106_3202.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___106_3202.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___106_3202.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3208 =
             let uu____3213 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3213 in
           (match uu____3208 with
            | (a,wp_a_src) ->
                let uu____3224 =
                  let uu____3229 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3229 in
                (match uu____3224 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3241 =
                         let uu____3243 =
                           let uu____3244 =
                             let uu____3249 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3249) in
                           FStar_Syntax_Syntax.NT uu____3244 in
                         [uu____3243] in
                       FStar_Syntax_Subst.subst uu____3241 wp_b_tgt in
                     let expected_k =
                       let uu____3253 =
                         let uu____3257 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3258 =
                           let uu____3260 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3260] in
                         uu____3257 :: uu____3258 in
                       let uu____3261 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3253 uu____3261 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3282 =
                           let uu____3283 =
                             let uu____3286 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3287 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3286, uu____3287) in
                           FStar_Errors.Error uu____3283 in
                         raise uu____3282 in
                       let uu____3290 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3290 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3309 =
                             let uu____3310 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3310 in
                           if uu____3309
                           then no_reify eff_name
                           else
                             (let uu____3315 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3316 =
                                let uu____3319 =
                                  let uu____3320 =
                                    let uu____3330 =
                                      let uu____3332 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3333 =
                                        let uu____3335 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3335] in
                                      uu____3332 :: uu____3333 in
                                    (repr, uu____3330) in
                                  FStar_Syntax_Syntax.Tm_app uu____3320 in
                                FStar_Syntax_Syntax.mk uu____3319 in
                              uu____3316 None uu____3315) in
                     let uu____3345 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3360,lift_wp)) ->
                           let uu____3373 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3373)
                       | (Some (what,lift),None ) ->
                           ((let uu____3388 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3388
                             then
                               let uu____3389 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3389
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3392 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3392 with
                             | (lift1,comp,uu____3401) ->
                                 let uu____3402 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3402 with
                                  | (uu____3409,lift_wp,lift_elab) ->
                                      let uu____3412 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3413 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3345 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___107_3436 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___107_3436.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___107_3436.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___107_3436.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___107_3436.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___107_3436.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___107_3436.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___107_3436.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___107_3436.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___107_3436.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___107_3436.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___107_3436.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___107_3436.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___107_3436.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___107_3436.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___107_3436.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___107_3436.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___107_3436.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___107_3436.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___107_3436.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___107_3436.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___107_3436.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___107_3436.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___107_3436.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___107_3436.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___107_3436.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___107_3436.FStar_TypeChecker_Env.is_native_tactic)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3440,lift1) ->
                                let uu____3447 =
                                  let uu____3452 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3452 in
                                (match uu____3447 with
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
                                         let uu____3474 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3475 =
                                           let uu____3478 =
                                             let uu____3479 =
                                               let uu____3489 =
                                                 let uu____3491 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3492 =
                                                   let uu____3494 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3494] in
                                                 uu____3491 :: uu____3492 in
                                               (lift_wp1, uu____3489) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3479 in
                                           FStar_Syntax_Syntax.mk uu____3478 in
                                         uu____3475 None uu____3474 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3507 =
                                         let uu____3511 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3512 =
                                           let uu____3514 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3515 =
                                             let uu____3517 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3517] in
                                           uu____3514 :: uu____3515 in
                                         uu____3511 :: uu____3512 in
                                       let uu____3518 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3507
                                         uu____3518 in
                                     let uu____3521 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3521 with
                                      | (expected_k2,uu____3527,uu____3528)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___108_3531 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___108_3531.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___108_3531.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___109_3533 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___109_3533.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___109_3533.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___109_3533.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3546 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3546 with
            | (tps1,c1) ->
                let uu____3555 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3555 with
                 | (tps2,env3,us) ->
                     let uu____3566 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3566 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3580 =
                              let uu____3581 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3581 in
                            match uu____3580 with
                            | (uvs1,t) ->
                                let uu____3594 =
                                  let uu____3602 =
                                    let uu____3605 =
                                      let uu____3606 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3606.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3605) in
                                  match uu____3602 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3616,c4)) -> ([], c4)
                                  | (uu____3640,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3658 -> failwith "Impossible" in
                                (match uu____3594 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3689 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3689 with
                                         | (uu____3692,t1) ->
                                             let uu____3694 =
                                               let uu____3695 =
                                                 let uu____3698 =
                                                   let uu____3699 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3700 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3705 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3699 uu____3700
                                                     uu____3705 in
                                                 (uu____3698, r) in
                                               FStar_Errors.Error uu____3695 in
                                             raise uu____3694)
                                      else ();
                                      (let se1 =
                                         let uu___110_3708 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___110_3708.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___110_3708.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___110_3708.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3718,uu____3719,uu____3720) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___84_3722  ->
                   match uu___84_3722 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3723 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3726,uu____3727,uu____3728) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___84_3734  ->
                   match uu___84_3734 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3735 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3742 =
             if uvs = []
             then
               let uu____3743 =
                 let uu____3744 = FStar_Syntax_Util.type_u () in
                 fst uu____3744 in
               check_and_gen env2 t uu____3743
             else
               (let uu____3748 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3748 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3754 =
                        let uu____3755 = FStar_Syntax_Util.type_u () in
                        fst uu____3755 in
                      tc_check_trivial_guard env2 t1 uu____3754 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3759 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3759)) in
           (match uu____3742 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___111_3769 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___111_3769.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___111_3769.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___111_3769.FStar_Syntax_Syntax.sigmeta)
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
           let uu____3781 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3781 with
            | (e1,c,g1) ->
                let uu____3792 =
                  let uu____3796 =
                    let uu____3798 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3798 in
                  let uu____3799 =
                    let uu____3802 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3802) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3796 uu____3799 in
                (match uu____3792 with
                 | (e2,uu____3812,g) ->
                     ((let uu____3815 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3815);
                      (let se1 =
                         let uu___112_3817 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___112_3817.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___112_3817.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___112_3817.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3853 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3853
                 then Some q
                 else
                   (let uu____3866 =
                      let uu____3867 =
                        let uu____3870 =
                          let uu____3871 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3872 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3873 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3871 uu____3872 uu____3873 in
                        (uu____3870, r) in
                      FStar_Errors.Error uu____3867 in
                    raise uu____3866) in
           let uu____3876 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3897  ->
                     fun lb  ->
                       match uu____3897 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3921 =
                             let uu____3927 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3927 with
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
                                   | uu____3979 ->
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
                                  (let uu____3991 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3991, quals_opt1))) in
                           (match uu____3921 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3876 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____4044 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___85_4046  ->
                                match uu___85_4046 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____4047 -> false)) in
                      if uu____4044
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____4055 =
                    let uu____4058 =
                      let uu____4059 =
                        let uu____4067 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____4067) in
                      FStar_Syntax_Syntax.Tm_let uu____4059 in
                    FStar_Syntax_Syntax.mk uu____4058 in
                  uu____4055 None r in
                let uu____4089 =
                  let uu____4095 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___113_4099 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___113_4099.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___113_4099.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___113_4099.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___113_4099.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___113_4099.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___113_4099.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___113_4099.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___113_4099.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___113_4099.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___113_4099.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___113_4099.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___113_4099.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___113_4099.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___113_4099.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___113_4099.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___113_4099.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___113_4099.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___113_4099.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___113_4099.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___113_4099.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___113_4099.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___113_4099.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___113_4099.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___113_4099.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___113_4099.FStar_TypeChecker_Env.is_native_tactic)
                       }) e in
                  match uu____4095 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4107;
                       FStar_Syntax_Syntax.pos = uu____4108;
                       FStar_Syntax_Syntax.vars = uu____4109;_},uu____4110,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4129,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4134 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___86_4137  ->
                             match uu___86_4137 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4139 =
                                   let uu____4140 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4144 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4144)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4140 in
                                 if uu____4139
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___114_4153 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___114_4153.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___114_4153.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4159 -> failwith "impossible" in
                (match uu____4089 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4186 = log env2 in
                       if uu____4186
                       then
                         let uu____4187 =
                           let uu____4188 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4195 =
                                         let uu____4200 =
                                           let uu____4201 =
                                             let uu____4206 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4206.FStar_Syntax_Syntax.fv_name in
                                           uu____4201.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4200 in
                                       match uu____4195 with
                                       | None  -> true
                                       | uu____4213 -> false in
                                     if should_log
                                     then
                                       let uu____4218 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4219 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4218 uu____4219
                                     else "")) in
                           FStar_All.pipe_right uu____4188
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4187
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4243 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____4243 with
                              | (bs1,c1) ->
                                  let uu____4248 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____4248
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4258 =
                                            let uu____4259 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____4259.FStar_Syntax_Syntax.n in
                                          (match uu____4258 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4278 =
                                                 let uu____4279 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____4279.FStar_Syntax_Syntax.n in
                                               (match uu____4278 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4289 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4289 in
                                                    let uu____4290 =
                                                      let uu____4291 =
                                                        let uu____4292 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4292 args in
                                                      uu____4291 None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4290 u
                                                | uu____4297 -> c1)
                                           | uu____4298 -> c1)
                                      | uu____4299 -> c1 in
                                    let uu___115_4300 = t1 in
                                    let uu____4301 =
                                      let uu____4302 =
                                        let uu____4310 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4310) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4302 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4301;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___115_4300.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___115_4300.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___115_4300.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4332 =
                               let uu____4333 = FStar_Syntax_Subst.compress h in
                               uu____4333.FStar_Syntax_Syntax.n in
                             (match uu____4332 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4343 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4343 in
                                  let uu____4344 =
                                    let uu____4345 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4345
                                      args in
                                  uu____4344 None t1.FStar_Syntax_Syntax.pos
                              | uu____4350 -> t1)
                         | uu____4351 -> t1 in
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
                           let uu____4382 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4382 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4391 =
                                  FStar_Syntax_Syntax.bv_to_name (fst x) in
                                (uu____4391, (snd x))) bs in
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
                           let uu____4423 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4423 in
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
                         let uu___116_4454 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___117_4461 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___117_4461.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___117_4461.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___117_4461.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___117_4461.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids, attrs));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___116_4454.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___116_4454.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___116_4454.FStar_Syntax_Syntax.sigmeta)
                         } in
                       let tactic_decls =
                         match snd lbs1 with
                         | hd1::[] ->
                             let uu____4471 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4471 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4491 =
                                    let uu____4492 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4492.FStar_Syntax_Syntax.n in
                                  (match uu____4491 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4516 =
                                           let uu____4521 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4521.FStar_Syntax_Syntax.fv_name in
                                         uu____4516.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4526 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4526 in
                                       let uu____4527 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____4528 =
                                              let uu____4529 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4529 in
                                            Prims.op_Negation uu____4528) in
                                       if uu____4527
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl (fst lbs1)
                                             hd1 bs assm_lid comp in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4552 -> None))
                         | uu____4555 -> None in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4568 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4568
                             then
                               let uu____4569 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4570 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4569 uu____4570
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
             (fun uu___87_4603  ->
                match uu___87_4603 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4604 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4610) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4614 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4619 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4622 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4635 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4648) ->
          let uu____4653 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4653
          then
            let for_export_bundle se1 uu____4672 =
              match uu____4672 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4695,uu____4696) ->
                       let dec =
                         let uu___118_4702 = se1 in
                         let uu____4703 =
                           let uu____4704 =
                             let uu____4708 =
                               let uu____4711 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4711 in
                             (l, us, uu____4708) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4704 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4703;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___118_4702.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___118_4702.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4721,uu____4722,uu____4723) ->
                       let dec =
                         let uu___119_4727 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___119_4727.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___119_4727.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4730 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4742,uu____4743) ->
          let uu____4744 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4744 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4757 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4757
          then
            ([(let uu___120_4765 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___120_4765.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___120_4765.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4767 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___88_4769  ->
                       match uu___88_4769 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4770 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4773 -> true
                       | uu____4774 -> false)) in
             if uu____4767 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4784 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4787 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4790 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4793 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4796 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4806,uu____4807)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4823 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4823
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4844) ->
          let uu____4849 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4849
          then
            let uu____4854 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___121_4860 = se in
                      let uu____4861 =
                        let uu____4862 =
                          let uu____4866 =
                            let uu____4867 =
                              let uu____4872 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4872.FStar_Syntax_Syntax.fv_name in
                            uu____4867.FStar_Syntax_Syntax.v in
                          (uu____4866, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4862 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4861;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___121_4860.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___121_4860.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4854, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4892 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4901 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4910 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4913 = FStar_Options.using_facts_from () in
                 match uu____4913 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4925 =
                         let uu____4930 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4930 [([], false)] in
                       [uu____4925] in
                     let uu___122_4958 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_4958.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_4958.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_4958.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_4958.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_4958.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_4958.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_4958.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_4958.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_4958.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_4958.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_4958.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_4958.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_4958.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_4958.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_4958.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_4958.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_4958.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_4958.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___122_4958.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_4958.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_4958.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_4958.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_4958.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___122_4958.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___122_4958.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_4958.FStar_TypeChecker_Env.is_native_tactic)
                     }
                 | None  -> env))
           | uu____4960 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4961 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4967 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4967) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4968,uu____4969,uu____4970) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___89_4972  ->
                  match uu___89_4972 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4973 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4974,uu____4975,uu____4976) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___89_4982  ->
                  match uu___89_4982 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4983 -> false))
          -> env
      | uu____4984 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____5022 se =
        match uu____5022 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____5052 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____5052
              then
                let uu____5053 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5053
              else ());
             (let uu____5055 = tc_decl env1 se in
              match uu____5055 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____5081 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____5081
                    then
                      let uu____5082 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____5085 =
                                 let uu____5086 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____5086 "\n" in
                               Prims.strcat s uu____5085) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____5082
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____5090 =
                      let accum_exports_hidden uu____5108 se1 =
                        match uu____5108 with
                        | (exports1,hidden1) ->
                            let uu____5124 = for_export hidden1 se1 in
                            (match uu____5124 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____5090 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____5174 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____5174 with
      | (ses1,exports,env1,uu____5200) ->
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
      (let uu____5227 = FStar_Options.debug_any () in
       if uu____5227
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
         let uu___123_5233 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_5233.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_5233.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_5233.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_5233.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_5233.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_5233.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_5233.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_5233.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_5233.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_5233.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_5233.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_5233.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___123_5233.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___123_5233.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_5233.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_5233.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___123_5233.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_5233.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___123_5233.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_5233.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___123_5233.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_5233.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___123_5233.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___123_5233.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___123_5233.FStar_TypeChecker_Env.is_native_tactic)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____5236 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5236 with
        | (ses,exports,env3) ->
            ((let uu___124_5254 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___124_5254.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___124_5254.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___124_5254.FStar_Syntax_Syntax.is_interface)
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
        let uu____5273 = tc_decls env decls in
        match uu____5273 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___125_5291 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___125_5291.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___125_5291.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___125_5291.FStar_Syntax_Syntax.is_interface)
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
          let uu___126_5308 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___126_5308.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___126_5308.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___126_5308.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___126_5308.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___126_5308.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___126_5308.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___126_5308.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___126_5308.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___126_5308.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___126_5308.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___126_5308.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___126_5308.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___126_5308.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___126_5308.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___126_5308.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___126_5308.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___126_5308.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___126_5308.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___126_5308.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___126_5308.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___126_5308.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___126_5308.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___126_5308.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___126_5308.FStar_TypeChecker_Env.is_native_tactic)
          } in
        let check_term lid univs1 t =
          let uu____5319 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5319 with
          | (univs2,t1) ->
              ((let uu____5325 =
                  let uu____5326 =
                    let uu____5329 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5329 in
                  FStar_All.pipe_left uu____5326
                    (FStar_Options.Other "Exports") in
                if uu____5325
                then
                  let uu____5330 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5331 =
                    let uu____5332 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5332
                      (FStar_String.concat ", ") in
                  let uu____5337 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5330 uu____5331 uu____5337
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5340 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5340 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5358 =
             let uu____5359 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5360 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5359 uu____5360 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5358);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5367) ->
              let uu____5372 =
                let uu____5373 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5373 in
              if uu____5372
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5381,uu____5382) ->
              let t =
                let uu____5390 =
                  let uu____5393 =
                    let uu____5394 =
                      let uu____5402 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5402) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5394 in
                  FStar_Syntax_Syntax.mk uu____5393 in
                uu____5390 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5414,uu____5415,uu____5416) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5422 =
                let uu____5423 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5423 in
              if uu____5422 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5426,lbs),uu____5428,uu____5429) ->
              let uu____5439 =
                let uu____5440 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5440 in
              if uu____5439
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
              let uu____5457 =
                let uu____5458 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5458 in
              if uu____5457
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5472 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5473 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5476 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5477 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5478 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5479 -> () in
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
          let uu___127_5496 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___127_5496.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___127_5496.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5499 =
           let uu____5500 = FStar_Options.lax () in
           Prims.op_Negation uu____5500 in
         if uu____5499 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5506 =
           let uu____5507 = FStar_Options.interactive () in
           Prims.op_Negation uu____5507 in
         if uu____5506
         then
           let uu____5508 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5508 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5520 = tc_partial_modul env modul in
      match uu____5520 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5543 = FStar_Options.debug_any () in
       if uu____5543
       then
         let uu____5544 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5544
       else ());
      (let env1 =
         let uu___128_5548 = env in
         let uu____5549 =
           let uu____5550 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5550 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___128_5548.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___128_5548.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___128_5548.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___128_5548.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___128_5548.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___128_5548.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___128_5548.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___128_5548.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___128_5548.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___128_5548.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___128_5548.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___128_5548.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___128_5548.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___128_5548.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___128_5548.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___128_5548.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___128_5548.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___128_5548.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5549;
           FStar_TypeChecker_Env.lax_universes =
             (uu___128_5548.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___128_5548.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___128_5548.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___128_5548.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___128_5548.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___128_5548.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___128_5548.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___128_5548.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____5551 = tc_modul env1 m in
       match uu____5551 with
       | (m1,env2) ->
           ((let uu____5559 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5559
             then
               let uu____5560 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5560
             else ());
            (let uu____5563 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5563
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
                       let uu____5590 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5590 with
                       | (univnames1,e) ->
                           let uu___129_5595 = lb in
                           let uu____5596 =
                             let uu____5599 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5599 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___129_5595.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___129_5595.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___129_5595.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___129_5595.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5596
                           } in
                     let uu___130_5600 = se in
                     let uu____5601 =
                       let uu____5602 =
                         let uu____5608 =
                           let uu____5612 = FStar_List.map update lbs in
                           (b, uu____5612) in
                         (uu____5608, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5602 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5601;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___130_5600.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___130_5600.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___130_5600.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5620 -> se in
               let normalized_module =
                 let uu___131_5622 = m1 in
                 let uu____5623 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___131_5622.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5623;
                   FStar_Syntax_Syntax.exports =
                     (uu___131_5622.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___131_5622.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5624 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5624
             else ());
            (m1, env2)))