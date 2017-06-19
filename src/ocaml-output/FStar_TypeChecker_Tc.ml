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
          let uu___91_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___91_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___91_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___91_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___91_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___91_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___91_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___91_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___91_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___91_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___91_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___91_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___91_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___91_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___91_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___91_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___91_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___91_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___91_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___91_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___91_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___91_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___91_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___91_12.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___91_12.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___91_12.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___91_12.FStar_TypeChecker_Env.is_native_tactic)
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
          let uu___92_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___92_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___92_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___92_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___92_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___92_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___92_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___92_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___92_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___92_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___92_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___92_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___92_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___92_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___92_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___92_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___92_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___92_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___92_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___92_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___92_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___92_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___92_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___92_24.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___92_24.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___92_24.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___92_24.FStar_TypeChecker_Env.is_native_tactic)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____30 =
         let uu____31 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____31 in
       Prims.op_Negation uu____30)
let is_native_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____42) ->
            let uu____47 =
              let uu____48 = FStar_Syntax_Subst.compress h' in
              uu____48.FStar_Syntax_Syntax.n in
            (match uu____47 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.tactic_lid
                 -> env.FStar_TypeChecker_Env.is_native_tactic tac_lid
             | uu____52 -> false)
        | uu____53 -> false
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____63 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____63 with
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
        (let uu____85 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____85
         then
           let uu____86 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____86
         else ());
        (let uu____88 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____88 with
         | (t',uu____93,uu____94) ->
             ((let uu____96 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____96
               then
                 let uu____97 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____97
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
        let uu____108 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____108
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____130 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____130)
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
        let fail uu____152 =
          let uu____153 =
            let uu____154 =
              let uu____157 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____157, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____154 in
          raise uu____153 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____185)::(wp,uu____187)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____196 -> fail ())
        | uu____197 -> fail ()
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____259 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____259 with
      | (effect_params_un,signature_un,opening) ->
          let uu____266 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____266 with
           | (effect_params,env,uu____272) ->
               let uu____273 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____273 with
                | (signature,uu____277) ->
                    let ed1 =
                      let uu___93_279 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___93_279.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___93_279.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___93_279.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___93_279.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___93_279.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___93_279.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___93_279.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___93_279.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___93_279.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___93_279.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___93_279.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___93_279.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___93_279.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___93_279.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___93_279.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___93_279.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___93_279.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____283 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
                          let uu___94_301 = ed1 in
                          let uu____302 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____303 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____304 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____305 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____306 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____307 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____308 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____309 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____310 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____311 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____312 =
                            let uu____313 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____313 in
                          let uu____319 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____320 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____321 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___95_324 = a in
                                 let uu____325 =
                                   let uu____326 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____326 in
                                 let uu____332 =
                                   let uu____333 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____333 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___95_324.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___95_324.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___95_324.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___95_324.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____325;
                                   FStar_Syntax_Syntax.action_typ = uu____332
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___94_301.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___94_301.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___94_301.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___94_301.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___94_301.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____302;
                            FStar_Syntax_Syntax.bind_wp = uu____303;
                            FStar_Syntax_Syntax.if_then_else = uu____304;
                            FStar_Syntax_Syntax.ite_wp = uu____305;
                            FStar_Syntax_Syntax.stronger = uu____306;
                            FStar_Syntax_Syntax.close_wp = uu____307;
                            FStar_Syntax_Syntax.assert_p = uu____308;
                            FStar_Syntax_Syntax.assume_p = uu____309;
                            FStar_Syntax_Syntax.null_wp = uu____310;
                            FStar_Syntax_Syntax.trivial = uu____311;
                            FStar_Syntax_Syntax.repr = uu____312;
                            FStar_Syntax_Syntax.return_repr = uu____319;
                            FStar_Syntax_Syntax.bind_repr = uu____320;
                            FStar_Syntax_Syntax.actions = uu____321
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____361 =
                          let uu____362 =
                            let uu____365 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____365, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____362 in
                        raise uu____361 in
                      let uu____370 =
                        let uu____371 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____371.FStar_Syntax_Syntax.n in
                      match uu____370 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____396)::(wp,uu____398)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____407 -> fail signature1)
                      | uu____408 -> fail signature1 in
                    let uu____409 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____409 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____427 =
                           let uu____428 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____428 with
                           | (signature1,uu____436) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____438 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____438 in
                         ((let uu____440 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____440
                           then
                             let uu____441 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____442 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____443 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____444 =
                               let uu____445 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____445 in
                             let uu____446 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____441 uu____442 uu____443 uu____444
                               uu____446
                           else ());
                          (let check_and_gen' env2 uu____459 k =
                             match uu____459 with
                             | (uu____464,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____472 =
                                 let uu____476 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____477 =
                                   let uu____479 =
                                     let uu____480 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____480 in
                                   [uu____479] in
                                 uu____476 :: uu____477 in
                               let uu____481 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____472 uu____481 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____485 = fresh_effect_signature () in
                             match uu____485 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____499 =
                                     let uu____503 =
                                       let uu____504 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____504 in
                                     [uu____503] in
                                   let uu____505 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____499
                                     uu____505 in
                                 let expected_k =
                                   let uu____511 =
                                     let uu____515 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____516 =
                                       let uu____518 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____519 =
                                         let uu____521 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____522 =
                                           let uu____524 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____525 =
                                             let uu____527 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____527] in
                                           uu____524 :: uu____525 in
                                         uu____521 :: uu____522 in
                                       uu____518 :: uu____519 in
                                     uu____515 :: uu____516 in
                                   let uu____528 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____511
                                     uu____528 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____533 =
                                 let uu____534 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____534
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____533 in
                             let expected_k =
                               let uu____542 =
                                 let uu____546 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____547 =
                                   let uu____549 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____550 =
                                     let uu____552 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____553 =
                                       let uu____555 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____555] in
                                     uu____552 :: uu____553 in
                                   uu____549 :: uu____550 in
                                 uu____546 :: uu____547 in
                               let uu____556 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____542 uu____556 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____563 =
                                 let uu____567 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____568 =
                                   let uu____570 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____570] in
                                 uu____567 :: uu____568 in
                               let uu____571 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____563 uu____571 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____575 = FStar_Syntax_Util.type_u () in
                             match uu____575 with
                             | (t,uu____579) ->
                                 let expected_k =
                                   let uu____583 =
                                     let uu____587 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____588 =
                                       let uu____590 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____591 =
                                         let uu____593 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____593] in
                                       uu____590 :: uu____591 in
                                     uu____587 :: uu____588 in
                                   let uu____594 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____583
                                     uu____594 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____599 =
                                 let uu____600 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____600
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____599 in
                             let b_wp_a =
                               let uu____608 =
                                 let uu____612 =
                                   let uu____613 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____613 in
                                 [uu____612] in
                               let uu____614 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____608 uu____614 in
                             let expected_k =
                               let uu____620 =
                                 let uu____624 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____625 =
                                   let uu____627 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____628 =
                                     let uu____630 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____630] in
                                   uu____627 :: uu____628 in
                                 uu____624 :: uu____625 in
                               let uu____631 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____620 uu____631 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____638 =
                                 let uu____642 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____643 =
                                   let uu____645 =
                                     let uu____646 =
                                       let uu____647 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____647
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____646 in
                                   let uu____652 =
                                     let uu____654 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____654] in
                                   uu____645 :: uu____652 in
                                 uu____642 :: uu____643 in
                               let uu____655 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____638 uu____655 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____662 =
                                 let uu____666 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____667 =
                                   let uu____669 =
                                     let uu____670 =
                                       let uu____671 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____671
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____670 in
                                   let uu____676 =
                                     let uu____678 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____678] in
                                   uu____669 :: uu____676 in
                                 uu____666 :: uu____667 in
                               let uu____679 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____662 uu____679 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____686 =
                                 let uu____690 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____690] in
                               let uu____691 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____686 uu____691 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____695 = FStar_Syntax_Util.type_u () in
                             match uu____695 with
                             | (t,uu____699) ->
                                 let expected_k =
                                   let uu____703 =
                                     let uu____707 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____708 =
                                       let uu____710 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____710] in
                                     uu____707 :: uu____708 in
                                   let uu____711 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____703
                                     uu____711 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____714 =
                             let uu____720 =
                               let uu____721 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____721.FStar_Syntax_Syntax.n in
                             match uu____720 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____730 ->
                                 let repr =
                                   let uu____732 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____732 with
                                   | (t,uu____736) ->
                                       let expected_k =
                                         let uu____740 =
                                           let uu____744 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____745 =
                                             let uu____747 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____747] in
                                           uu____744 :: uu____745 in
                                         let uu____748 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____740
                                           uu____748 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____761 =
                                     let uu____764 =
                                       let uu____765 =
                                         let uu____775 =
                                           let uu____777 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____778 =
                                             let uu____780 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____780] in
                                           uu____777 :: uu____778 in
                                         (repr1, uu____775) in
                                       FStar_Syntax_Syntax.Tm_app uu____765 in
                                     FStar_Syntax_Syntax.mk uu____764 in
                                   uu____761 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____799 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____799 wp in
                                 let destruct_repr t =
                                   let uu____810 =
                                     let uu____811 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____811.FStar_Syntax_Syntax.n in
                                   match uu____810 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____820,(t1,uu____822)::(wp,uu____824)::[])
                                       -> (t1, wp)
                                   | uu____858 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____867 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____867
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____868 = fresh_effect_signature () in
                                   match uu____868 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____882 =
                                           let uu____886 =
                                             let uu____887 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____887 in
                                           [uu____886] in
                                         let uu____888 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____882
                                           uu____888 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____894 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____894 in
                                       let wp_g_x =
                                         let uu____898 =
                                           let uu____899 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____900 =
                                             let uu____901 =
                                               let uu____902 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____902 in
                                             [uu____901] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____899 uu____900 in
                                         uu____898 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____913 =
                                             let uu____914 =
                                               let uu____915 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____915
                                                 FStar_Pervasives.snd in
                                             let uu____920 =
                                               let uu____921 =
                                                 let uu____923 =
                                                   let uu____925 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____926 =
                                                     let uu____928 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____929 =
                                                       let uu____931 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____932 =
                                                         let uu____934 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____934] in
                                                       uu____931 :: uu____932 in
                                                     uu____928 :: uu____929 in
                                                   uu____925 :: uu____926 in
                                                 r :: uu____923 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____921 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____914 uu____920 in
                                           uu____913 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____942 =
                                           let uu____946 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____947 =
                                             let uu____949 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____950 =
                                               let uu____952 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____953 =
                                                 let uu____955 =
                                                   let uu____956 =
                                                     let uu____957 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____957 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____956 in
                                                 let uu____958 =
                                                   let uu____960 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____961 =
                                                     let uu____963 =
                                                       let uu____964 =
                                                         let uu____965 =
                                                           let uu____969 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____969] in
                                                         let uu____970 =
                                                           let uu____973 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____973 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____965
                                                           uu____970 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____964 in
                                                     [uu____963] in
                                                   uu____960 :: uu____961 in
                                                 uu____955 :: uu____958 in
                                               uu____952 :: uu____953 in
                                             uu____949 :: uu____950 in
                                           uu____946 :: uu____947 in
                                         let uu____974 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____942
                                           uu____974 in
                                       let uu____977 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____977 with
                                        | (expected_k1,uu____982,uu____983)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___96_987 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___96_987.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___96_987.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___96_987.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___96_987.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___96_987.FStar_TypeChecker_Env.is_native_tactic)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____994 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____994 in
                                   let res =
                                     let wp =
                                       let uu____1001 =
                                         let uu____1002 =
                                           let uu____1003 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1003
                                             FStar_Pervasives.snd in
                                         let uu____1008 =
                                           let uu____1009 =
                                             let uu____1011 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1012 =
                                               let uu____1014 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1014] in
                                             uu____1011 :: uu____1012 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1009 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1002 uu____1008 in
                                       uu____1001 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1022 =
                                       let uu____1026 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1027 =
                                         let uu____1029 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1029] in
                                       uu____1026 :: uu____1027 in
                                     let uu____1030 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1022
                                       uu____1030 in
                                   let uu____1033 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1033 with
                                   | (expected_k1,uu____1041,uu____1042) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1045 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1045 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1057 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1071 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1071 with
                                     | (act_typ,uu____1076,g_t) ->
                                         let env' =
                                           let uu___97_1079 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___97_1079.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___97_1079.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___97_1079.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___97_1079.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___97_1079.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___97_1079.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___97_1079.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___97_1079.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___97_1079.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___97_1079.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___97_1079.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___97_1079.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___97_1079.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___97_1079.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___97_1079.FStar_TypeChecker_Env.is_native_tactic)
                                           } in
                                         ((let uu____1081 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1081
                                           then
                                             let uu____1082 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1083 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1082 uu____1083
                                           else ());
                                          (let uu____1085 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1085 with
                                           | (act_defn,uu____1090,g_a) ->
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
                                               let uu____1094 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1112 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1112 with
                                                      | (bs1,uu____1118) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1125 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1125 in
                                                          let uu____1128 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1128
                                                           with
                                                           | (k1,uu____1135,g)
                                                               -> (k1, g)))
                                                 | uu____1137 ->
                                                     let uu____1138 =
                                                       let uu____1139 =
                                                         let uu____1142 =
                                                           let uu____1143 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1144 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1143
                                                             uu____1144 in
                                                         (uu____1142,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1139 in
                                                     raise uu____1138 in
                                               (match uu____1094 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1151 =
                                                        let uu____1152 =
                                                          let uu____1153 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1153 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1152 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1151);
                                                     (let act_typ2 =
                                                        let uu____1157 =
                                                          let uu____1158 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1158.FStar_Syntax_Syntax.n in
                                                        match uu____1157 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1175 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1175
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1182
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1182
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1202
                                                                    =
                                                                    let uu____1203
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1203] in
                                                                    let uu____1204
                                                                    =
                                                                    let uu____1210
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1210] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1202;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1204;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1211
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1211))
                                                        | uu____1214 ->
                                                            failwith "" in
                                                      let uu____1217 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1217 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___98_1223 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___98_1223.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___98_1223.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___98_1223.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____714 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1239 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1239 in
                               let uu____1242 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1242 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1248 =
                                        let uu____1251 =
                                          let uu____1252 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1252.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1251) in
                                      match uu____1248 with
                                      | ([],uu____1255) -> t1
                                      | (uu____1261,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1262,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1274 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1285 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1285 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1290 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1291 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1291))
                                           && (m <> n1) in
                                       if uu____1290
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1300 =
                                           let uu____1301 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1302 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1301 uu____1302 in
                                         failwith uu____1300
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1308 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1308 with
                                      | (univs2,defn) ->
                                          let uu____1313 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1313 with
                                           | (univs',typ) ->
                                               let uu___99_1319 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___99_1319.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___99_1319.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___99_1319.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___100_1322 = ed2 in
                                      let uu____1323 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1324 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1325 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1326 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1327 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1328 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1329 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1330 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1331 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1332 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1333 =
                                        let uu____1334 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1334 in
                                      let uu____1340 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1341 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1342 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___100_1322.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___100_1322.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1323;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1324;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1325;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1326;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1327;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1328;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1329;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1330;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1331;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1332;
                                        FStar_Syntax_Syntax.repr = uu____1333;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1340;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1341;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1342
                                      } in
                                    ((let uu____1345 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1345
                                      then
                                        let uu____1346 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1346
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
      let uu____1350 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1350 with
      | (effect_binders_un,signature_un) ->
          let uu____1360 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1360 with
           | (effect_binders,env1,uu____1371) ->
               let uu____1372 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1372 with
                | (signature,uu____1381) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1390  ->
                           match uu____1390 with
                           | (bv,qual) ->
                               let uu____1397 =
                                 let uu___101_1398 = bv in
                                 let uu____1399 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___101_1398.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___101_1398.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1399
                                 } in
                               (uu____1397, qual)) effect_binders in
                    let uu____1402 =
                      let uu____1407 =
                        let uu____1408 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1408.FStar_Syntax_Syntax.n in
                      match uu____1407 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1416)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1431 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1402 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1448 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1448
                           then
                             let uu____1449 =
                               let uu____1451 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1451 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1449
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1475 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1475 with
                           | (t2,comp,uu____1483) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1494 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1494 with
                          | (repr,_comp) ->
                              ((let uu____1507 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1507
                                then
                                  let uu____1508 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1508
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
                                  let uu____1514 =
                                    let uu____1515 =
                                      let uu____1516 =
                                        let uu____1526 =
                                          let uu____1530 =
                                            let uu____1533 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1534 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1533, uu____1534) in
                                          [uu____1530] in
                                        (wp_type1, uu____1526) in
                                      FStar_Syntax_Syntax.Tm_app uu____1516 in
                                    mk1 uu____1515 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1514 in
                                let effect_signature =
                                  let binders =
                                    let uu____1549 =
                                      let uu____1552 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1552) in
                                    let uu____1553 =
                                      let uu____1557 =
                                        let uu____1558 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1558
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1557] in
                                    uu____1549 :: uu____1553 in
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
                                  let uu____1601 = item in
                                  match uu____1601 with
                                  | (u_item,item1) ->
                                      let uu____1613 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1613 with
                                       | (item2,item_comp) ->
                                           ((let uu____1623 =
                                               let uu____1624 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1624 in
                                             if uu____1623
                                             then
                                               let uu____1625 =
                                                 let uu____1626 =
                                                   let uu____1627 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1628 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1627 uu____1628 in
                                                 FStar_Errors.Err uu____1626 in
                                               raise uu____1625
                                             else ());
                                            (let uu____1630 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1630 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1643 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1643 with
                                | (dmff_env1,uu____1656,bind_wp,bind_elab) ->
                                    let uu____1659 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1659 with
                                     | (dmff_env2,uu____1672,return_wp,return_elab)
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Syntax_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu____1679 =
                                             let uu____1680 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1680.FStar_Syntax_Syntax.n in
                                           match uu____1679 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1708 =
                                                 let uu____1716 =
                                                   let uu____1719 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1719 in
                                                 match uu____1716 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1753 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1708 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1775 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1775 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1786 =
                                                          let uu____1787 =
                                                            let uu____1797 =
                                                              let uu____1801
                                                                =
                                                                let uu____1804
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
                                                                let uu____1805
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1804,
                                                                  uu____1805) in
                                                              [uu____1801] in
                                                            (wp_type1,
                                                              uu____1797) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1787 in
                                                        mk1 uu____1786 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1813 =
                                                      let uu____1818 =
                                                        let uu____1819 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1819 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1818 in
                                                    (match uu____1813 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1832
                                                           =
                                                           let error_msg =
                                                             let uu____1834 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1834
                                                               (match what'
                                                                with
                                                                | None  ->
                                                                    "None"
                                                                | Some rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some rc ->
                                                               (if
                                                                  Prims.op_Negation
                                                                    (
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                then fail ()
                                                                else ();
                                                                (let uu____1840
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0 in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    Some g'
                                                                    ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    None  ->
                                                                    fail ()) in
                                                                 FStar_All.pipe_right
                                                                   uu____1840
                                                                   FStar_Pervasives.ignore)));
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
                                                             let uu____1860 =
                                                               let uu____1861
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1862
                                                                 =
                                                                 let uu____1863
                                                                   =
                                                                   let uu____1867
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1867,
                                                                    None) in
                                                                 [uu____1863] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1861
                                                                 uu____1862 in
                                                             uu____1860 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1883 =
                                                             let uu____1884 =
                                                               let uu____1888
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1888] in
                                                             b11 ::
                                                               uu____1884 in
                                                           let uu____1891 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1883
                                                             uu____1891
                                                             (Some rc_gtot)))))
                                           | uu____1892 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1894 =
                                             let uu____1895 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1895.FStar_Syntax_Syntax.n in
                                           match uu____1894 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1923 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1923
                                                 (Some rc_gtot)
                                           | uu____1930 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____1932 =
                                             let uu____1933 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____1933.FStar_Syntax_Syntax.n in
                                           match uu____1932 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____1952 =
                                                 let uu____1953 =
                                                   let uu____1955 =
                                                     let uu____1956 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____1956 in
                                                   [uu____1955] in
                                                 FStar_List.append uu____1953
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____1952 body what
                                           | uu____1957 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____1975 =
                                                let uu____1976 =
                                                  let uu____1977 =
                                                    let uu____1987 =
                                                      let uu____1988 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____1988 in
                                                    (t, uu____1987) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____1977 in
                                                mk1 uu____1976 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____1975) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2011 = f a2 in
                                               [uu____2011]
                                           | x::xs ->
                                               let uu____2015 =
                                                 apply_last1 f xs in
                                               x :: uu____2015 in
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
                                           let uu____2030 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2030 with
                                           | Some (_us,_t) ->
                                               ((let uu____2047 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2047
                                                 then
                                                   let uu____2048 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2048
                                                 else ());
                                                (let uu____2050 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2050))
                                           | None  ->
                                               let uu____2055 =
                                                 let uu____2058 = mk_lid name in
                                                 let uu____2059 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2058 uu____2059 in
                                               (match uu____2055 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2063 =
                                                        let uu____2065 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2065 in
                                                      FStar_ST.write sigelts
                                                        uu____2063);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2076 =
                                             let uu____2078 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2079 =
                                               FStar_ST.read sigelts in
                                             uu____2078 :: uu____2079 in
                                           FStar_ST.write sigelts uu____2076);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2089 =
                                              let uu____2091 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2092 =
                                                FStar_ST.read sigelts in
                                              uu____2091 :: uu____2092 in
                                            FStar_ST.write sigelts uu____2089);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2102 =
                                               let uu____2104 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____2105 =
                                                 FStar_ST.read sigelts in
                                               uu____2104 :: uu____2105 in
                                             FStar_ST.write sigelts
                                               uu____2102);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2115 =
                                                let uu____2117 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____2118 =
                                                  FStar_ST.read sigelts in
                                                uu____2117 :: uu____2118 in
                                              FStar_ST.write sigelts
                                                uu____2115);
                                             (let uu____2126 =
                                                FStar_List.fold_left
                                                  (fun uu____2133  ->
                                                     fun action  ->
                                                       match uu____2133 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2146 =
                                                             let uu____2150 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2150
                                                               params_un in
                                                           (match uu____2146
                                                            with
                                                            | (action_params,env',uu____2156)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2165
                                                                     ->
                                                                    match uu____2165
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2172
                                                                    =
                                                                    let uu___102_2173
                                                                    = bv in
                                                                    let uu____2174
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___102_2173.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___102_2173.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2174
                                                                    } in
                                                                    (uu____2172,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2178
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2178
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
                                                                    uu____2199
                                                                    ->
                                                                    let uu____2200
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2200 in
                                                                    ((
                                                                    let uu____2204
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2204
                                                                    then
                                                                    let uu____2205
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2206
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2207
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2208
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2205
                                                                    uu____2206
                                                                    uu____2207
                                                                    uu____2208
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
                                                                    let uu____2212
                                                                    =
                                                                    let uu____2214
                                                                    =
                                                                    let uu___103_2215
                                                                    = action in
                                                                    let uu____2216
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2217
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___103_2215.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___103_2215.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___103_2215.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2216;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2217
                                                                    } in
                                                                    uu____2214
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2212))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2126 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2237 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2238 =
                                                        let uu____2240 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2240] in
                                                      uu____2237 ::
                                                        uu____2238 in
                                                    let uu____2241 =
                                                      let uu____2242 =
                                                        let uu____2243 =
                                                          let uu____2244 =
                                                            let uu____2254 =
                                                              let uu____2258
                                                                =
                                                                let uu____2261
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2262
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2261,
                                                                  uu____2262) in
                                                              [uu____2258] in
                                                            (repr,
                                                              uu____2254) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2244 in
                                                        mk1 uu____2243 in
                                                      let uu____2270 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2242
                                                        uu____2270 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2241 None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2273 =
                                                    let uu____2278 =
                                                      let uu____2279 =
                                                        let uu____2282 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2282 in
                                                      uu____2279.FStar_Syntax_Syntax.n in
                                                    match uu____2278 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2290)
                                                        ->
                                                        let uu____2307 =
                                                          let uu____2316 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2316
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2347 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2307
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2375 =
                                                               let uu____2376
                                                                 =
                                                                 let uu____2379
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2379 in
                                                               uu____2376.FStar_Syntax_Syntax.n in
                                                             (match uu____2375
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2396
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2396
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2405
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2416
                                                                     ->
                                                                    match uu____2416
                                                                    with
                                                                    | 
                                                                    (bv,uu____2420)
                                                                    ->
                                                                    let uu____2421
                                                                    =
                                                                    let uu____2422
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2422
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2421
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2405
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
                                                                    uu____2455
                                                                    ->
                                                                    let uu____2459
                                                                    =
                                                                    let uu____2460
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2460 in
                                                                    failwith
                                                                    uu____2459 in
                                                                    let uu____2463
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2466
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2463,
                                                                    uu____2466)))
                                                              | uu____2471 ->
                                                                  let uu____2472
                                                                    =
                                                                    let uu____2473
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2473 in
                                                                  failwith
                                                                    uu____2472))
                                                    | uu____2478 ->
                                                        let uu____2479 =
                                                          let uu____2480 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2480 in
                                                        failwith uu____2479 in
                                                  (match uu____2273 with
                                                   | (pre,post) ->
                                                       ((let uu____2497 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2499 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2501 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___104_2503
                                                             = ed in
                                                           let uu____2504 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2505 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2506 =
                                                             let uu____2507 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2507) in
                                                           let uu____2513 =
                                                             let uu____2514 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2514) in
                                                           let uu____2520 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2521 =
                                                             let uu____2522 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2522) in
                                                           let uu____2528 =
                                                             let uu____2529 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2529) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2504;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2505;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2506;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2513;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___104_2503.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2520;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2521;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2528;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2535 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2535
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2546
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2546
                                                               then
                                                                 let uu____2547
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2547
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
                                                                    let uu____2557
                                                                    =
                                                                    let uu____2559
                                                                    =
                                                                    let uu____2565
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2565) in
                                                                    Some
                                                                    uu____2559 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2557;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2576
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
                                                                    uu____2576
                                                                 else None in
                                                               let uu____2578
                                                                 =
                                                                 let uu____2580
                                                                   =
                                                                   let uu____2582
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2582 in
                                                                 FStar_List.append
                                                                   uu____2580
                                                                   sigelts' in
                                                               (uu____2578,
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
                (lex_t1,[],[],t,uu____2605,uu____2606);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2608;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2612);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2614;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2618);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2620;_}::[]
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
                let uu____2659 =
                  let uu____2662 =
                    let uu____2663 =
                      let uu____2668 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2668, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2663 in
                  FStar_Syntax_Syntax.mk uu____2662 in
                uu____2659 None r1 in
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
                  let uu____2688 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2688 in
                let hd1 =
                  let uu____2694 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2694 in
                let tl1 =
                  let uu____2696 =
                    let uu____2697 =
                      let uu____2700 =
                        let uu____2701 =
                          let uu____2706 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2706, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2701 in
                      FStar_Syntax_Syntax.mk uu____2700 in
                    uu____2697 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2696 in
                let res =
                  let uu____2719 =
                    let uu____2722 =
                      let uu____2723 =
                        let uu____2728 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2728,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2723 in
                    FStar_Syntax_Syntax.mk uu____2722 in
                  uu____2719 None r2 in
                let uu____2738 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2738 in
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
              let uu____2760 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2760;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2763 ->
              let uu____2765 =
                let uu____2766 =
                  let uu____2767 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2767 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2766 in
              failwith uu____2765
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
            let uu____2777 = FStar_Syntax_Util.type_u () in
            match uu____2777 with
            | (k,uu____2781) ->
                let phi1 =
                  let uu____2783 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2783
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
          let uu____2793 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2793 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2812 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2812 FStar_List.flatten in
              ((let uu____2820 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2820
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
                          let uu____2826 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2832,uu____2833,uu____2834,uu____2835,uu____2836)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2841 -> failwith "Impossible!" in
                          match uu____2826 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2850 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2854,uu____2855,uu____2856,uu____2857,uu____2858)
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
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____2888;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2906 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____2919 ->
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
           let uu____2949 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____2949 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____2974 = FStar_Options.set_options t s in
             match uu____2974 with
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
                ((let uu____2991 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____2991 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____2997 = cps_and_elaborate env1 ne in
           (match uu____2997 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___105_3018 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___105_3018.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_3018.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_3018.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___106_3019 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___106_3019.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___106_3019.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___106_3019.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___107_3025 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___107_3025.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___107_3025.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___107_3025.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____3031 =
             let uu____3036 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3036 in
           (match uu____3031 with
            | (a,wp_a_src) ->
                let uu____3047 =
                  let uu____3052 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3052 in
                (match uu____3047 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3064 =
                         let uu____3066 =
                           let uu____3067 =
                             let uu____3072 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3072) in
                           FStar_Syntax_Syntax.NT uu____3067 in
                         [uu____3066] in
                       FStar_Syntax_Subst.subst uu____3064 wp_b_tgt in
                     let expected_k =
                       let uu____3076 =
                         let uu____3080 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3081 =
                           let uu____3083 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3083] in
                         uu____3080 :: uu____3081 in
                       let uu____3084 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3076 uu____3084 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3105 =
                           let uu____3106 =
                             let uu____3109 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3110 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3109, uu____3110) in
                           FStar_Errors.Error uu____3106 in
                         raise uu____3105 in
                       let uu____3113 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3113 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3132 =
                             let uu____3133 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3133 in
                           if uu____3132
                           then no_reify eff_name
                           else
                             (let uu____3138 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3139 =
                                let uu____3142 =
                                  let uu____3143 =
                                    let uu____3153 =
                                      let uu____3155 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3156 =
                                        let uu____3158 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3158] in
                                      uu____3155 :: uu____3156 in
                                    (repr, uu____3153) in
                                  FStar_Syntax_Syntax.Tm_app uu____3143 in
                                FStar_Syntax_Syntax.mk uu____3142 in
                              uu____3139 None uu____3138) in
                     let uu____3168 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3183,lift_wp)) ->
                           let uu____3196 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3196)
                       | (Some (what,lift),None ) ->
                           ((let uu____3211 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3211
                             then
                               let uu____3212 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3212
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3215 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3215 with
                             | (lift1,comp,uu____3224) ->
                                 let uu____3225 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3225 with
                                  | (uu____3232,lift_wp,lift_elab) ->
                                      let uu____3235 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3236 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3168 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___108_3259 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___108_3259.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___108_3259.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___108_3259.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___108_3259.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___108_3259.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___108_3259.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___108_3259.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___108_3259.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___108_3259.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___108_3259.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___108_3259.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___108_3259.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___108_3259.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___108_3259.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___108_3259.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___108_3259.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___108_3259.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___108_3259.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___108_3259.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___108_3259.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___108_3259.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___108_3259.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___108_3259.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___108_3259.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___108_3259.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___108_3259.FStar_TypeChecker_Env.is_native_tactic)
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3263,lift1) ->
                                let uu____3270 =
                                  let uu____3275 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3275 in
                                (match uu____3270 with
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
                                         let uu____3297 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3298 =
                                           let uu____3301 =
                                             let uu____3302 =
                                               let uu____3312 =
                                                 let uu____3314 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3315 =
                                                   let uu____3317 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3317] in
                                                 uu____3314 :: uu____3315 in
                                               (lift_wp1, uu____3312) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3302 in
                                           FStar_Syntax_Syntax.mk uu____3301 in
                                         uu____3298 None uu____3297 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3330 =
                                         let uu____3334 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3335 =
                                           let uu____3337 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3338 =
                                             let uu____3340 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3340] in
                                           uu____3337 :: uu____3338 in
                                         uu____3334 :: uu____3335 in
                                       let uu____3341 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3330
                                         uu____3341 in
                                     let uu____3344 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3344 with
                                      | (expected_k2,uu____3350,uu____3351)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
                            let uu___109_3354 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___109_3354.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___109_3354.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___110_3356 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___110_3356.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___110_3356.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___110_3356.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3369 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3369 with
            | (tps1,c1) ->
                let uu____3378 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3378 with
                 | (tps2,env3,us) ->
                     let uu____3389 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3389 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3403 =
                              let uu____3404 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3404 in
                            match uu____3403 with
                            | (uvs1,t) ->
                                let uu____3417 =
                                  let uu____3425 =
                                    let uu____3428 =
                                      let uu____3429 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3429.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3428) in
                                  match uu____3425 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3439,c4)) -> ([], c4)
                                  | (uu____3463,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3481 -> failwith "Impossible" in
                                (match uu____3417 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3510 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3510 with
                                         | (uu____3513,t1) ->
                                             let uu____3515 =
                                               let uu____3516 =
                                                 let uu____3519 =
                                                   let uu____3520 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3521 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3524 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3520 uu____3521
                                                     uu____3524 in
                                                 (uu____3519, r) in
                                               FStar_Errors.Error uu____3516 in
                                             raise uu____3515)
                                      else ();
                                      (let se1 =
                                         let uu___111_3527 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___111_3527.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___111_3527.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___111_3527.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3537,uu____3538,uu____3539) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3541  ->
                   match uu___85_3541 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3542 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3545,uu____3546,uu____3547) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3553  ->
                   match uu___85_3553 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3554 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3561 =
             if uvs = []
             then
               let uu____3562 =
                 let uu____3563 = FStar_Syntax_Util.type_u () in
                 fst uu____3563 in
               check_and_gen env2 t uu____3562
             else
               (let uu____3567 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3567 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3573 =
                        let uu____3574 = FStar_Syntax_Util.type_u () in
                        fst uu____3574 in
                      tc_check_trivial_guard env2 t1 uu____3573 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3578 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3578)) in
           (match uu____3561 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___112_3588 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___112_3588.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___112_3588.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___112_3588.FStar_Syntax_Syntax.sigmeta)
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
           let uu____3600 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3600 with
            | (e1,c,g1) ->
                let uu____3611 =
                  let uu____3615 =
                    let uu____3617 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3617 in
                  let uu____3618 =
                    let uu____3621 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3621) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3615 uu____3618 in
                (match uu____3611 with
                 | (e2,uu____3631,g) ->
                     ((let uu____3634 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3634);
                      (let se1 =
                         let uu___113_3636 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___113_3636.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___113_3636.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___113_3636.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3672 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3672
                 then Some q
                 else
                   (let uu____3681 =
                      let uu____3682 =
                        let uu____3685 =
                          let uu____3686 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3687 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3688 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3686 uu____3687 uu____3688 in
                        (uu____3685, r) in
                      FStar_Errors.Error uu____3682 in
                    raise uu____3681) in
           let uu____3691 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3712  ->
                     fun lb  ->
                       match uu____3712 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3736 =
                             let uu____3742 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3742 with
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
                                   | uu____3794 ->
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
                                  (let uu____3802 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3802, quals_opt1))) in
                           (match uu____3736 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3691 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3855 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___86_3857  ->
                                match uu___86_3857 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____3858 -> false)) in
                      if uu____3855
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____3866 =
                    let uu____3869 =
                      let uu____3870 =
                        let uu____3878 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____3878) in
                      FStar_Syntax_Syntax.Tm_let uu____3870 in
                    FStar_Syntax_Syntax.mk uu____3869 in
                  uu____3866 None r in
                let uu____3900 =
                  let uu____3906 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___114_3910 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___114_3910.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___114_3910.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___114_3910.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___114_3910.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___114_3910.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___114_3910.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___114_3910.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___114_3910.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___114_3910.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___114_3910.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___114_3910.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___114_3910.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___114_3910.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___114_3910.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___114_3910.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___114_3910.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___114_3910.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___114_3910.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___114_3910.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___114_3910.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___114_3910.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___114_3910.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___114_3910.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___114_3910.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___114_3910.FStar_TypeChecker_Env.is_native_tactic)
                       }) e in
                  match uu____3906 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3918;
                       FStar_Syntax_Syntax.pos = uu____3919;
                       FStar_Syntax_Syntax.vars = uu____3920;_},uu____3921,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3940,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____3945 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___87_3948  ->
                             match uu___87_3948 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____3950 =
                                   let uu____3951 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____3955 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____3955)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____3951 in
                                 if uu____3950
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
                      ((let uu___115_3964 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___115_3964.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___115_3964.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____3970 -> failwith "impossible" in
                (match uu____3900 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____3997 = log env2 in
                       if uu____3997
                       then
                         let uu____3998 =
                           let uu____3999 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4006 =
                                         let uu____4011 =
                                           let uu____4012 =
                                             let uu____4017 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4017.FStar_Syntax_Syntax.fv_name in
                                           uu____4012.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4011 in
                                       match uu____4006 with
                                       | None  -> true
                                       | uu____4024 -> false in
                                     if should_log
                                     then
                                       let uu____4029 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4030 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4029 uu____4030
                                     else "")) in
                           FStar_All.pipe_right uu____3999
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____3998
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4054 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____4054 with
                              | (bs1,c1) ->
                                  let uu____4059 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____4059
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4069 =
                                            let uu____4070 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____4070.FStar_Syntax_Syntax.n in
                                          (match uu____4069 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4089 =
                                                 let uu____4090 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____4090.FStar_Syntax_Syntax.n in
                                               (match uu____4089 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4100 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4100 in
                                                    let uu____4101 =
                                                      let uu____4102 =
                                                        let uu____4103 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4103 args in
                                                      uu____4102 None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4101 u
                                                | uu____4108 -> c1)
                                           | uu____4109 -> c1)
                                      | uu____4110 -> c1 in
                                    let uu___116_4111 = t1 in
                                    let uu____4112 =
                                      let uu____4113 =
                                        let uu____4121 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4121) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4113 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4112;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___116_4111.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___116_4111.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___116_4111.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4143 =
                               let uu____4144 = FStar_Syntax_Subst.compress h in
                               uu____4144.FStar_Syntax_Syntax.n in
                             (match uu____4143 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4154 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4154 in
                                  let uu____4155 =
                                    let uu____4156 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4156
                                      args in
                                  uu____4155 None t1.FStar_Syntax_Syntax.pos
                              | uu____4161 -> t1)
                         | uu____4162 -> t1 in
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
                           let uu____4189 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4189 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4198 =
                                  FStar_Syntax_Syntax.bv_to_name (fst x) in
                                (uu____4198, (snd x))) bs in
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
                           let uu____4230 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4230 in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let uu___117_4235 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___118_4242 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___118_4242.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___118_4242.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___118_4242.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___118_4242.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids, attrs));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_4235.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_4235.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_4235.FStar_Syntax_Syntax.sigmeta)
                         } in
                       let tactic_decls =
                         match snd lbs1 with
                         | hd1::[] ->
                             let uu____4252 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4252 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4272 =
                                    let uu____4273 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4273.FStar_Syntax_Syntax.n in
                                  (match uu____4272 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4297 =
                                           let uu____4302 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4302.FStar_Syntax_Syntax.fv_name in
                                         uu____4297.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4307 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4307 in
                                       let uu____4308 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____4309 =
                                              let uu____4310 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4310 in
                                            Prims.op_Negation uu____4309) in
                                       if uu____4308
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl (fst lbs1)
                                             hd1 bs assm_lid comp in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4333 -> None))
                         | uu____4336 -> None in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4349 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4349
                             then
                               let uu____4350 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4351 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4350 uu____4351
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
             (fun uu___88_4382  ->
                match uu___88_4382 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4383 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4389) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4393 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4398 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4401 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4414 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4427) ->
          let uu____4432 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4432
          then
            let for_export_bundle se1 uu____4451 =
              match uu____4451 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4474,uu____4475) ->
                       let dec =
                         let uu___119_4481 = se1 in
                         let uu____4482 =
                           let uu____4483 =
                             let uu____4487 =
                               let uu____4490 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4490 in
                             (l, us, uu____4487) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4483 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4482;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___119_4481.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___119_4481.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4500,uu____4501,uu____4502) ->
                       let dec =
                         let uu___120_4506 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___120_4506.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___120_4506.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4509 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4521,uu____4522) ->
          let uu____4523 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4523 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4536 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4536
          then
            ([(let uu___121_4544 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___121_4544.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___121_4544.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4546 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___89_4548  ->
                       match uu___89_4548 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4549 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4552 -> true
                       | uu____4553 -> false)) in
             if uu____4546 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4563 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4566 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4569 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4572 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4575 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4585,uu____4586)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4602 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4602
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4623) ->
          let uu____4628 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4628
          then
            let uu____4633 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___122_4639 = se in
                      let uu____4640 =
                        let uu____4641 =
                          let uu____4645 =
                            let uu____4646 =
                              let uu____4651 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4651.FStar_Syntax_Syntax.fv_name in
                            uu____4646.FStar_Syntax_Syntax.v in
                          (uu____4645, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4641 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4640;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___122_4639.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___122_4639.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4633, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4669 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4678 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4687 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4690 = FStar_Options.using_facts_from () in
                 match uu____4690 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4702 =
                         let uu____4707 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4707 [([], false)] in
                       [uu____4702] in
                     let uu___123_4735 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___123_4735.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___123_4735.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___123_4735.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___123_4735.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___123_4735.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___123_4735.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___123_4735.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___123_4735.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___123_4735.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___123_4735.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___123_4735.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___123_4735.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___123_4735.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___123_4735.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___123_4735.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___123_4735.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___123_4735.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___123_4735.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___123_4735.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___123_4735.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___123_4735.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___123_4735.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___123_4735.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___123_4735.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___123_4735.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___123_4735.FStar_TypeChecker_Env.is_native_tactic)
                     }
                 | None  -> env))
           | uu____4737 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4738 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4744 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4744) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4745,uu____4746,uu____4747) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4749  ->
                  match uu___90_4749 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4750 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4751,uu____4752,uu____4753) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4759  ->
                  match uu___90_4759 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4760 -> false))
          -> env
      | uu____4761 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4797 se =
        match uu____4797 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4827 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4827
              then
                let uu____4828 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4828
              else ());
             (let uu____4830 = tc_decl env1 se in
              match uu____4830 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____4856 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____4856
                    then
                      let uu____4857 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4860 =
                                 let uu____4861 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4861 "\n" in
                               Prims.strcat s uu____4860) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4857
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4865 =
                      let accum_exports_hidden uu____4883 se1 =
                        match uu____4883 with
                        | (exports1,hidden1) ->
                            let uu____4899 = for_export hidden1 se1 in
                            (match uu____4899 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____4865 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____4949 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4949 with
      | (ses1,exports,env1,uu____4975) ->
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
      (let uu____5000 = FStar_Options.debug_any () in
       if uu____5000
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
         let uu___124_5006 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_5006.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_5006.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_5006.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_5006.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_5006.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_5006.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_5006.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_5006.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_5006.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_5006.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_5006.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_5006.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___124_5006.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___124_5006.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_5006.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_5006.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___124_5006.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_5006.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___124_5006.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_5006.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___124_5006.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___124_5006.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___124_5006.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___124_5006.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___124_5006.FStar_TypeChecker_Env.is_native_tactic)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____5009 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5009 with
        | (ses,exports,env3) ->
            ((let uu___125_5027 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___125_5027.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___125_5027.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___125_5027.FStar_Syntax_Syntax.is_interface)
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
        let uu____5043 = tc_decls env decls in
        match uu____5043 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___126_5061 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___126_5061.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___126_5061.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___126_5061.FStar_Syntax_Syntax.is_interface)
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
          let uu___127_5075 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___127_5075.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___127_5075.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___127_5075.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___127_5075.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___127_5075.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___127_5075.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___127_5075.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___127_5075.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___127_5075.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___127_5075.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___127_5075.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___127_5075.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___127_5075.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___127_5075.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___127_5075.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___127_5075.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___127_5075.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___127_5075.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___127_5075.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___127_5075.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___127_5075.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___127_5075.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___127_5075.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___127_5075.FStar_TypeChecker_Env.is_native_tactic)
          } in
        let check_term lid univs1 t =
          let uu____5086 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5086 with
          | (univs2,t1) ->
              ((let uu____5092 =
                  let uu____5093 =
                    let uu____5096 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5096 in
                  FStar_All.pipe_left uu____5093
                    (FStar_Options.Other "Exports") in
                if uu____5092
                then
                  let uu____5097 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5098 =
                    let uu____5099 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5099
                      (FStar_String.concat ", ") in
                  let uu____5104 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5097 uu____5098 uu____5104
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5107 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5107 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5125 =
             let uu____5126 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5127 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5126 uu____5127 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5125);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5134) ->
              let uu____5139 =
                let uu____5140 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5140 in
              if uu____5139
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5148,uu____5149) ->
              let t =
                let uu____5157 =
                  let uu____5160 =
                    let uu____5161 =
                      let uu____5169 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5169) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5161 in
                  FStar_Syntax_Syntax.mk uu____5160 in
                uu____5157 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5181,uu____5182,uu____5183) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5189 =
                let uu____5190 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5190 in
              if uu____5189 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5193,lbs),uu____5195,uu____5196) ->
              let uu____5206 =
                let uu____5207 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5207 in
              if uu____5206
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
              let uu____5224 =
                let uu____5225 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5225 in
              if uu____5224
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5239 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5240 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5243 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5244 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5245 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5246 -> () in
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
          let uu___128_5260 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___128_5260.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___128_5260.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5263 =
           let uu____5264 = FStar_Options.lax () in
           Prims.op_Negation uu____5264 in
         if uu____5263 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5270 =
           let uu____5271 = FStar_Options.interactive () in
           Prims.op_Negation uu____5271 in
         if uu____5270
         then
           let uu____5272 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5272 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5282 = tc_partial_modul env modul in
      match uu____5282 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5303 = FStar_Options.debug_any () in
       if uu____5303
       then
         let uu____5304 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5304
       else ());
      (let env1 =
         let uu___129_5308 = env in
         let uu____5309 =
           let uu____5310 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5310 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___129_5308.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___129_5308.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___129_5308.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___129_5308.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___129_5308.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___129_5308.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___129_5308.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___129_5308.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___129_5308.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___129_5308.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___129_5308.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___129_5308.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___129_5308.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___129_5308.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___129_5308.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___129_5308.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___129_5308.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___129_5308.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5309;
           FStar_TypeChecker_Env.lax_universes =
             (uu___129_5308.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___129_5308.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___129_5308.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___129_5308.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___129_5308.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___129_5308.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___129_5308.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___129_5308.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____5311 = tc_modul env1 m in
       match uu____5311 with
       | (m1,env2) ->
           ((let uu____5319 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5319
             then
               let uu____5320 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5320
             else ());
            (let uu____5323 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5323
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
                       let uu____5350 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5350 with
                       | (univnames1,e) ->
                           let uu___130_5355 = lb in
                           let uu____5356 =
                             let uu____5359 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5359 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___130_5355.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___130_5355.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___130_5355.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___130_5355.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5356
                           } in
                     let uu___131_5360 = se in
                     let uu____5361 =
                       let uu____5362 =
                         let uu____5368 =
                           let uu____5372 = FStar_List.map update lbs in
                           (b, uu____5372) in
                         (uu____5368, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5362 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5361;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___131_5360.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___131_5360.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___131_5360.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5380 -> se in
               let normalized_module =
                 let uu___132_5382 = m1 in
                 let uu____5383 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___132_5382.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5383;
                   FStar_Syntax_Syntax.exports =
                     (uu___132_5382.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___132_5382.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5384 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5384
             else ());
            (m1, env2)))