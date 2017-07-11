open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____9 = FStar_Options.reuse_hint_for () in
      match uu____9 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____13 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____13 l in
          let uu___91_14 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___91_14.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___91_14.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___91_14.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___91_14.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___91_14.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___91_14.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___91_14.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___91_14.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___91_14.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___91_14.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___91_14.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___91_14.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___91_14.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___91_14.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___91_14.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___91_14.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___91_14.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___91_14.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___91_14.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___91_14.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___91_14.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___91_14.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___91_14.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___91_14.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___91_14.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___91_14.FStar_TypeChecker_Env.is_native_tactic)
          }
      | FStar_Pervasives_Native.None  ->
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
          let uu___92_26 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___92_26.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___92_26.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___92_26.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___92_26.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___92_26.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___92_26.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___92_26.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___92_26.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___92_26.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___92_26.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___92_26.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___92_26.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___92_26.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___92_26.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___92_26.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___92_26.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___92_26.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___92_26.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___92_26.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___92_26.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___92_26.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___92_26.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___92_26.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___92_26.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___92_26.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___92_26.FStar_TypeChecker_Env.is_native_tactic)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____34 =
         let uu____35 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____35 in
       Prims.op_Negation uu____34)
let is_native_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____49) ->
            let uu____52 =
              let uu____53 = FStar_Syntax_Subst.compress h' in
              uu____53.FStar_Syntax_Syntax.n in
            (match uu____52 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> env.FStar_TypeChecker_Env.is_native_tactic tac_lid
             | uu____56 -> false)
        | uu____57 -> false
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____70 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____70 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____91 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____91
         then
           let uu____92 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____92
         else ());
        (let uu____94 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____94 with
         | (t',uu____99,uu____100) ->
             ((let uu____102 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____102
               then
                 let uu____103 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____103
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
        let uu____117 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____117
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____143 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____143)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____166 =
          let uu____167 =
            let uu____168 =
              let uu____171 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____171, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____168 in
          raise uu____167 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____194)::(wp,uu____196)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____204 -> fail ())
        | uu____205 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____216 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____216 with
      | (effect_params_un,signature_un,opening) ->
          let uu____223 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____223 with
           | (effect_params,env,uu____229) ->
               let uu____230 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____230 with
                | (signature,uu____234) ->
                    let ed1 =
                      let uu___93_236 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___93_236.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___93_236.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___93_236.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___93_236.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___93_236.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___93_236.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___93_236.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___93_236.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___93_236.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___93_236.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___93_236.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___93_236.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___93_236.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___93_236.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___93_236.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___93_236.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___93_236.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____240 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening
                                (FStar_Pervasives_Native.snd ts) in
                            ([], t1) in
                          let uu___94_259 = ed1 in
                          let uu____260 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____261 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____262 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____263 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____264 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____265 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____266 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____267 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____268 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____269 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____270 =
                            let uu____271 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            FStar_Pervasives_Native.snd uu____271 in
                          let uu____277 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____278 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____279 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___95_286 = a in
                                 let uu____287 =
                                   let uu____288 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   FStar_Pervasives_Native.snd uu____288 in
                                 let uu____294 =
                                   let uu____295 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   FStar_Pervasives_Native.snd uu____295 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___95_286.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___95_286.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___95_286.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___95_286.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____287;
                                   FStar_Syntax_Syntax.action_typ = uu____294
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___94_259.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___94_259.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___94_259.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___94_259.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___94_259.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____260;
                            FStar_Syntax_Syntax.bind_wp = uu____261;
                            FStar_Syntax_Syntax.if_then_else = uu____262;
                            FStar_Syntax_Syntax.ite_wp = uu____263;
                            FStar_Syntax_Syntax.stronger = uu____264;
                            FStar_Syntax_Syntax.close_wp = uu____265;
                            FStar_Syntax_Syntax.assert_p = uu____266;
                            FStar_Syntax_Syntax.assume_p = uu____267;
                            FStar_Syntax_Syntax.null_wp = uu____268;
                            FStar_Syntax_Syntax.trivial = uu____269;
                            FStar_Syntax_Syntax.repr = uu____270;
                            FStar_Syntax_Syntax.return_repr = uu____277;
                            FStar_Syntax_Syntax.bind_repr = uu____278;
                            FStar_Syntax_Syntax.actions = uu____279
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____321 =
                          let uu____322 =
                            let uu____325 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____325, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____322 in
                        raise uu____321 in
                      let uu____329 =
                        let uu____330 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____330.FStar_Syntax_Syntax.n in
                      match uu____329 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____350)::(wp,uu____352)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____360 -> fail signature1)
                      | uu____361 -> fail signature1 in
                    let uu____362 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____362 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____376 =
                           let uu____377 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____377 with
                           | (signature1,uu____384) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____386 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____386 in
                         ((let uu____388 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____388
                           then
                             let uu____389 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____390 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____391 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____392 =
                               let uu____393 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____393 in
                             let uu____394 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____389 uu____390 uu____391 uu____392
                               uu____394
                           else ());
                          (let check_and_gen' env2 uu____407 k =
                             match uu____407 with
                             | (uu____412,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____419 =
                                 let uu____423 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____424 =
                                   let uu____426 =
                                     let uu____427 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____427 in
                                   [uu____426] in
                                 uu____423 :: uu____424 in
                               let uu____428 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____419 uu____428 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____431 = fresh_effect_signature () in
                             match uu____431 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____441 =
                                     let uu____445 =
                                       let uu____446 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____446 in
                                     [uu____445] in
                                   let uu____447 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____441
                                     uu____447 in
                                 let expected_k =
                                   let uu____451 =
                                     let uu____455 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____456 =
                                       let uu____458 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____459 =
                                         let uu____461 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____462 =
                                           let uu____464 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____465 =
                                             let uu____467 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____467] in
                                           uu____464 :: uu____465 in
                                         uu____461 :: uu____462 in
                                       uu____458 :: uu____459 in
                                     uu____455 :: uu____456 in
                                   let uu____468 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____451
                                     uu____468 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____472 =
                                 let uu____473 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____473
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____472 in
                             let expected_k =
                               let uu____480 =
                                 let uu____484 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____485 =
                                   let uu____487 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____488 =
                                     let uu____490 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____491 =
                                       let uu____493 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____493] in
                                     uu____490 :: uu____491 in
                                   uu____487 :: uu____488 in
                                 uu____484 :: uu____485 in
                               let uu____494 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____480 uu____494 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____499 =
                                 let uu____503 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____504 =
                                   let uu____506 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____506] in
                                 uu____503 :: uu____504 in
                               let uu____507 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____499 uu____507 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____510 = FStar_Syntax_Util.type_u () in
                             match uu____510 with
                             | (t,uu____514) ->
                                 let expected_k =
                                   let uu____517 =
                                     let uu____521 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____522 =
                                       let uu____524 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____525 =
                                         let uu____527 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____527] in
                                       uu____524 :: uu____525 in
                                     uu____521 :: uu____522 in
                                   let uu____528 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____517
                                     uu____528 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____532 =
                                 let uu____533 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____533
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____532 in
                             let b_wp_a =
                               let uu____540 =
                                 let uu____544 =
                                   let uu____545 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____545 in
                                 [uu____544] in
                               let uu____546 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____540 uu____546 in
                             let expected_k =
                               let uu____550 =
                                 let uu____554 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____555 =
                                   let uu____557 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____558 =
                                     let uu____560 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____560] in
                                   uu____557 :: uu____558 in
                                 uu____554 :: uu____555 in
                               let uu____561 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____550 uu____561 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____566 =
                                 let uu____570 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____571 =
                                   let uu____573 =
                                     let uu____574 =
                                       let uu____575 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____575
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____574 in
                                   let uu____580 =
                                     let uu____582 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____582] in
                                   uu____573 :: uu____580 in
                                 uu____570 :: uu____571 in
                               let uu____583 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____566 uu____583 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____588 =
                                 let uu____592 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____593 =
                                   let uu____595 =
                                     let uu____596 =
                                       let uu____597 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____597
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____596 in
                                   let uu____602 =
                                     let uu____604 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____604] in
                                   uu____595 :: uu____602 in
                                 uu____592 :: uu____593 in
                               let uu____605 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____588 uu____605 in
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
                             let uu____618 = FStar_Syntax_Util.type_u () in
                             match uu____618 with
                             | (t,uu____622) ->
                                 let expected_k =
                                   let uu____625 =
                                     let uu____629 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____630 =
                                       let uu____632 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____632] in
                                     uu____629 :: uu____630 in
                                   let uu____633 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____625
                                     uu____633 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____635 =
                             let uu____641 =
                               let uu____642 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____642.FStar_Syntax_Syntax.n in
                             match uu____641 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____650 ->
                                 let repr =
                                   let uu____652 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____652 with
                                   | (t,uu____656) ->
                                       let expected_k =
                                         let uu____659 =
                                           let uu____663 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____664 =
                                             let uu____666 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____666] in
                                           uu____663 :: uu____664 in
                                         let uu____667 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____659
                                           uu____667 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____678 =
                                     let uu____680 =
                                       let uu____681 =
                                         let uu____689 =
                                           let uu____691 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____692 =
                                             let uu____694 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____694] in
                                           uu____691 :: uu____692 in
                                         (repr1, uu____689) in
                                       FStar_Syntax_Syntax.Tm_app uu____681 in
                                     FStar_Syntax_Syntax.mk uu____680 in
                                   uu____678 FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____710 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____710 wp in
                                 let destruct_repr t =
                                   let uu____719 =
                                     let uu____720 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____720.FStar_Syntax_Syntax.n in
                                   match uu____719 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____726,(t1,uu____728)::(wp,uu____730)::[])
                                       -> (t1, wp)
                                   | uu____752 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____759 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_All.pipe_right uu____759
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____760 = fresh_effect_signature () in
                                   match uu____760 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____770 =
                                           let uu____774 =
                                             let uu____775 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____775 in
                                           [uu____774] in
                                         let uu____776 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____770
                                           uu____776 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           FStar_Pervasives_Native.None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           FStar_Pervasives_Native.None
                                           a_wp_b in
                                       let x_a =
                                         let uu____781 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           FStar_Pervasives_Native.None
                                           uu____781 in
                                       let wp_g_x =
                                         let uu____784 =
                                           let uu____785 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____786 =
                                             let uu____787 =
                                               let uu____788 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____788 in
                                             [uu____787] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____785 uu____786 in
                                         uu____784
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____797 =
                                             let uu____798 =
                                               let uu____799 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____799
                                                 FStar_Pervasives_Native.snd in
                                             let uu____804 =
                                               let uu____805 =
                                                 let uu____807 =
                                                   let uu____809 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____810 =
                                                     let uu____812 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____813 =
                                                       let uu____815 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____816 =
                                                         let uu____818 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____818] in
                                                       uu____815 :: uu____816 in
                                                     uu____812 :: uu____813 in
                                                   uu____809 :: uu____810 in
                                                 r :: uu____807 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____805 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____798 uu____804 in
                                           uu____797
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____825 =
                                           let uu____829 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____830 =
                                             let uu____832 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____833 =
                                               let uu____835 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____836 =
                                                 let uu____838 =
                                                   let uu____839 =
                                                     let uu____840 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____840 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____839 in
                                                 let uu____841 =
                                                   let uu____843 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____844 =
                                                     let uu____846 =
                                                       let uu____847 =
                                                         let uu____848 =
                                                           let uu____852 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____852] in
                                                         let uu____853 =
                                                           let uu____855 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____855 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____848
                                                           uu____853 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____847 in
                                                     [uu____846] in
                                                   uu____843 :: uu____844 in
                                                 uu____838 :: uu____841 in
                                               uu____835 :: uu____836 in
                                             uu____832 :: uu____833 in
                                           uu____829 :: uu____830 in
                                         let uu____856 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____825
                                           uu____856 in
                                       let uu____858 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____858 with
                                        | (expected_k1,uu____863,uu____864)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___96_868 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___96_868.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___96_868.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___96_868.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___96_868.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___96_868.FStar_TypeChecker_Env.is_native_tactic)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____875 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a"
                                       FStar_Pervasives_Native.None uu____875 in
                                   let res =
                                     let wp =
                                       let uu____880 =
                                         let uu____881 =
                                           let uu____882 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____882
                                             FStar_Pervasives_Native.snd in
                                         let uu____887 =
                                           let uu____888 =
                                             let uu____890 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____891 =
                                               let uu____893 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____893] in
                                             uu____890 :: uu____891 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____888 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____881 uu____887 in
                                       uu____880 FStar_Pervasives_Native.None
                                         FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____900 =
                                       let uu____904 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____905 =
                                         let uu____907 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____907] in
                                       uu____904 :: uu____905 in
                                     let uu____908 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____900
                                       uu____908 in
                                   let uu____910 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____910 with
                                   | (expected_k1,uu____918,uu____919) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (FStar_Pervasives_Native.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____922 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____922 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____934 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____954 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____954 with
                                     | (act_typ,uu____959,g_t) ->
                                         let env' =
                                           let uu___97_962 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___97_962.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___97_962.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___97_962.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___97_962.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___97_962.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___97_962.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___97_962.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___97_962.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___97_962.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___97_962.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___97_962.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___97_962.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___97_962.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___97_962.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___97_962.FStar_TypeChecker_Env.is_native_tactic)
                                           } in
                                         ((let uu____964 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____964
                                           then
                                             let uu____965 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____966 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____965 uu____966
                                           else ());
                                          (let uu____968 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____968 with
                                           | (act_defn,uu____973,g_a) ->
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
                                               let uu____977 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____993 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____993 with
                                                      | (bs1,uu____999) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1004 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1004 in
                                                          let uu____1006 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1006
                                                           with
                                                           | (k1,uu____1013,g)
                                                               -> (k1, g)))
                                                 | uu____1015 ->
                                                     let uu____1016 =
                                                       let uu____1017 =
                                                         let uu____1020 =
                                                           let uu____1021 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1022 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1021
                                                             uu____1022 in
                                                         (uu____1020,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1017 in
                                                     raise uu____1016 in
                                               (match uu____977 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1029 =
                                                        let uu____1030 =
                                                          let uu____1031 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1031 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1030 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1029);
                                                     (let act_typ2 =
                                                        let uu____1034 =
                                                          let uu____1035 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1035.FStar_Syntax_Syntax.n in
                                                        match uu____1034 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1048 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1048
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1054
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1054
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1067
                                                                    =
                                                                    let uu____1068
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1068] in
                                                                    let uu____1069
                                                                    =
                                                                    let uu____1074
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1074] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1067;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1069;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1075
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1075))
                                                        | uu____1077 ->
                                                            failwith "" in
                                                      let uu____1079 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1079 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let act_typ4 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              univs1 act_typ3 in
                                                          let uu___98_1086 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___98_1086.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___98_1086.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___98_1086.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ4
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____635 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1101 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1101 in
                               let uu____1103 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1103 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1109 =
                                        let uu____1112 =
                                          let uu____1113 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1113.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1112) in
                                      match uu____1109 with
                                      | ([],uu____1115) -> t1
                                      | (uu____1121,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1122,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1132 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1143 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1143 in
                                      let m =
                                        FStar_List.length
                                          (FStar_Pervasives_Native.fst ts1) in
                                      (let uu____1149 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1151 =
                                               FStar_Syntax_Util.is_unknown
                                                 (FStar_Pervasives_Native.snd
                                                    ts1) in
                                             Prims.op_Negation uu____1151))
                                           && (m <> n1) in
                                       if uu____1149
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1165 =
                                           let uu____1166 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1167 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1166 uu____1167 in
                                         failwith uu____1165
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1173 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1173 with
                                      | (univs2,defn) ->
                                          let uu____1178 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1178 with
                                           | (univs',typ) ->
                                               let uu___99_1185 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___99_1185.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___99_1185.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___99_1185.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___100_1189 = ed2 in
                                      let uu____1190 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1191 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1192 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1193 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1194 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1195 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1196 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1197 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1198 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1199 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1200 =
                                        let uu____1201 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1201 in
                                      let uu____1207 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1208 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1209 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___100_1189.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___100_1189.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1190;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1191;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1192;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1193;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1194;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1195;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1196;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1197;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1198;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1199;
                                        FStar_Syntax_Syntax.repr = uu____1200;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1207;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1208;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1209
                                      } in
                                    ((let uu____1212 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1212
                                      then
                                        let uu____1213 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1213
                                      else ());
                                     ed3)))))))
let cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ed  ->
      let uu____1228 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1228 with
      | (effect_binders_un,signature_un) ->
          let uu____1238 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1238 with
           | (effect_binders,env1,uu____1249) ->
               let uu____1250 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1250 with
                | (signature,uu____1259) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1272  ->
                           match uu____1272 with
                           | (bv,qual) ->
                               let uu____1279 =
                                 let uu___101_1280 = bv in
                                 let uu____1281 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___101_1280.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___101_1280.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1281
                                 } in
                               (uu____1279, qual)) effect_binders in
                    let uu____1283 =
                      let uu____1287 =
                        let uu____1288 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1288.FStar_Syntax_Syntax.n in
                      match uu____1287 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1294)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1306 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1283 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1320 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1320
                           then
                             let uu____1321 =
                               let uu____1323 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____1323 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1321
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1347 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1347 with
                           | (t2,comp,uu____1355) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1364 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1364 with
                          | (repr,_comp) ->
                              ((let uu____1377 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1377
                                then
                                  let uu____1378 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1378
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
                                  let uu____1384 =
                                    let uu____1385 =
                                      let uu____1386 =
                                        let uu____1394 =
                                          let uu____1398 =
                                            let uu____1401 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1402 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1401, uu____1402) in
                                          [uu____1398] in
                                        (wp_type1, uu____1394) in
                                      FStar_Syntax_Syntax.Tm_app uu____1386 in
                                    mk1 uu____1385 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1384 in
                                let effect_signature =
                                  let binders =
                                    let uu____1416 =
                                      let uu____1419 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1419) in
                                    let uu____1420 =
                                      let uu____1424 =
                                        let uu____1425 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____1425
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1424] in
                                    uu____1416 :: uu____1420 in
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
                                  let uu____1467 = item in
                                  match uu____1467 with
                                  | (u_item,item1) ->
                                      let uu____1479 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1479 with
                                       | (item2,item_comp) ->
                                           ((let uu____1489 =
                                               let uu____1490 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1490 in
                                             if uu____1489
                                             then
                                               let uu____1491 =
                                                 let uu____1492 =
                                                   let uu____1493 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1494 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1493 uu____1494 in
                                                 FStar_Errors.Err uu____1492 in
                                               raise uu____1491
                                             else ());
                                            (let uu____1496 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1496 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____1509 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1509 with
                                | (dmff_env1,uu____1522,bind_wp,bind_elab) ->
                                    let uu____1525 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1525 with
                                     | (dmff_env2,uu____1538,return_wp,return_elab)
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu____1544 =
                                             let uu____1545 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1545.FStar_Syntax_Syntax.n in
                                           match uu____1544 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1570 =
                                                 let uu____1578 =
                                                   let uu____1581 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1581 in
                                                 match uu____1578 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1615 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1570 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1637 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1637 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1647 =
                                                          let uu____1648 =
                                                            let uu____1656 =
                                                              let uu____1660
                                                                =
                                                                let uu____1663
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____1664
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1663,
                                                                  uu____1664) in
                                                              [uu____1660] in
                                                            (wp_type1,
                                                              uu____1656) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1648 in
                                                        mk1 uu____1647 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1672 =
                                                      let uu____1677 =
                                                        let uu____1678 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1678 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1677 in
                                                    (match uu____1672 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1691
                                                           =
                                                           let error_msg =
                                                             let uu____1693 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1693
                                                               (match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               (if
                                                                  Prims.op_Negation
                                                                    (
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                then fail ()
                                                                else ();
                                                                (let uu____1699
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
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ()) in
                                                                 FStar_All.pipe_right
                                                                   uu____1699
                                                                   FStar_Pervasives.ignore)));
                                                          (let wp =
                                                             let t2 =
                                                               (FStar_Pervasives_Native.fst
                                                                  b21).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type in
                                                           let body3 =
                                                             let uu____1718 =
                                                               let uu____1719
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1720
                                                                 =
                                                                 let uu____1721
                                                                   =
                                                                   let uu____1725
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____1725,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____1721] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1719
                                                                 uu____1720 in
                                                             uu____1718
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____1741 =
                                                             let uu____1742 =
                                                               let uu____1746
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1746] in
                                                             b11 ::
                                                               uu____1742 in
                                                           let uu____1749 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1741
                                                             uu____1749
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____1750 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1752 =
                                             let uu____1753 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1753.FStar_Syntax_Syntax.n in
                                           match uu____1752 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1778 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1778
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____1785 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____1787 =
                                             let uu____1788 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____1788.FStar_Syntax_Syntax.n in
                                           match uu____1787 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____1804 =
                                                 let uu____1805 =
                                                   let uu____1807 =
                                                     let uu____1808 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____1808 in
                                                   [uu____1807] in
                                                 FStar_List.append uu____1805
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____1804 body what
                                           | uu____1809 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____1825 =
                                                let uu____1826 =
                                                  let uu____1827 =
                                                    let uu____1835 =
                                                      let uu____1836 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____1836 in
                                                    (t, uu____1835) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____1827 in
                                                mk1 uu____1826 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____1825) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____1858 = f a2 in
                                               [uu____1858]
                                           | x::xs ->
                                               let uu____1862 =
                                                 apply_last1 f xs in
                                               x :: uu____1862 in
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
                                           let uu____1879 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____1879 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____1896 =
                                                   FStar_Options.debug_any () in
                                                 if uu____1896
                                                 then
                                                   let uu____1897 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____1897
                                                 else ());
                                                (let uu____1899 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____1899))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____1904 =
                                                 let uu____1907 = mk_lid name in
                                                 let uu____1908 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____1907 uu____1908 in
                                               (match uu____1904 with
                                                | (sigelt,fv) ->
                                                    ((let uu____1912 =
                                                        let uu____1914 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____1914 in
                                                      FStar_ST.write sigelts
                                                        uu____1912);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____1925 =
                                             let uu____1927 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____1928 =
                                               FStar_ST.read sigelts in
                                             uu____1927 :: uu____1928 in
                                           FStar_ST.write sigelts uu____1925);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____1938 =
                                              let uu____1940 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____1941 =
                                                FStar_ST.read sigelts in
                                              uu____1940 :: uu____1941 in
                                            FStar_ST.write sigelts uu____1938);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____1951 =
                                               let uu____1953 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____1954 =
                                                 FStar_ST.read sigelts in
                                               uu____1953 :: uu____1954 in
                                             FStar_ST.write sigelts
                                               uu____1951);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____1964 =
                                                let uu____1966 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____1967 =
                                                  FStar_ST.read sigelts in
                                                uu____1966 :: uu____1967 in
                                              FStar_ST.write sigelts
                                                uu____1964);
                                             (let uu____1975 =
                                                FStar_List.fold_left
                                                  (fun uu____2009  ->
                                                     fun action  ->
                                                       match uu____2009 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____2022 =
                                                             let uu____2026 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2026
                                                               params_un in
                                                           (match uu____2022
                                                            with
                                                            | (action_params,env',uu____2032)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2045
                                                                     ->
                                                                    match uu____2045
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2052
                                                                    =
                                                                    let uu___102_2053
                                                                    = bv in
                                                                    let uu____2054
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___102_2053.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___102_2053.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2054
                                                                    } in
                                                                    (uu____2052,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____2057
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____2057
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
                                                                    FStar_Pervasives_Native.None in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____2078
                                                                    ->
                                                                    let uu____2079
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2079 in
                                                                    ((
                                                                    let uu____2082
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____2082
                                                                    then
                                                                    let uu____2083
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____2084
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____2085
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2086
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2083
                                                                    uu____2084
                                                                    uu____2085
                                                                    uu____2086
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
                                                                    let uu____2090
                                                                    =
                                                                    let uu____2092
                                                                    =
                                                                    let uu___103_2093
                                                                    = action in
                                                                    let uu____2094
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____2095
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___103_2093.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___103_2093.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___103_2093.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2094;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2095
                                                                    } in
                                                                    uu____2092
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2090))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____1975 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a in
                                                    let binders =
                                                      let uu____2115 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2116 =
                                                        let uu____2118 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2118] in
                                                      uu____2115 ::
                                                        uu____2116 in
                                                    let uu____2119 =
                                                      let uu____2120 =
                                                        let uu____2121 =
                                                          let uu____2122 =
                                                            let uu____2130 =
                                                              let uu____2134
                                                                =
                                                                let uu____2137
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2138
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2137,
                                                                  uu____2138) in
                                                              [uu____2134] in
                                                            (repr,
                                                              uu____2130) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2122 in
                                                        mk1 uu____2121 in
                                                      let uu____2146 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2120
                                                        uu____2146 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2119
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____2149 =
                                                    let uu____2153 =
                                                      let uu____2154 =
                                                        let uu____2156 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2156 in
                                                      uu____2154.FStar_Syntax_Syntax.n in
                                                    match uu____2153 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2163)
                                                        ->
                                                        let uu____2178 =
                                                          let uu____2187 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____2187
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2218 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2178
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2245 =
                                                               let uu____2246
                                                                 =
                                                                 let uu____2248
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2248 in
                                                               uu____2246.FStar_Syntax_Syntax.n in
                                                             (match uu____2245
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2262
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2262
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2270
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2285
                                                                     ->
                                                                    match uu____2285
                                                                    with
                                                                    | 
                                                                    (bv,uu____2289)
                                                                    ->
                                                                    let uu____2290
                                                                    =
                                                                    let uu____2291
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2291
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2290
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2270
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
                                                                    uu____2323
                                                                    ->
                                                                    let uu____2327
                                                                    =
                                                                    let uu____2328
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2328 in
                                                                    failwith
                                                                    uu____2327 in
                                                                    let uu____2331
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____2333
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____2331,
                                                                    uu____2333)))
                                                              | uu____2337 ->
                                                                  let uu____2338
                                                                    =
                                                                    let uu____2339
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2339 in
                                                                  failwith
                                                                    uu____2338))
                                                    | uu____2343 ->
                                                        let uu____2344 =
                                                          let uu____2345 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2345 in
                                                        failwith uu____2344 in
                                                  (match uu____2149 with
                                                   | (pre,post) ->
                                                       ((let uu____2359 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2361 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2363 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___104_2365
                                                             = ed in
                                                           let uu____2366 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2367 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2368 =
                                                             let uu____2369 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2369) in
                                                           let uu____2373 =
                                                             let uu____2374 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2374) in
                                                           let uu____2378 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2379 =
                                                             let uu____2380 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2380) in
                                                           let uu____2384 =
                                                             let uu____2385 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2385) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2366;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2367;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2368;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2373;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___104_2365.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2378;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2379;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2384;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2389 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____2389
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2400
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____2400
                                                               then
                                                                 let uu____2401
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____2401
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
                                                                    let uu____2413
                                                                    =
                                                                    let uu____2415
                                                                    =
                                                                    let uu____2420
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____2420) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____2415 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2413;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____2428
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____2428
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____2430
                                                                 =
                                                                 let uu____2432
                                                                   =
                                                                   let uu____2434
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2434 in
                                                                 FStar_List.append
                                                                   uu____2432
                                                                   sigelts' in
                                                               (uu____2430,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t env ses quals lids =
  match ses with
  | {
      FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ
        (lex_t1,[],[],t,uu____2485,uu____2486);
      FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = [];
      FStar_Syntax_Syntax.sigmeta = uu____2488;
      FStar_Syntax_Syntax.sigattrs = uu____2489;_}::{
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        FStar_Syntax_Syntax.Sig_datacon
                                                        (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2493);
                                                      FStar_Syntax_Syntax.sigrng
                                                        = r1;
                                                      FStar_Syntax_Syntax.sigquals
                                                        = [];
                                                      FStar_Syntax_Syntax.sigmeta
                                                        = uu____2495;
                                                      FStar_Syntax_Syntax.sigattrs
                                                        = uu____2496;_}::
      {
        FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
          (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2500);
        FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = uu____2502;
        FStar_Syntax_Syntax.sigattrs = uu____2503;_}::[]
      when
      ((_0_39 = (Prims.parse_int "0")) && (_0_40 = (Prims.parse_int "0"))) &&
        (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) &&
            (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid))
           &&
           (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))
      ->
      let u =
        FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r) in
      let t1 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
          FStar_Pervasives_Native.None r in
      let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
      let tc =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_inductive_typ
               (lex_t1, [u], [], t2, [],
                 [FStar_Parser_Const.lextop_lid;
                 FStar_Parser_Const.lexcons_lid]));
          FStar_Syntax_Syntax.sigrng = r;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = []
        } in
      let utop =
        FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r1) in
      let lex_top_t =
        let uu____2542 =
          let uu____2544 =
            let uu____2545 =
              let uu____2549 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1)
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              (uu____2549, [FStar_Syntax_Syntax.U_name utop]) in
            FStar_Syntax_Syntax.Tm_uinst uu____2545 in
          FStar_Syntax_Syntax.mk uu____2544 in
        uu____2542 FStar_Pervasives_Native.None r1 in
      let lex_top_t1 = FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
      let dc_lextop =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_datacon
               (lex_top1, [utop], lex_top_t1, FStar_Parser_Const.lex_t_lid,
                 (Prims.parse_int "0"), []));
          FStar_Syntax_Syntax.sigrng = r1;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = []
        } in
      let ucons1 =
        FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r2) in
      let ucons2 =
        FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some r2) in
      let lex_cons_t =
        let a =
          let uu____2566 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type
                 (FStar_Syntax_Syntax.U_name ucons1))
              FStar_Pervasives_Native.None r2 in
          FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
            uu____2566 in
        let hd1 =
          let uu____2571 = FStar_Syntax_Syntax.bv_to_name a in
          FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
            uu____2571 in
        let tl1 =
          let uu____2573 =
            let uu____2574 =
              let uu____2576 =
                let uu____2577 =
                  let uu____2581 =
                    FStar_Syntax_Syntax.fvar
                      (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid
                         r2) FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  (uu____2581, [FStar_Syntax_Syntax.U_name ucons2]) in
                FStar_Syntax_Syntax.Tm_uinst uu____2577 in
              FStar_Syntax_Syntax.mk uu____2576 in
            uu____2574 FStar_Pervasives_Native.None r2 in
          FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
            uu____2573 in
        let res =
          let uu____2591 =
            let uu____2593 =
              let uu____2594 =
                let uu____2598 =
                  FStar_Syntax_Syntax.fvar
                    (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid
                       r2) FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                (uu____2598,
                  [FStar_Syntax_Syntax.U_max
                     [FStar_Syntax_Syntax.U_name ucons1;
                     FStar_Syntax_Syntax.U_name ucons2]]) in
              FStar_Syntax_Syntax.Tm_uinst uu____2594 in
            FStar_Syntax_Syntax.mk uu____2593 in
          uu____2591 FStar_Pervasives_Native.None r2 in
        let uu____2606 = FStar_Syntax_Syntax.mk_Total res in
        FStar_Syntax_Util.arrow
          [(a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag));
          (hd1, FStar_Pervasives_Native.None);
          (tl1, FStar_Pervasives_Native.None)] uu____2606 in
      let lex_cons_t1 =
        FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2] lex_cons_t in
      let dc_lexcons =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_datacon
               (lex_cons, [ucons1; ucons2], lex_cons_t1,
                 FStar_Parser_Const.lex_t_lid, (Prims.parse_int "0"), []));
          FStar_Syntax_Syntax.sigrng = r2;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = []
        } in
      let uu____2627 = FStar_TypeChecker_Env.get_range env in
      {
        FStar_Syntax_Syntax.sigel =
          (FStar_Syntax_Syntax.Sig_bundle ([tc; dc_lextop; dc_lexcons], lids));
        FStar_Syntax_Syntax.sigrng = uu____2627;
        FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
        FStar_Syntax_Syntax.sigattrs = []
      }
  | uu____2630 ->
      let uu____2632 =
        let uu____2633 =
          let uu____2634 =
            FStar_Syntax_Syntax.mk_sigelt
              (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
          FStar_Syntax_Print.sigelt_to_string uu____2634 in
        FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2633 in
      failwith uu____2632
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
            let uu____2660 = FStar_Syntax_Util.type_u () in
            match uu____2660 with
            | (k,uu____2664) ->
                let phi1 =
                  let uu____2666 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2666
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____2668 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____2668 with
                  | (us,phi2) ->
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_assume (lid, us, phi2));
                        FStar_Syntax_Syntax.sigrng = r;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta;
                        FStar_Syntax_Syntax.sigattrs = []
                      }))
let tc_inductive:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let uu____2701 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____2701 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2720 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____2720 FStar_List.flatten in
              ((let uu____2728 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2728
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
                          let uu____2739 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2745,uu____2746,uu____2747,uu____2748,uu____2749)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2754 -> failwith "Impossible!" in
                          match uu____2739 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2763 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2767,uu____2768,uu____2769,uu____2770,uu____2771)
                        -> lid
                    | uu____2776 -> failwith "Impossible" in
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
                  let uu____2789 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____2789
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
                     let uu____2808 =
                       let uu____2810 =
                         let uu____2811 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____2811;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____2810 :: ses1 in
                     (uu____2808, data_ops_ses)) in
                (let uu____2817 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive" in
                 ());
                res))
let tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2841 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____2854 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____2884 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____2884 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____2909 = FStar_Options.set_options t s in
             match uu____2909 with
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
                ((let uu____2926 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____2926 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____2932 = cps_and_elaborate env1 ne in
           (match uu____2932 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___105_2954 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___105_2954.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_2954.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_2954.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___105_2954.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___106_2956 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___106_2956.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___106_2956.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___106_2956.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___106_2956.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___107_2962 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___107_2962.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___107_2962.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___107_2962.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___107_2962.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____2968 =
             let uu____2972 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____2972 in
           (match uu____2968 with
            | (a,wp_a_src) ->
                let uu____2981 =
                  let uu____2985 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____2985 in
                (match uu____2981 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____2995 =
                         let uu____2997 =
                           let uu____2998 =
                             let uu____3002 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3002) in
                           FStar_Syntax_Syntax.NT uu____2998 in
                         [uu____2997] in
                       FStar_Syntax_Subst.subst uu____2995 wp_b_tgt in
                     let expected_k =
                       let uu____3005 =
                         let uu____3009 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3010 =
                           let uu____3012 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3012] in
                         uu____3009 :: uu____3010 in
                       let uu____3013 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3005 uu____3013 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3031 =
                           let uu____3032 =
                             let uu____3035 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3036 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3035, uu____3036) in
                           FStar_Errors.Error uu____3032 in
                         raise uu____3031 in
                       let uu____3038 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3038 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3056 =
                             let uu____3057 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3057 in
                           if uu____3056
                           then no_reify eff_name
                           else
                             (let uu____3061 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3062 =
                                let uu____3064 =
                                  let uu____3065 =
                                    let uu____3073 =
                                      let uu____3075 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3076 =
                                        let uu____3078 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3078] in
                                      uu____3075 :: uu____3076 in
                                    (repr, uu____3073) in
                                  FStar_Syntax_Syntax.Tm_app uu____3065 in
                                FStar_Syntax_Syntax.mk uu____3064 in
                              uu____3062 FStar_Pervasives_Native.None
                                uu____3061) in
                     let uu____3086 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____3101,lift_wp)) ->
                           let uu____3114 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3114)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____3129 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3129
                             then
                               let uu____3130 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3130
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____3133 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3133 with
                             | (lift1,comp,uu____3142) ->
                                 let uu____3143 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3143 with
                                  | (uu____3150,lift_wp,lift_elab) ->
                                      let uu____3153 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3154 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3086 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___108_3177 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___108_3177.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___108_3177.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___108_3177.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___108_3177.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___108_3177.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___108_3177.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___108_3177.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___108_3177.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___108_3177.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___108_3177.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___108_3177.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___108_3177.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___108_3177.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___108_3177.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___108_3177.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___108_3177.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___108_3177.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___108_3177.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___108_3177.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___108_3177.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___108_3177.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___108_3177.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___108_3177.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___108_3177.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___108_3177.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___108_3177.FStar_TypeChecker_Env.is_native_tactic)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____3181,lift1)
                                ->
                                let uu____3188 =
                                  let uu____3192 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3192 in
                                (match uu____3188 with
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv
                                         FStar_Pervasives_Native.None
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
                                           env2
                                           (FStar_Pervasives_Native.snd
                                              lift_wp) in
                                       let lift_wp_a =
                                         let uu____3209 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3210 =
                                           let uu____3212 =
                                             let uu____3213 =
                                               let uu____3221 =
                                                 let uu____3223 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3224 =
                                                   let uu____3226 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3226] in
                                                 uu____3223 :: uu____3224 in
                                               (lift_wp1, uu____3221) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3213 in
                                           FStar_Syntax_Syntax.mk uu____3212 in
                                         uu____3210
                                           FStar_Pervasives_Native.None
                                           uu____3209 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____3236 =
                                         let uu____3240 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3241 =
                                           let uu____3243 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3244 =
                                             let uu____3246 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3246] in
                                           uu____3243 :: uu____3244 in
                                         uu____3240 :: uu____3241 in
                                       let uu____3247 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3236
                                         uu____3247 in
                                     let uu____3249 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3249 with
                                      | (expected_k2,uu____3255,uu____3256)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___109_3259 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___109_3259.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___109_3259.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___110_3261 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___110_3261.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___110_3261.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___110_3261.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___110_3261.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3275 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3275 with
            | (tps1,c1) ->
                let uu____3284 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3284 with
                 | (tps2,env3,us) ->
                     let uu____3295 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3295 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____3309 =
                              let uu____3310 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3310 in
                            match uu____3309 with
                            | (uvs1,t) ->
                                let uu____3322 =
                                  let uu____3329 =
                                    let uu____3332 =
                                      let uu____3333 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3333.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3332) in
                                  match uu____3329 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3341,c4)) -> ([], c4)
                                  | (uu____3362,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3377 -> failwith "Impossible" in
                                (match uu____3322 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3405 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3405 with
                                         | (uu____3408,t1) ->
                                             let uu____3410 =
                                               let uu____3411 =
                                                 let uu____3414 =
                                                   let uu____3415 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3416 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____3421 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3415 uu____3416
                                                     uu____3421 in
                                                 (uu____3414, r) in
                                               FStar_Errors.Error uu____3411 in
                                             raise uu____3410)
                                      else ();
                                      (let se1 =
                                         let uu___111_3424 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___111_3424.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___111_3424.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___111_3424.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___111_3424.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3433,uu____3434,uu____3435) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3438  ->
                   match uu___85_3438 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3439 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3442,uu____3443) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3448  ->
                   match uu___85_3448 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3449 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3456 =
             if uvs = []
             then
               let uu____3457 =
                 let uu____3458 = FStar_Syntax_Util.type_u () in
                 FStar_Pervasives_Native.fst uu____3458 in
               check_and_gen env2 t uu____3457
             else
               (let uu____3462 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3462 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3468 =
                        let uu____3469 = FStar_Syntax_Util.type_u () in
                        FStar_Pervasives_Native.fst uu____3469 in
                      tc_check_trivial_guard env2 t1 uu____3468 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____3473 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3473)) in
           (match uu____3456 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___112_3483 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___112_3483.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___112_3483.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___112_3483.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___112_3483.FStar_Syntax_Syntax.sigattrs)
                  } in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____3490 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____3490 with
            | (uu____3497,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit in
           let uu____3505 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3505 with
            | (e1,c,g1) ->
                let uu____3516 =
                  let uu____3520 =
                    let uu____3522 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    FStar_Pervasives_Native.Some uu____3522 in
                  let uu____3523 =
                    let uu____3526 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3526) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3520 uu____3523 in
                (match uu____3516 with
                 | (e2,uu____3534,g) ->
                     ((let uu____3537 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3537);
                      (let se1 =
                         let uu___113_3539 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___113_3539.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___113_3539.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___113_3539.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___113_3539.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____3572 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3572
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____3585 =
                      let uu____3586 =
                        let uu____3589 =
                          let uu____3590 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3591 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3592 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3590 uu____3591 uu____3592 in
                        (uu____3589, r) in
                      FStar_Errors.Error uu____3586 in
                    raise uu____3585) in
           let uu____3595 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3626  ->
                     fun lb  ->
                       match uu____3626 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3650 =
                             let uu____3656 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3656 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____3700 ->
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
                                  (let uu____3712 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3712, quals_opt1))) in
                           (match uu____3650 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____3595 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____3764 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___86_3767  ->
                                match uu___86_3767 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____3768 -> false)) in
                      if uu____3764
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____3775 =
                    let uu____3777 =
                      let uu____3778 =
                        let uu____3785 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____3785) in
                      FStar_Syntax_Syntax.Tm_let uu____3778 in
                    FStar_Syntax_Syntax.mk uu____3777 in
                  uu____3775 FStar_Pervasives_Native.None r in
                let uu____3802 =
                  let uu____3808 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___114_3814 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___114_3814.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___114_3814.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___114_3814.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___114_3814.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___114_3814.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___114_3814.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___114_3814.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___114_3814.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___114_3814.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___114_3814.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___114_3814.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___114_3814.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___114_3814.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___114_3814.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___114_3814.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___114_3814.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___114_3814.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___114_3814.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___114_3814.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___114_3814.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___114_3814.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___114_3814.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___114_3814.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___114_3814.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___114_3814.FStar_TypeChecker_Env.is_native_tactic)
                       }) e in
                  match uu____3808 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____3822;
                       FStar_Syntax_Syntax.vars = uu____3823;_},uu____3824,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3839,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____3842 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___87_3847  ->
                             match uu___87_3847 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____3849 =
                                   let uu____3850 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____3857 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____3857)
                                          else ();
                                          ok)
                                       (FStar_Pervasives_Native.snd lbs1) in
                                   Prims.op_Negation uu____3850 in
                                 if uu____3849
                                 then FStar_Pervasives_Native.None
                                 else
                                   FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> FStar_Pervasives_Native.Some q) quals1 in
                      ((let uu___115_3867 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___115_3867.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___115_3867.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___115_3867.FStar_Syntax_Syntax.sigattrs)
                        }), lbs1)
                  | uu____3872 -> failwith "impossible" in
                (match uu____3802 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.fv
                                fv lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____3901 = log env2 in
                       if uu____3901
                       then
                         let uu____3902 =
                           let uu____3903 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____3914 =
                                         let uu____3919 =
                                           let uu____3920 =
                                             let uu____3922 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____3922.FStar_Syntax_Syntax.fv_name in
                                           uu____3920.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____3919 in
                                       match uu____3914 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____3926 -> false in
                                     if should_log
                                     then
                                       let uu____3931 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____3932 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____3931 uu____3932
                                     else "")) in
                           FStar_All.pipe_right uu____3903
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____3902
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____3954 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____3954 with
                              | (bs1,c1) ->
                                  let uu____3959 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____3959
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____3967 =
                                            let uu____3968 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____3968.FStar_Syntax_Syntax.n in
                                          (match uu____3967 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____3982 =
                                                 let uu____3983 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____3983.FStar_Syntax_Syntax.n in
                                               (match uu____3982 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____3990 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____3990 in
                                                    let uu____3991 =
                                                      let uu____3992 =
                                                        let uu____3993 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____3993 args in
                                                      uu____3992
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____3991 u
                                                | uu____3998 -> c1)
                                           | uu____3999 -> c1)
                                      | uu____4000 -> c1 in
                                    let uu___116_4001 = t1 in
                                    let uu____4002 =
                                      let uu____4003 =
                                        let uu____4010 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4010) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4003 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4002;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___116_4001.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___116_4001.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4026 =
                               let uu____4027 = FStar_Syntax_Subst.compress h in
                               uu____4027.FStar_Syntax_Syntax.n in
                             (match uu____4026 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4034 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4034 in
                                  let uu____4035 =
                                    let uu____4036 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4036
                                      args in
                                  uu____4035 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____4041 -> t1)
                         | uu____4042 -> t1 in
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
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       let reflected_tactic_decl b lb bs assm_lid comp =
                         let reified_tac =
                           let uu____4069 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4069 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4080 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____4080, (FStar_Pervasives_Native.snd x)))
                             bs in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Parser_Const.tac_effect_lid))
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, FStar_Pervasives_Native.None)]
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let unit_binder =
                           let uu____4105 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4105 in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let uu___117_4110 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___118_4117 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___118_4117.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___118_4117.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___118_4117.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___118_4117.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_4110.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_4110.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_4110.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___117_4110.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____4127 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4127 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4146 =
                                    let uu____4147 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4147.FStar_Syntax_Syntax.n in
                                  (match uu____4146 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4166 =
                                           let uu____4168 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4168.FStar_Syntax_Syntax.fv_name in
                                         uu____4166.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4170 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4170 in
                                       let uu____4171 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____4173 =
                                              let uu____4174 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4174 in
                                            Prims.op_Negation uu____4173) in
                                       if uu____4171
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl
                                             (FStar_Pervasives_Native.fst
                                                lbs1) hd1 bs assm_lid comp in
                                         FStar_Pervasives_Native.Some
                                           (se_assm, se_refl)
                                       else FStar_Pervasives_Native.None
                                   | uu____4197 ->
                                       FStar_Pervasives_Native.None))
                         | uu____4200 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____4213 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4213
                             then
                               let uu____4214 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4215 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4214 uu____4215
                             else ());
                            ([se_assm; se_refl], []))
                       | FStar_Pervasives_Native.None  -> ([se1], []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___88_4249  ->
                match uu___88_4249 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4250 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4256) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4260 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4265 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4268 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4281 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4294) ->
          let uu____4299 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4299
          then
            let for_export_bundle se1 uu____4318 =
              match uu____4318 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4341,uu____4342) ->
                       let dec =
                         let uu___119_4348 = se1 in
                         let uu____4349 =
                           let uu____4350 =
                             let uu____4354 =
                               let uu____4356 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4356 in
                             (l, us, uu____4354) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4350 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4349;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___119_4348.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___119_4348.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___119_4348.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4364,uu____4365,uu____4366) ->
                       let dec =
                         let uu___120_4370 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___120_4370.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___120_4370.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___120_4370.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4373 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4385,uu____4386,uu____4387) ->
          let uu____4388 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4388 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4401 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4401
          then
            ([(let uu___121_4410 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___121_4410.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___121_4410.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___121_4410.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____4412 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___89_4415  ->
                       match uu___89_4415 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4416 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4419 -> true
                       | uu____4420 -> false)) in
             if uu____4412 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4430 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4433 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4436 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4439 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4442 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4452) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4462 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4462
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
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               } in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____4480 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4480
          then
            let uu____4485 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___122_4494 = se in
                      let uu____4495 =
                        let uu____4496 =
                          let uu____4500 =
                            let uu____4501 =
                              let uu____4503 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4503.FStar_Syntax_Syntax.fv_name in
                            uu____4501.FStar_Syntax_Syntax.v in
                          (uu____4500, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4496 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4495;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___122_4494.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___122_4494.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___122_4494.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____4485, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4519 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4528 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4537 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4540 = FStar_Options.using_facts_from () in
                 match uu____4540 with
                 | FStar_Pervasives_Native.Some ns ->
                     let proof_ns =
                       let uu____4552 =
                         let uu____4557 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4557 [([], false)] in
                       [uu____4552] in
                     let uu___123_4586 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___123_4586.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___123_4586.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___123_4586.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___123_4586.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___123_4586.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___123_4586.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___123_4586.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___123_4586.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___123_4586.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___123_4586.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___123_4586.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___123_4586.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___123_4586.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___123_4586.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___123_4586.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___123_4586.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___123_4586.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___123_4586.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___123_4586.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___123_4586.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___123_4586.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___123_4586.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___123_4586.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___123_4586.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___123_4586.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___123_4586.FStar_TypeChecker_Env.is_native_tactic)
                     }
                 | FStar_Pervasives_Native.None  -> env))
           | uu____4588 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4589 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4598 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4598) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4599,uu____4600,uu____4601) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4604  ->
                  match uu___90_4604 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4605 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4606,uu____4607) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4612  ->
                  match uu___90_4612 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4613 -> false))
          -> env
      | uu____4614 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4652 se =
        match uu____4652 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4682 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4682
              then
                let uu____4683 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4683
              else ());
             (let uu____4685 = tc_decl env1 se in
              match uu____4685 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____4714 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____4714
                             then
                               let uu____4715 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____4715
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  (FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.promote
                     (fun t  ->
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                          FStar_TypeChecker_Normalize.CheckNoUvars;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.NoDeltaSteps;
                          FStar_TypeChecker_Normalize.CompressUvars;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Zeta;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Iota;
                          FStar_TypeChecker_Normalize.NoFullNorm] env1 t);
                   (let env2 =
                      FStar_All.pipe_right ses'1
                        (FStar_List.fold_left
                           (fun env2  ->
                              fun se1  -> add_sigelt_to_env env2 se1) env1) in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____4734 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____4734
                     then
                       let uu____4735 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____4741 =
                                  let uu____4742 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____4742 "\n" in
                                Prims.strcat s uu____4741) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____4735
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____4747 =
                       let accum_exports_hidden uu____4765 se1 =
                         match uu____4765 with
                         | (exports1,hidden1) ->
                             let uu____4781 = for_export hidden1 se1 in
                             (match uu____4781 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____4747 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___124_4825 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___124_4825.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___124_4825.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___124_4825.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___124_4825.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____4868 = acc in
        match uu____4868 with
        | (uu____4886,uu____4887,env1,uu____4889) ->
            let uu____4896 =
              FStar_Util.record_time
                (fun uu____4920  -> process_one_decl acc se) in
            (match uu____4896 with
             | (r,ms_elapsed) ->
                 ((let uu____4954 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____4954
                   then
                     let uu____4955 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____4956 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____4955 uu____4956
                   else ());
                  r)) in
      let uu____4958 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____4958 with
      | (ses1,exports,env1,uu____4984) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
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
      (let uu____5011 = FStar_Options.debug_any () in
       if uu____5011
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
         let uu___125_5017 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___125_5017.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___125_5017.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___125_5017.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___125_5017.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___125_5017.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___125_5017.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___125_5017.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___125_5017.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___125_5017.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___125_5017.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___125_5017.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___125_5017.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___125_5017.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___125_5017.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___125_5017.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___125_5017.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___125_5017.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___125_5017.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___125_5017.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___125_5017.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___125_5017.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___125_5017.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___125_5017.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___125_5017.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___125_5017.FStar_TypeChecker_Env.is_native_tactic)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____5020 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5020 with
        | (ses,exports,env3) ->
            ((let uu___126_5039 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___126_5039.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___126_5039.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___126_5039.FStar_Syntax_Syntax.is_interface)
              }), exports, env3)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____5058 = tc_decls env decls in
        match uu____5058 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___127_5076 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___127_5076.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___127_5076.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___127_5076.FStar_Syntax_Syntax.is_interface)
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
          let uu___128_5093 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___128_5093.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___128_5093.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___128_5093.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___128_5093.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___128_5093.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___128_5093.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___128_5093.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___128_5093.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___128_5093.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___128_5093.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___128_5093.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___128_5093.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___128_5093.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___128_5093.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___128_5093.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___128_5093.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___128_5093.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___128_5093.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___128_5093.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___128_5093.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___128_5093.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___128_5093.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___128_5093.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___128_5093.FStar_TypeChecker_Env.is_native_tactic)
          } in
        let check_term lid univs1 t =
          let uu____5104 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5104 with
          | (univs2,t1) ->
              ((let uu____5110 =
                  let uu____5111 =
                    let uu____5114 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5114 in
                  FStar_All.pipe_left uu____5111
                    (FStar_Options.Other "Exports") in
                if uu____5110
                then
                  let uu____5115 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5116 =
                    let uu____5117 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5117
                      (FStar_String.concat ", ") in
                  let uu____5123 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5115 uu____5116 uu____5123
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5126 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5126 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5144 =
             let uu____5145 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5146 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5145 uu____5146 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5144);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5153) ->
              let uu____5158 =
                let uu____5159 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5159 in
              if uu____5158
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5167,uu____5168) ->
              let t =
                let uu____5175 =
                  let uu____5177 =
                    let uu____5178 =
                      let uu____5185 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5185) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5178 in
                  FStar_Syntax_Syntax.mk uu____5177 in
                uu____5175 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5195,uu____5196,uu____5197) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5203 =
                let uu____5204 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5204 in
              if uu____5203 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____5207,lbs),uu____5209) ->
              let uu____5217 =
                let uu____5218 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5218 in
              if uu____5217
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
              let uu____5233 =
                let uu____5234 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5234 in
              if uu____5233
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5242 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5243 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5247 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5248 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5249 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5250 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let finish_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul1 =
          let uu___129_5267 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___129_5267.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___129_5267.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____5270 =
           let uu____5271 = FStar_Options.lax () in
           Prims.op_Negation uu____5271 in
         if uu____5270 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5277 =
           let uu____5278 = FStar_Options.interactive () in
           Prims.op_Negation uu____5278 in
         if uu____5277
         then
           let uu____5279 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5279 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      let uu____5291 = tc_partial_modul env modul in
      match uu____5291 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      (let uu____5314 = FStar_Options.debug_any () in
       if uu____5314
       then
         let uu____5315 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5315
       else ());
      (let env1 =
         let uu___130_5319 = env in
         let uu____5320 =
           let uu____5321 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5321 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___130_5319.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___130_5319.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___130_5319.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___130_5319.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___130_5319.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___130_5319.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___130_5319.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___130_5319.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___130_5319.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___130_5319.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___130_5319.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___130_5319.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___130_5319.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___130_5319.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___130_5319.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___130_5319.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___130_5319.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___130_5319.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5320;
           FStar_TypeChecker_Env.lax_universes =
             (uu___130_5319.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___130_5319.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___130_5319.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___130_5319.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___130_5319.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___130_5319.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___130_5319.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___130_5319.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____5322 = tc_modul env1 m in
       match uu____5322 with
       | (m1,env2) ->
           ((let uu____5330 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5330
             then
               let uu____5331 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5331
             else ());
            (let uu____5334 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____5334
             then
               let normalize_toplevel_lets se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),ids) ->
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
                       let uu____5358 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5358 with
                       | (univnames1,e) ->
                           let uu___131_5363 = lb in
                           let uu____5364 =
                             let uu____5366 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5366 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___131_5363.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___131_5363.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___131_5363.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___131_5363.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5364
                           } in
                     let uu___132_5367 = se in
                     let uu____5368 =
                       let uu____5369 =
                         let uu____5373 =
                           let uu____5377 = FStar_List.map update lbs in
                           (b, uu____5377) in
                         (uu____5373, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____5369 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5368;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___132_5367.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___132_5367.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___132_5367.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___132_5367.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____5384 -> se in
               let normalized_module =
                 let uu___133_5386 = m1 in
                 let uu____5387 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___133_5386.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5387;
                   FStar_Syntax_Syntax.exports =
                     (uu___133_5386.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___133_5386.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5388 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5388
             else ());
            (m1, env2)))