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
            let uu____14 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____14 l in
          let uu___91_15 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___91_15.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___91_15.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___91_15.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___91_15.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___91_15.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___91_15.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___91_15.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___91_15.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___91_15.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___91_15.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___91_15.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___91_15.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___91_15.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___91_15.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___91_15.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___91_15.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___91_15.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___91_15.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___91_15.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___91_15.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___91_15.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___91_15.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___91_15.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___91_15.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___91_15.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___91_15.FStar_TypeChecker_Env.is_native_tactic)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____24 = FStar_TypeChecker_Env.current_module env in
                let uu____25 =
                  let uu____26 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____26 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____24 uu____25
            | l::uu____28 -> l in
          let uu___92_31 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___92_31.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___92_31.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___92_31.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___92_31.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___92_31.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___92_31.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___92_31.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___92_31.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___92_31.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___92_31.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___92_31.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___92_31.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___92_31.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___92_31.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___92_31.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___92_31.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___92_31.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___92_31.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___92_31.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___92_31.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___92_31.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___92_31.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___92_31.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___92_31.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___92_31.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___92_31.FStar_TypeChecker_Env.is_native_tactic)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____41 =
         let uu____42 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____42 in
       Prims.op_Negation uu____41)
let is_native_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____56) ->
            let uu____65 =
              let uu____66 = FStar_Syntax_Subst.compress h' in
              uu____66.FStar_Syntax_Syntax.n in
            (match uu____65 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> env.FStar_TypeChecker_Env.is_native_tactic tac_lid
             | uu____72 -> false)
        | uu____73 -> false
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____86 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____86 with
        | (t1,c,g) ->
            (FStar_ST.write t1.FStar_Syntax_Syntax.tk
               (FStar_Pervasives_Native.Some
                  ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n));
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
        (let uu____113 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____113
         then
           let uu____114 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____114
         else ());
        (let uu____116 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____116 with
         | (t',uu____124,uu____125) ->
             ((let uu____127 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____127
               then
                 let uu____128 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____128
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
        let uu____142 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____142
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____171 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____171)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____205 =
          let uu____206 =
            let uu____207 =
              let uu____212 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____212, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____207 in
          raise uu____206 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____262)::(wp,uu____264)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____281 -> fail ())
        | uu____282 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____294 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____294 with
      | (effect_params_un,signature_un,opening) ->
          let uu____304 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____304 with
           | (effect_params,env,uu____313) ->
               let uu____314 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____314 with
                | (signature,uu____320) ->
                    let ed1 =
                      let uu___93_322 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___93_322.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___93_322.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___93_322.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___93_322.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___93_322.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___93_322.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___93_322.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___93_322.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___93_322.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___93_322.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___93_322.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___93_322.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___93_322.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___93_322.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___93_322.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___93_322.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___93_322.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____328 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening
                                (FStar_Pervasives_Native.snd ts) in
                            ([], t1) in
                          let uu___94_359 = ed1 in
                          let uu____360 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____361 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____362 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____363 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____364 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____365 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____366 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____367 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____368 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____369 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____370 =
                            let uu____371 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            FStar_Pervasives_Native.snd uu____371 in
                          let uu____382 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____383 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____384 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___95_392 = a in
                                 let uu____393 =
                                   let uu____394 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   FStar_Pervasives_Native.snd uu____394 in
                                 let uu____405 =
                                   let uu____406 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   FStar_Pervasives_Native.snd uu____406 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___95_392.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___95_392.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___95_392.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___95_392.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____393;
                                   FStar_Syntax_Syntax.action_typ = uu____405
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___94_359.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___94_359.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___94_359.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___94_359.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___94_359.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____360;
                            FStar_Syntax_Syntax.bind_wp = uu____361;
                            FStar_Syntax_Syntax.if_then_else = uu____362;
                            FStar_Syntax_Syntax.ite_wp = uu____363;
                            FStar_Syntax_Syntax.stronger = uu____364;
                            FStar_Syntax_Syntax.close_wp = uu____365;
                            FStar_Syntax_Syntax.assert_p = uu____366;
                            FStar_Syntax_Syntax.assume_p = uu____367;
                            FStar_Syntax_Syntax.null_wp = uu____368;
                            FStar_Syntax_Syntax.trivial = uu____369;
                            FStar_Syntax_Syntax.repr = uu____370;
                            FStar_Syntax_Syntax.return_repr = uu____382;
                            FStar_Syntax_Syntax.bind_repr = uu____383;
                            FStar_Syntax_Syntax.actions = uu____384
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____447 =
                          let uu____448 =
                            let uu____453 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____453, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____448 in
                        raise uu____447 in
                      let uu____462 =
                        let uu____463 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____463.FStar_Syntax_Syntax.n in
                      match uu____462 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____508)::(wp,uu____510)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____527 -> fail signature1)
                      | uu____528 -> fail signature1 in
                    let uu____529 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____529 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____559 =
                           let uu____560 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____560 with
                           | (signature1,uu____574) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____576 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____576 in
                         ((let uu____578 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____578
                           then
                             let uu____579 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____580 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____581 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____582 =
                               let uu____583 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____583 in
                             let uu____584 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____579 uu____580 uu____581 uu____582
                               uu____584
                           else ());
                          (let check_and_gen' env2 uu____600 k =
                             match uu____600 with
                             | (uu____608,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____620 =
                                 let uu____627 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____628 =
                                   let uu____631 =
                                     let uu____632 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____632 in
                                   [uu____631] in
                                 uu____627 :: uu____628 in
                               let uu____633 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____620 uu____633 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____639 = fresh_effect_signature () in
                             match uu____639 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____663 =
                                     let uu____670 =
                                       let uu____671 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____671 in
                                     [uu____670] in
                                   let uu____672 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____663
                                     uu____672 in
                                 let expected_k =
                                   let uu____682 =
                                     let uu____689 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____690 =
                                       let uu____693 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____694 =
                                         let uu____697 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____698 =
                                           let uu____701 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____702 =
                                             let uu____705 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____705] in
                                           uu____701 :: uu____702 in
                                         uu____697 :: uu____698 in
                                       uu____693 :: uu____694 in
                                     uu____689 :: uu____690 in
                                   let uu____706 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____682
                                     uu____706 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____713 =
                                 let uu____714 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____714
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____713 in
                             let expected_k =
                               let uu____728 =
                                 let uu____735 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____736 =
                                   let uu____739 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____740 =
                                     let uu____743 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____744 =
                                       let uu____747 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____747] in
                                     uu____743 :: uu____744 in
                                   uu____739 :: uu____740 in
                                 uu____735 :: uu____736 in
                               let uu____748 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____728 uu____748 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____759 =
                                 let uu____766 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____767 =
                                   let uu____770 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____770] in
                                 uu____766 :: uu____767 in
                               let uu____771 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____759 uu____771 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____777 = FStar_Syntax_Util.type_u () in
                             match uu____777 with
                             | (t,uu____783) ->
                                 let expected_k =
                                   let uu____789 =
                                     let uu____796 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____797 =
                                       let uu____800 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____801 =
                                         let uu____804 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____804] in
                                       uu____800 :: uu____801 in
                                     uu____796 :: uu____797 in
                                   let uu____805 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____789
                                     uu____805 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____812 =
                                 let uu____813 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____813
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____812 in
                             let b_wp_a =
                               let uu____827 =
                                 let uu____834 =
                                   let uu____835 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____835 in
                                 [uu____834] in
                               let uu____836 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____827 uu____836 in
                             let expected_k =
                               let uu____846 =
                                 let uu____853 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____854 =
                                   let uu____857 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____858 =
                                     let uu____861 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____861] in
                                   uu____857 :: uu____858 in
                                 uu____853 :: uu____854 in
                               let uu____862 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____846 uu____862 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____873 =
                                 let uu____880 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____881 =
                                   let uu____884 =
                                     let uu____885 =
                                       let uu____886 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____886
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____885 in
                                   let uu____895 =
                                     let uu____898 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____898] in
                                   uu____884 :: uu____895 in
                                 uu____880 :: uu____881 in
                               let uu____899 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____873 uu____899 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____910 =
                                 let uu____917 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____918 =
                                   let uu____921 =
                                     let uu____922 =
                                       let uu____923 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____923
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____922 in
                                   let uu____932 =
                                     let uu____935 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____935] in
                                   uu____921 :: uu____932 in
                                 uu____917 :: uu____918 in
                               let uu____936 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____910 uu____936 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____947 =
                                 let uu____954 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____954] in
                               let uu____955 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____947 uu____955 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____961 = FStar_Syntax_Util.type_u () in
                             match uu____961 with
                             | (t,uu____967) ->
                                 let expected_k =
                                   let uu____973 =
                                     let uu____980 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____981 =
                                       let uu____984 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____984] in
                                     uu____980 :: uu____981 in
                                   let uu____985 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____973
                                     uu____985 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____990 =
                             let uu____1001 =
                               let uu____1002 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____1002.FStar_Syntax_Syntax.n in
                             match uu____1001 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____1019 ->
                                 let repr =
                                   let uu____1021 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____1021 with
                                   | (t,uu____1027) ->
                                       let expected_k =
                                         let uu____1033 =
                                           let uu____1040 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1041 =
                                             let uu____1044 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____1044] in
                                           uu____1040 :: uu____1041 in
                                         let uu____1045 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____1033
                                           uu____1045 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____1062 =
                                     let uu____1067 =
                                       let uu____1068 =
                                         let uu____1087 =
                                           let uu____1090 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____1091 =
                                             let uu____1094 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____1094] in
                                           uu____1090 :: uu____1091 in
                                         (repr1, uu____1087) in
                                       FStar_Syntax_Syntax.Tm_app uu____1068 in
                                     FStar_Syntax_Syntax.mk uu____1067 in
                                   uu____1062 FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____1112 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____1112 wp in
                                 let destruct_repr t =
                                   let uu____1129 =
                                     let uu____1130 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____1130.FStar_Syntax_Syntax.n in
                                   match uu____1129 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____1147,(t1,uu____1149)::(wp,uu____1151)::[])
                                       -> (t1, wp)
                                   | uu____1218 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____1233 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_All.pipe_right uu____1233
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____1234 = fresh_effect_signature () in
                                   match uu____1234 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____1258 =
                                           let uu____1265 =
                                             let uu____1266 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____1266 in
                                           [uu____1265] in
                                         let uu____1267 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____1258
                                           uu____1267 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           FStar_Pervasives_Native.None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           FStar_Pervasives_Native.None
                                           a_wp_b in
                                       let x_a =
                                         let uu____1275 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           FStar_Pervasives_Native.None
                                           uu____1275 in
                                       let wp_g_x =
                                         let uu____1281 =
                                           let uu____1282 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____1283 =
                                             let uu____1284 =
                                               let uu____1285 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1285 in
                                             [uu____1284] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____1282 uu____1283 in
                                         uu____1281
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____1298 =
                                             let uu____1299 =
                                               let uu____1300 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right
                                                 uu____1300
                                                 FStar_Pervasives_Native.snd in
                                             let uu____1309 =
                                               let uu____1310 =
                                                 let uu____1313 =
                                                   let uu____1316 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____1317 =
                                                     let uu____1320 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____1321 =
                                                       let uu____1324 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____1325 =
                                                         let uu____1328 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____1328] in
                                                       uu____1324 ::
                                                         uu____1325 in
                                                     uu____1320 :: uu____1321 in
                                                   uu____1316 :: uu____1317 in
                                                 r :: uu____1313 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1310 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____1299 uu____1309 in
                                           uu____1298
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____1336 =
                                           let uu____1343 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1344 =
                                             let uu____1347 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____1348 =
                                               let uu____1351 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____1352 =
                                                 let uu____1355 =
                                                   let uu____1356 =
                                                     let uu____1357 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____1357 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____1356 in
                                                 let uu____1358 =
                                                   let uu____1361 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____1362 =
                                                     let uu____1365 =
                                                       let uu____1366 =
                                                         let uu____1367 =
                                                           let uu____1374 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____1374] in
                                                         let uu____1375 =
                                                           let uu____1380 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____1380 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____1367
                                                           uu____1375 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____1366 in
                                                     [uu____1365] in
                                                   uu____1361 :: uu____1362 in
                                                 uu____1355 :: uu____1358 in
                                               uu____1351 :: uu____1352 in
                                             uu____1347 :: uu____1348 in
                                           uu____1343 :: uu____1344 in
                                         let uu____1381 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____1336
                                           uu____1381 in
                                       let uu____1386 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____1386 with
                                        | (expected_k1,uu____1394,uu____1395)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___96_1400 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___96_1400.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___96_1400.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___96_1400.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___96_1400.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___96_1400.FStar_TypeChecker_Env.is_native_tactic)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1410 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a"
                                       FStar_Pervasives_Native.None
                                       uu____1410 in
                                   let res =
                                     let wp =
                                       let uu____1421 =
                                         let uu____1422 =
                                           let uu____1423 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1423
                                             FStar_Pervasives_Native.snd in
                                         let uu____1432 =
                                           let uu____1433 =
                                             let uu____1436 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1437 =
                                               let uu____1440 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1440] in
                                             uu____1436 :: uu____1437 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1433 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1422 uu____1432 in
                                       uu____1421
                                         FStar_Pervasives_Native.None
                                         FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1448 =
                                       let uu____1455 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1456 =
                                         let uu____1459 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1459] in
                                       uu____1455 :: uu____1456 in
                                     let uu____1460 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1448
                                       uu____1460 in
                                   let uu____1465 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1465 with
                                   | (expected_k1,uu____1479,uu____1480) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (FStar_Pervasives_Native.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1484 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1484 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1505 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1530 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1530 with
                                     | (act_typ,uu____1538,g_t) ->
                                         let env' =
                                           let uu___97_1541 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___97_1541.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___97_1541.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___97_1541.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___97_1541.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___97_1541.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___97_1541.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___97_1541.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___97_1541.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___97_1541.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___97_1541.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___97_1541.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___97_1541.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___97_1541.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___97_1541.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___97_1541.FStar_TypeChecker_Env.is_native_tactic)
                                           } in
                                         ((let uu____1543 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1543
                                           then
                                             let uu____1544 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1545 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1544 uu____1545
                                           else ());
                                          (let uu____1547 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1547 with
                                           | (act_defn,uu____1555,g_a) ->
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
                                               let uu____1559 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1591 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1591 with
                                                      | (bs1,uu____1601) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1612 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1612 in
                                                          let uu____1617 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1617
                                                           with
                                                           | (k1,uu____1629,g)
                                                               -> (k1, g)))
                                                 | uu____1631 ->
                                                     let uu____1632 =
                                                       let uu____1633 =
                                                         let uu____1638 =
                                                           let uu____1639 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1640 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1639
                                                             uu____1640 in
                                                         (uu____1638,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1633 in
                                                     raise uu____1632 in
                                               (match uu____1559 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1649 =
                                                        let uu____1650 =
                                                          let uu____1651 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1651 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1650 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1649);
                                                     (let act_typ2 =
                                                        let uu____1657 =
                                                          let uu____1658 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1658.FStar_Syntax_Syntax.n in
                                                        match uu____1657 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1689 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1689
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1700
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1700
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1736
                                                                    =
                                                                    let uu____1737
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1737] in
                                                                    let uu____1738
                                                                    =
                                                                    let uu____1749
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1749] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1736;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1738;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1750
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1750))
                                                        | uu____1755 ->
                                                            failwith "" in
                                                      let uu____1760 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1760 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let act_typ4 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              univs1 act_typ3 in
                                                          let uu___98_1769 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___98_1769.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___98_1769.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___98_1769.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ4
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____990 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1795 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1795 in
                               let uu____1800 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1800 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1808 =
                                        let uu____1813 =
                                          let uu____1814 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1814.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1813) in
                                      match uu____1808 with
                                      | ([],uu____1819) -> t1
                                      | (uu____1830,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1831,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1853 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1866 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1866 in
                                      let m =
                                        FStar_List.length
                                          (FStar_Pervasives_Native.fst ts1) in
                                      (let uu____1871 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1873 =
                                               FStar_Syntax_Util.is_unknown
                                                 (FStar_Pervasives_Native.snd
                                                    ts1) in
                                             Prims.op_Negation uu____1873))
                                           && (m <> n1) in
                                       if uu____1871
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1888 =
                                           let uu____1889 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1890 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1889 uu____1890 in
                                         failwith uu____1888
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1896 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1896 with
                                      | (univs2,defn) ->
                                          let uu____1903 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1903 with
                                           | (univs',typ) ->
                                               let uu___99_1913 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___99_1913.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___99_1913.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___99_1913.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___100_1918 = ed2 in
                                      let uu____1919 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1920 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1921 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1922 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1923 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1924 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1925 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1926 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1927 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1928 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1929 =
                                        let uu____1930 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1930 in
                                      let uu____1941 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1942 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1943 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___100_1918.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___100_1918.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1919;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1920;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1921;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1922;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1923;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1924;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1925;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1926;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1927;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1928;
                                        FStar_Syntax_Syntax.repr = uu____1929;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1941;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1942;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1943
                                      } in
                                    ((let uu____1947 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1947
                                      then
                                        let uu____1948 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1948
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
      let uu____1968 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1968 with
      | (effect_binders_un,signature_un) ->
          let uu____1985 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1985 with
           | (effect_binders,env1,uu____2004) ->
               let uu____2005 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____2005 with
                | (signature,uu____2021) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2041  ->
                           match uu____2041 with
                           | (bv,qual) ->
                               let uu____2052 =
                                 let uu___101_2053 = bv in
                                 let uu____2054 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___101_2053.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___101_2053.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2054
                                 } in
                               (uu____2052, qual)) effect_binders in
                    let uu____2059 =
                      let uu____2068 =
                        let uu____2069 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____2069.FStar_Syntax_Syntax.n in
                      match uu____2068 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____2083)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____2111 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____2059 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2141 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____2141
                           then
                             let uu____2142 =
                               let uu____2145 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____2145 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2142
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____2179 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____2179 with
                           | (t2,comp,uu____2192) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2201 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2201 with
                          | (repr,_comp) ->
                              ((let uu____2223 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2223
                                then
                                  let uu____2224 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2224
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
                                  let uu____2230 =
                                    let uu____2231 =
                                      let uu____2232 =
                                        let uu____2251 =
                                          let uu____2258 =
                                            let uu____2263 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2264 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2263, uu____2264) in
                                          [uu____2258] in
                                        (wp_type1, uu____2251) in
                                      FStar_Syntax_Syntax.Tm_app uu____2232 in
                                    mk1 uu____2231 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2230 in
                                let effect_signature =
                                  let binders =
                                    let uu____2291 =
                                      let uu____2296 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2296) in
                                    let uu____2297 =
                                      let uu____2304 =
                                        let uu____2305 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2305
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2304] in
                                    uu____2291 :: uu____2297 in
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
                                  let uu____2370 = item in
                                  match uu____2370 with
                                  | (u_item,item1) ->
                                      let uu____2391 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2391 with
                                       | (item2,item_comp) ->
                                           ((let uu____2407 =
                                               let uu____2408 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2408 in
                                             if uu____2407
                                             then
                                               let uu____2409 =
                                                 let uu____2410 =
                                                   let uu____2411 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2412 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2411 uu____2412 in
                                                 FStar_Errors.Err uu____2410 in
                                               raise uu____2409
                                             else ());
                                            (let uu____2414 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2414 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2434 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2434 with
                                | (dmff_env1,uu____2458,bind_wp,bind_elab) ->
                                    let uu____2461 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2461 with
                                     | (dmff_env2,uu____2485,return_wp,return_elab)
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
                                           let uu____2494 =
                                             let uu____2495 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2495.FStar_Syntax_Syntax.n in
                                           match uu____2494 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2545 =
                                                 let uu____2560 =
                                                   let uu____2565 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2565 in
                                                 match uu____2560 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2629 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2545 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2668 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2668 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2687 =
                                                          let uu____2688 =
                                                            let uu____2707 =
                                                              let uu____2714
                                                                =
                                                                let uu____2719
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2720
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2719,
                                                                  uu____2720) in
                                                              [uu____2714] in
                                                            (wp_type1,
                                                              uu____2707) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2688 in
                                                        mk1 uu____2687 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2735 =
                                                      let uu____2744 =
                                                        let uu____2745 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2745 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2744 in
                                                    (match uu____2735 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2764
                                                           =
                                                           let error_msg =
                                                             let uu____2766 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2766
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
                                                                (let uu____2772
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
                                                                   uu____2772
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
                                                             let uu____2807 =
                                                               let uu____2808
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2809
                                                                 =
                                                                 let uu____2810
                                                                   =
                                                                   let uu____2817
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2817,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2810] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2808
                                                                 uu____2809 in
                                                             uu____2807
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2842 =
                                                             let uu____2843 =
                                                               let uu____2850
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2850] in
                                                             b11 ::
                                                               uu____2843 in
                                                           let uu____2855 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2842
                                                             uu____2855
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2856 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2858 =
                                             let uu____2859 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2859.FStar_Syntax_Syntax.n in
                                           match uu____2858 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2909 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2909
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2922 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2924 =
                                             let uu____2925 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2925.FStar_Syntax_Syntax.n in
                                           match uu____2924 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2958 =
                                                 let uu____2959 =
                                                   let uu____2962 =
                                                     let uu____2963 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2963 in
                                                   [uu____2962] in
                                                 FStar_List.append uu____2959
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2958 body what
                                           | uu____2964 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2990 =
                                                let uu____2991 =
                                                  let uu____2992 =
                                                    let uu____3011 =
                                                      let uu____3012 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3012 in
                                                    (t, uu____3011) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2992 in
                                                mk1 uu____2991 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2990) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3044 = f a2 in
                                               [uu____3044]
                                           | x::xs ->
                                               let uu____3049 =
                                                 apply_last1 f xs in
                                               x :: uu____3049 in
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
                                           let uu____3069 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____3069 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3099 =
                                                   FStar_Options.debug_any () in
                                                 if uu____3099
                                                 then
                                                   let uu____3100 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3100
                                                 else ());
                                                (let uu____3102 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3102))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3111 =
                                                 let uu____3116 = mk_lid name in
                                                 let uu____3117 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3116 uu____3117 in
                                               (match uu____3111 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3121 =
                                                        let uu____3124 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____3124 in
                                                      FStar_ST.write sigelts
                                                        uu____3121);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____3138 =
                                             let uu____3141 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3142 =
                                               FStar_ST.read sigelts in
                                             uu____3141 :: uu____3142 in
                                           FStar_ST.write sigelts uu____3138);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____3155 =
                                              let uu____3158 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____3159 =
                                                FStar_ST.read sigelts in
                                              uu____3158 :: uu____3159 in
                                            FStar_ST.write sigelts uu____3155);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____3172 =
                                               let uu____3175 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3176 =
                                                 FStar_ST.read sigelts in
                                               uu____3175 :: uu____3176 in
                                             FStar_ST.write sigelts
                                               uu____3172);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____3189 =
                                                let uu____3192 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____3193 =
                                                  FStar_ST.read sigelts in
                                                uu____3192 :: uu____3193 in
                                              FStar_ST.write sigelts
                                                uu____3189);
                                             (let uu____3204 =
                                                FStar_List.fold_left
                                                  (fun uu____3244  ->
                                                     fun action  ->
                                                       match uu____3244 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3265 =
                                                             let uu____3272 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3272
                                                               params_un in
                                                           (match uu____3265
                                                            with
                                                            | (action_params,env',uu____3281)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3301
                                                                     ->
                                                                    match uu____3301
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3312
                                                                    =
                                                                    let uu___102_3313
                                                                    = bv in
                                                                    let uu____3314
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___102_3313.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___102_3313.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3314
                                                                    } in
                                                                    (uu____3312,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3320
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3320
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
                                                                    uu____3350
                                                                    ->
                                                                    let uu____3351
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3351 in
                                                                    ((
                                                                    let uu____3357
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3357
                                                                    then
                                                                    let uu____3358
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3359
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3360
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3361
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3358
                                                                    uu____3359
                                                                    uu____3360
                                                                    uu____3361
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
                                                                    let uu____3365
                                                                    =
                                                                    let uu____3368
                                                                    =
                                                                    let uu___103_3369
                                                                    = action in
                                                                    let uu____3370
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3371
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___103_3369.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___103_3369.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___103_3369.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3370;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3371
                                                                    } in
                                                                    uu____3368
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3365))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3204 with
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
                                                      let uu____3404 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3405 =
                                                        let uu____3408 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3408] in
                                                      uu____3404 ::
                                                        uu____3405 in
                                                    let uu____3409 =
                                                      let uu____3410 =
                                                        let uu____3411 =
                                                          let uu____3412 =
                                                            let uu____3431 =
                                                              let uu____3438
                                                                =
                                                                let uu____3443
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3444
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3443,
                                                                  uu____3444) in
                                                              [uu____3438] in
                                                            (repr,
                                                              uu____3431) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3412 in
                                                        mk1 uu____3411 in
                                                      let uu____3459 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3410
                                                        uu____3459 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3409
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3462 =
                                                    let uu____3471 =
                                                      let uu____3472 =
                                                        let uu____3477 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3477 in
                                                      uu____3472.FStar_Syntax_Syntax.n in
                                                    match uu____3471 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3489)
                                                        ->
                                                        let uu____3522 =
                                                          let uu____3539 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3539
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3597 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3522
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3649 =
                                                               let uu____3650
                                                                 =
                                                                 let uu____3655
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3655 in
                                                               uu____3650.FStar_Syntax_Syntax.n in
                                                             (match uu____3649
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3686
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3686
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3701
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3726
                                                                     ->
                                                                    match uu____3726
                                                                    with
                                                                    | 
                                                                    (bv,uu____3732)
                                                                    ->
                                                                    let uu____3733
                                                                    =
                                                                    let uu____3734
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3734
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3733
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3701
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
                                                                    uu____3795
                                                                    ->
                                                                    let uu____3802
                                                                    =
                                                                    let uu____3803
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____3803 in
                                                                    failwith
                                                                    uu____3802 in
                                                                    let uu____3808
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____3813
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____3808,
                                                                    uu____3813)))
                                                              | uu____3822 ->
                                                                  let uu____3823
                                                                    =
                                                                    let uu____3824
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3824 in
                                                                  failwith
                                                                    uu____3823))
                                                    | uu____3833 ->
                                                        let uu____3834 =
                                                          let uu____3835 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____3835 in
                                                        failwith uu____3834 in
                                                  (match uu____3462 with
                                                   | (pre,post) ->
                                                       ((let uu____3865 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____3867 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____3869 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___104_3871
                                                             = ed in
                                                           let uu____3872 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____3873 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____3874 =
                                                             let uu____3875 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____3875) in
                                                           let uu____3886 =
                                                             let uu____3887 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____3887) in
                                                           let uu____3898 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____3899 =
                                                             let uu____3900 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____3900) in
                                                           let uu____3911 =
                                                             let uu____3912 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____3912) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3872;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3873;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3874;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3886;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___104_3871.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3898;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3899;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3911;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____3923 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____3923
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3941
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____3941
                                                               then
                                                                 let uu____3942
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____3942
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
                                                                    let uu____3954
                                                                    =
                                                                    let uu____3957
                                                                    =
                                                                    let uu____3968
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____3968) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3957 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3954;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____3989
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____3989
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____3991
                                                                 =
                                                                 let uu____3994
                                                                   =
                                                                   let uu____3997
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____3997 in
                                                                 FStar_List.append
                                                                   uu____3994
                                                                   sigelts' in
                                                               (uu____3991,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t env ses quals lids =
  match ses with
  | {
      FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ
        (lex_t1,[],[],t,uu____4061,uu____4062);
      FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = [];
      FStar_Syntax_Syntax.sigmeta = uu____4064;
      FStar_Syntax_Syntax.sigattrs = uu____4065;_}::{
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        FStar_Syntax_Syntax.Sig_datacon
                                                        (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____4069);
                                                      FStar_Syntax_Syntax.sigrng
                                                        = r1;
                                                      FStar_Syntax_Syntax.sigquals
                                                        = [];
                                                      FStar_Syntax_Syntax.sigmeta
                                                        = uu____4071;
                                                      FStar_Syntax_Syntax.sigattrs
                                                        = uu____4072;_}::
      {
        FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
          (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____4076);
        FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = uu____4078;
        FStar_Syntax_Syntax.sigattrs = uu____4079;_}::[]
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
        let uu____4148 =
          let uu____4153 =
            let uu____4154 =
              let uu____4163 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1)
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              (uu____4163, [FStar_Syntax_Syntax.U_name utop]) in
            FStar_Syntax_Syntax.Tm_uinst uu____4154 in
          FStar_Syntax_Syntax.mk uu____4153 in
        uu____4148 FStar_Pervasives_Native.None r1 in
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
          let uu____4184 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type
                 (FStar_Syntax_Syntax.U_name ucons1))
              FStar_Pervasives_Native.None r2 in
          FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
            uu____4184 in
        let hd1 =
          let uu____4186 = FStar_Syntax_Syntax.bv_to_name a in
          FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
            uu____4186 in
        let tl1 =
          let uu____4188 =
            let uu____4189 =
              let uu____4194 =
                let uu____4195 =
                  let uu____4204 =
                    FStar_Syntax_Syntax.fvar
                      (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid
                         r2) FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  (uu____4204, [FStar_Syntax_Syntax.U_name ucons2]) in
                FStar_Syntax_Syntax.Tm_uinst uu____4195 in
              FStar_Syntax_Syntax.mk uu____4194 in
            uu____4189 FStar_Pervasives_Native.None r2 in
          FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r2)
            uu____4188 in
        let res =
          let uu____4216 =
            let uu____4221 =
              let uu____4222 =
                let uu____4231 =
                  FStar_Syntax_Syntax.fvar
                    (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid
                       r2) FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                (uu____4231,
                  [FStar_Syntax_Syntax.U_max
                     [FStar_Syntax_Syntax.U_name ucons1;
                     FStar_Syntax_Syntax.U_name ucons2]]) in
              FStar_Syntax_Syntax.Tm_uinst uu____4222 in
            FStar_Syntax_Syntax.mk uu____4221 in
          uu____4216 FStar_Pervasives_Native.None r2 in
        let uu____4238 = FStar_Syntax_Syntax.mk_Total res in
        FStar_Syntax_Util.arrow
          [(a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag));
          (hd1, FStar_Pervasives_Native.None);
          (tl1, FStar_Pervasives_Native.None)] uu____4238 in
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
      let uu____4279 = FStar_TypeChecker_Env.get_range env in
      {
        FStar_Syntax_Syntax.sigel =
          (FStar_Syntax_Syntax.Sig_bundle ([tc; dc_lextop; dc_lexcons], lids));
        FStar_Syntax_Syntax.sigrng = uu____4279;
        FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
        FStar_Syntax_Syntax.sigattrs = []
      }
  | uu____4284 ->
      let uu____4287 =
        let uu____4288 =
          let uu____4289 =
            FStar_Syntax_Syntax.mk_sigelt
              (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
          FStar_Syntax_Print.sigelt_to_string uu____4289 in
        FStar_Util.format1 "Unexpected lex_t: %s\n" uu____4288 in
      failwith uu____4287
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
            let uu____4319 = FStar_Syntax_Util.type_u () in
            match uu____4319 with
            | (k,uu____4325) ->
                let phi1 =
                  let uu____4327 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4327
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4329 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4329 with
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
          let uu____4375 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4375 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4408 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4408 FStar_List.flatten in
              ((let uu____4422 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4422
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
                          let uu____4433 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4443,uu____4444,uu____4445,uu____4446,uu____4447)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4456 -> failwith "Impossible!" in
                          match uu____4433 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4467 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4471,uu____4472,uu____4473,uu____4474,uu____4475)
                        -> lid
                    | uu____4484 -> failwith "Impossible" in
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
                  let uu____4502 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4502
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
                     let uu____4525 =
                       let uu____4528 =
                         let uu____4529 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4529;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4528 :: ses1 in
                     (uu____4525, data_ops_ses)) in
                (let uu____4539 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4575 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4600 ->
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
           let uu____4652 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4652 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4691 = FStar_Options.set_options t s in
             match uu____4691 with
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
                ((let uu____4717 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4717 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4725 = cps_and_elaborate env1 ne in
           (match uu____4725 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___105_4762 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___105_4762.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_4762.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_4762.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___105_4762.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___106_4764 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___106_4764.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___106_4764.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___106_4764.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___106_4764.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___107_4772 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___107_4772.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___107_4772.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___107_4772.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___107_4772.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4780 =
             let uu____4789 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4789 in
           (match uu____4780 with
            | (a,wp_a_src) ->
                let uu____4808 =
                  let uu____4817 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4817 in
                (match uu____4808 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4837 =
                         let uu____4840 =
                           let uu____4841 =
                             let uu____4850 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4850) in
                           FStar_Syntax_Syntax.NT uu____4841 in
                         [uu____4840] in
                       FStar_Syntax_Subst.subst uu____4837 wp_b_tgt in
                     let expected_k =
                       let uu____4856 =
                         let uu____4863 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4864 =
                           let uu____4867 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4867] in
                         uu____4863 :: uu____4864 in
                       let uu____4868 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4856 uu____4868 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4895 =
                           let uu____4896 =
                             let uu____4901 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____4902 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____4901, uu____4902) in
                           FStar_Errors.Error uu____4896 in
                         raise uu____4895 in
                       let uu____4907 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____4907 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____4941 =
                             let uu____4942 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____4942 in
                           if uu____4941
                           then no_reify eff_name
                           else
                             (let uu____4950 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____4951 =
                                let uu____4956 =
                                  let uu____4957 =
                                    let uu____4976 =
                                      let uu____4979 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____4980 =
                                        let uu____4983 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____4983] in
                                      uu____4979 :: uu____4980 in
                                    (repr, uu____4976) in
                                  FStar_Syntax_Syntax.Tm_app uu____4957 in
                                FStar_Syntax_Syntax.mk uu____4956 in
                              uu____4951 FStar_Pervasives_Native.None
                                uu____4950) in
                     let uu____4990 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5018,lift_wp)) ->
                           let uu____5042 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5042)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5068 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5068
                             then
                               let uu____5069 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5069
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____5072 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5072 with
                             | (lift1,comp,uu____5087) ->
                                 let uu____5088 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5088 with
                                  | (uu____5101,lift_wp,lift_elab) ->
                                      let uu____5104 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5105 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____4990 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___108_5146 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___108_5146.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___108_5146.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___108_5146.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___108_5146.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___108_5146.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___108_5146.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___108_5146.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___108_5146.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___108_5146.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___108_5146.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___108_5146.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___108_5146.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___108_5146.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___108_5146.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___108_5146.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___108_5146.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___108_5146.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___108_5146.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___108_5146.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___108_5146.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___108_5146.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___108_5146.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___108_5146.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___108_5146.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___108_5146.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___108_5146.FStar_TypeChecker_Env.is_native_tactic)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5152,lift1)
                                ->
                                let uu____5164 =
                                  let uu____5173 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5173 in
                                (match uu____5164 with
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
                                         let uu____5207 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5208 =
                                           let uu____5213 =
                                             let uu____5214 =
                                               let uu____5233 =
                                                 let uu____5236 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5237 =
                                                   let uu____5240 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5240] in
                                                 uu____5236 :: uu____5237 in
                                               (lift_wp1, uu____5233) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5214 in
                                           FStar_Syntax_Syntax.mk uu____5213 in
                                         uu____5208
                                           FStar_Pervasives_Native.None
                                           uu____5207 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5252 =
                                         let uu____5259 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5260 =
                                           let uu____5263 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5264 =
                                             let uu____5267 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5267] in
                                           uu____5263 :: uu____5264 in
                                         uu____5259 :: uu____5260 in
                                       let uu____5268 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5252
                                         uu____5268 in
                                     let uu____5273 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5273 with
                                      | (expected_k2,uu____5283,uu____5284)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___109_5287 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___109_5287.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___109_5287.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___110_5289 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___110_5289.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___110_5289.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___110_5289.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___110_5289.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5308 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5308 with
            | (tps1,c1) ->
                let uu____5323 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5323 with
                 | (tps2,env3,us) ->
                     let uu____5341 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5341 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5362 =
                              let uu____5363 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5363 in
                            match uu____5362 with
                            | (uvs1,t) ->
                                let uu____5378 =
                                  let uu____5393 =
                                    let uu____5398 =
                                      let uu____5399 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5399.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5398) in
                                  match uu____5393 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5418,c4)) -> ([], c4)
                                  | (uu____5464,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5497 -> failwith "Impossible" in
                                (match uu____5378 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5547 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5547 with
                                         | (uu____5552,t1) ->
                                             let uu____5554 =
                                               let uu____5555 =
                                                 let uu____5560 =
                                                   let uu____5561 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5562 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5563 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5561 uu____5562
                                                     uu____5563 in
                                                 (uu____5560, r) in
                                               FStar_Errors.Error uu____5555 in
                                             raise uu____5554)
                                      else ();
                                      (let se1 =
                                         let uu___111_5566 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___111_5566.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___111_5566.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___111_5566.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___111_5566.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5585,uu____5586,uu____5587) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_5591  ->
                   match uu___85_5591 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5592 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5597,uu____5598) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_5606  ->
                   match uu___85_5606 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5607 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5616 =
             if uvs = []
             then
               let uu____5617 =
                 let uu____5618 = FStar_Syntax_Util.type_u () in
                 FStar_Pervasives_Native.fst uu____5618 in
               check_and_gen env2 t uu____5617
             else
               (let uu____5624 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____5624 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____5632 =
                        let uu____5633 = FStar_Syntax_Util.type_u () in
                        FStar_Pervasives_Native.fst uu____5633 in
                      tc_check_trivial_guard env2 t1 uu____5632 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____5639 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____5639)) in
           (match uu____5616 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___112_5655 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___112_5655.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___112_5655.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___112_5655.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___112_5655.FStar_Syntax_Syntax.sigattrs)
                  } in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5665 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5665 with
            | (uu____5678,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit in
           let uu____5688 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5688 with
            | (e1,c,g1) ->
                let uu____5706 =
                  let uu____5713 =
                    let uu____5716 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    FStar_Pervasives_Native.Some uu____5716 in
                  let uu____5717 =
                    let uu____5722 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5722) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5713 uu____5717 in
                (match uu____5706 with
                 | (e2,uu____5740,g) ->
                     ((let uu____5743 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5743);
                      (let se1 =
                         let uu___113_5745 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___113_5745.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___113_5745.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___113_5745.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___113_5745.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5796 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5796
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5804 =
                      let uu____5805 =
                        let uu____5810 =
                          let uu____5811 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5812 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5813 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5811 uu____5812 uu____5813 in
                        (uu____5810, r) in
                      FStar_Errors.Error uu____5805 in
                    raise uu____5804) in
           let uu____5818 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____5869  ->
                     fun lb  ->
                       match uu____5869 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____5911 =
                             let uu____5922 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____5922 with
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
                                   | uu____6003 ->
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
                                  (let uu____6008 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____6008, quals_opt1))) in
                           (match uu____5911 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____5818 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6104 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___86_6108  ->
                                match uu___86_6108 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6109 -> false)) in
                      if uu____6104
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6121 =
                    let uu____6126 =
                      let uu____6127 =
                        let uu____6142 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6142) in
                      FStar_Syntax_Syntax.Tm_let uu____6127 in
                    FStar_Syntax_Syntax.mk uu____6126 in
                  uu____6121 FStar_Pervasives_Native.None r in
                let uu____6165 =
                  let uu____6176 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___114_6185 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___114_6185.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___114_6185.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___114_6185.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___114_6185.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___114_6185.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___114_6185.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___114_6185.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___114_6185.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___114_6185.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___114_6185.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___114_6185.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___114_6185.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___114_6185.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___114_6185.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___114_6185.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___114_6185.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___114_6185.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___114_6185.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___114_6185.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___114_6185.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___114_6185.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___114_6185.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___114_6185.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___114_6185.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___114_6185.FStar_TypeChecker_Env.is_native_tactic)
                       }) e in
                  match uu____6176 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____6198;
                       FStar_Syntax_Syntax.pos = uu____6199;
                       FStar_Syntax_Syntax.vars = uu____6200;_},uu____6201,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6236,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6245 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___87_6251  ->
                             match uu___87_6251 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____6254 =
                                   let uu____6255 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____6262 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____6262)
                                          else ();
                                          ok)
                                       (FStar_Pervasives_Native.snd lbs1) in
                                   Prims.op_Negation uu____6255 in
                                 if uu____6254
                                 then FStar_Pervasives_Native.None
                                 else
                                   FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> FStar_Pervasives_Native.Some q) quals1 in
                      ((let uu___115_6277 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___115_6277.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___115_6277.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___115_6277.FStar_Syntax_Syntax.sigattrs)
                        }), lbs1)
                  | uu____6286 -> failwith "impossible" in
                (match uu____6165 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6335 = log env2 in
                       if uu____6335
                       then
                         let uu____6336 =
                           let uu____6337 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6352 =
                                         let uu____6361 =
                                           let uu____6362 =
                                             let uu____6365 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6365.FStar_Syntax_Syntax.fv_name in
                                           uu____6362.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6361 in
                                       match uu____6352 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6372 -> false in
                                     if should_log
                                     then
                                       let uu____6381 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6382 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6381 uu____6382
                                     else "")) in
                           FStar_All.pipe_right uu____6337
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6336
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6417 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6417 with
                              | (bs1,c1) ->
                                  let uu____6424 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6424
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6440 =
                                            let uu____6441 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6441.FStar_Syntax_Syntax.n in
                                          (match uu____6440 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6476 =
                                                 let uu____6477 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6477.FStar_Syntax_Syntax.n in
                                               (match uu____6476 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6493 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6493 in
                                                    let uu____6494 =
                                                      let uu____6495 =
                                                        let uu____6496 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6496 args in
                                                      uu____6495
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6494 u
                                                | uu____6499 -> c1)
                                           | uu____6500 -> c1)
                                      | uu____6501 -> c1 in
                                    let uu___116_6502 = t1 in
                                    let uu____6503 =
                                      let uu____6504 =
                                        let uu____6519 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6519) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6504 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6503;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___116_6502.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___116_6502.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___116_6502.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6551 =
                               let uu____6552 = FStar_Syntax_Subst.compress h in
                               uu____6552.FStar_Syntax_Syntax.n in
                             (match uu____6551 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6568 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6568 in
                                  let uu____6569 =
                                    let uu____6570 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6570
                                      args in
                                  uu____6569 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6573 -> t1)
                         | uu____6574 -> t1 in
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
                           let uu____6602 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6602 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6619 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____6619, (FStar_Pervasives_Native.snd x)))
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
                           let uu____6662 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6662 in
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
                         let uu___117_6669 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___118_6681 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___118_6681.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___118_6681.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___118_6681.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___118_6681.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_6669.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_6669.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_6669.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___117_6669.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6698 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____6698 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____6734 =
                                    let uu____6735 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6735.FStar_Syntax_Syntax.n in
                                  (match uu____6734 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____6778 =
                                           let uu____6781 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____6781.FStar_Syntax_Syntax.fv_name in
                                         uu____6778.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____6783 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____6783 in
                                       let uu____6784 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____6786 =
                                              let uu____6787 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____6787 in
                                            Prims.op_Negation uu____6786) in
                                       if uu____6784
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
                                   | uu____6829 ->
                                       FStar_Pervasives_Native.None))
                         | uu____6834 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____6856 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____6856
                             then
                               let uu____6857 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____6858 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____6857 uu____6858
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
             (fun uu___88_6911  ->
                match uu___88_6911 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____6912 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____6918) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____6924 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____6933 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____6938 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____6963 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6987) ->
          let uu____6996 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____6996
          then
            let for_export_bundle se1 uu____7027 =
              match uu____7027 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7066,uu____7067) ->
                       let dec =
                         let uu___119_7077 = se1 in
                         let uu____7078 =
                           let uu____7079 =
                             let uu____7086 =
                               let uu____7091 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7091 in
                             (l, us, uu____7086) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7079 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7078;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___119_7077.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___119_7077.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___119_7077.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7107,uu____7108,uu____7109) ->
                       let dec =
                         let uu___120_7115 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___120_7115.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___120_7115.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___120_7115.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7120 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7142,uu____7143,uu____7144) ->
          let uu____7145 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7145 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7166 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7166
          then
            ([(let uu___121_7182 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___121_7182.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___121_7182.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___121_7182.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7184 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___89_7188  ->
                       match uu___89_7188 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7189 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7194 -> true
                       | uu____7195 -> false)) in
             if uu____7184 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7213 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7218 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7223 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7228 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7233 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7251) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7268 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7268
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
          let uu____7301 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7301
          then
            let uu____7310 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___122_7323 = se in
                      let uu____7324 =
                        let uu____7325 =
                          let uu____7332 =
                            let uu____7333 =
                              let uu____7336 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7336.FStar_Syntax_Syntax.fv_name in
                            uu____7333.FStar_Syntax_Syntax.v in
                          (uu____7332, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7325 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7324;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___122_7323.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___122_7323.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___122_7323.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7310, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7360 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7377 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____7393 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____7397 = FStar_Options.using_facts_from () in
                 match uu____7397 with
                 | FStar_Pervasives_Native.Some ns ->
                     let proof_ns =
                       let uu____7418 =
                         let uu____7427 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____7427 [([], false)] in
                       [uu____7418] in
                     let uu___123_7482 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___123_7482.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___123_7482.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___123_7482.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___123_7482.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___123_7482.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___123_7482.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___123_7482.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___123_7482.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___123_7482.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___123_7482.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___123_7482.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___123_7482.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___123_7482.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___123_7482.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___123_7482.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___123_7482.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___123_7482.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___123_7482.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___123_7482.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___123_7482.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___123_7482.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___123_7482.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___123_7482.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___123_7482.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___123_7482.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___123_7482.FStar_TypeChecker_Env.is_native_tactic)
                     }
                 | FStar_Pervasives_Native.None  -> env))
           | uu____7485 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7486 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7496 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7496) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7497,uu____7498,uu____7499) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_7503  ->
                  match uu___90_7503 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7504 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7505,uu____7506) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_7514  ->
                  match uu___90_7514 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7515 -> false))
          -> env
      | uu____7516 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7578 se =
        match uu____7578 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7631 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7631
              then
                let uu____7632 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7632
              else ());
             (let uu____7634 = tc_decl env1 se in
              match uu____7634 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7684 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7684
                             then
                               let uu____7685 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7685
                             else ());
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
                   (let uu____7705 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____7705
                    then
                      let uu____7706 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____7712 =
                                 let uu____7713 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____7713 "\n" in
                               Prims.strcat s uu____7712) "" ses'1 in
                      FStar_Util.print1 "Checked: %s\n" uu____7706
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses'1;
                   (let uu____7718 =
                      let accum_exports_hidden uu____7748 se1 =
                        match uu____7748 with
                        | (exports1,hidden1) ->
                            let uu____7776 = for_export hidden1 se1 in
                            (match uu____7776 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'1 in
                    match uu____7718 with
                    | (exports1,hidden1) ->
                        let ses'2 =
                          FStar_List.map
                            (fun s  ->
                               let uu___124_7855 = s in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (uu___124_7855.FStar_Syntax_Syntax.sigel);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___124_7855.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___124_7855.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___124_7855.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (se.FStar_Syntax_Syntax.sigattrs)
                               }) ses'1 in
                        (((FStar_List.rev_append ses'2 ses1), exports1, env2,
                           hidden1), ses_elaborated1))))) in
      let process_one_decl_timed acc se =
        let uu____7933 = acc in
        match uu____7933 with
        | (uu____7968,uu____7969,env1,uu____7971) ->
            let uu____7984 =
              FStar_Util.record_time
                (fun uu____8030  -> process_one_decl acc se) in
            (match uu____7984 with
             | (r,ms_elapsed) ->
                 ((let uu____8094 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8094
                   then
                     let uu____8095 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8096 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8095 uu____8096
                   else ());
                  r)) in
      let uu____8098 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8098 with
      | (ses1,exports,env1,uu____8146) ->
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
      (let uu____8185 = FStar_Options.debug_any () in
       if uu____8185
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
         let uu___125_8191 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___125_8191.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___125_8191.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___125_8191.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___125_8191.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___125_8191.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___125_8191.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___125_8191.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___125_8191.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___125_8191.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___125_8191.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___125_8191.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___125_8191.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___125_8191.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___125_8191.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___125_8191.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___125_8191.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___125_8191.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___125_8191.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___125_8191.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___125_8191.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___125_8191.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___125_8191.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___125_8191.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___125_8191.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___125_8191.FStar_TypeChecker_Env.is_native_tactic)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____8194 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____8194 with
        | (ses,exports,env3) ->
            ((let uu___126_8227 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___126_8227.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___126_8227.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___126_8227.FStar_Syntax_Syntax.is_interface)
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
        let uu____8252 = tc_decls env decls in
        match uu____8252 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___127_8283 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___127_8283.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___127_8283.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___127_8283.FStar_Syntax_Syntax.is_interface)
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
          let uu___128_8303 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___128_8303.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___128_8303.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___128_8303.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___128_8303.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___128_8303.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___128_8303.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___128_8303.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___128_8303.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___128_8303.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___128_8303.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___128_8303.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___128_8303.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___128_8303.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___128_8303.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___128_8303.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___128_8303.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___128_8303.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___128_8303.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___128_8303.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___128_8303.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___128_8303.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___128_8303.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___128_8303.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___128_8303.FStar_TypeChecker_Env.is_native_tactic)
          } in
        let check_term lid univs1 t =
          let uu____8314 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8314 with
          | (univs2,t1) ->
              ((let uu____8322 =
                  let uu____8323 =
                    let uu____8326 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8326 in
                  FStar_All.pipe_left uu____8323
                    (FStar_Options.Other "Exports") in
                if uu____8322
                then
                  let uu____8327 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8328 =
                    let uu____8329 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8329
                      (FStar_String.concat ", ") in
                  let uu____8338 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8327 uu____8328 uu____8338
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8341 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8341 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____8365 =
             let uu____8366 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8367 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8366 uu____8367 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8365);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8374) ->
              let uu____8383 =
                let uu____8384 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8384 in
              if uu____8383
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8394,uu____8395) ->
              let t =
                let uu____8409 =
                  let uu____8414 =
                    let uu____8415 =
                      let uu____8430 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8430) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8415 in
                  FStar_Syntax_Syntax.mk uu____8414 in
                uu____8409 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8438,uu____8439,uu____8440) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8448 =
                let uu____8449 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8449 in
              if uu____8448 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8453,lbs),uu____8455) ->
              let uu____8470 =
                let uu____8471 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8471 in
              if uu____8470
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
              let uu____8490 =
                let uu____8491 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8491 in
              if uu____8490
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8500 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8501 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8508 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8509 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8510 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8511 -> () in
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
          let uu___129_8530 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___129_8530.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___129_8530.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____8533 =
           let uu____8534 = FStar_Options.lax () in
           Prims.op_Negation uu____8534 in
         if uu____8533 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____8540 =
           let uu____8541 = FStar_Options.interactive () in
           Prims.op_Negation uu____8541 in
         if uu____8540
         then
           let uu____8542 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____8542 FStar_Pervasives.ignore
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
      let uu____8556 = tc_partial_modul env modul in
      match uu____8556 with
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
      (let uu____8589 = FStar_Options.debug_any () in
       if uu____8589
       then
         let uu____8590 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8590
       else ());
      (let env1 =
         let uu___130_8594 = env in
         let uu____8595 =
           let uu____8596 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8596 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___130_8594.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___130_8594.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___130_8594.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___130_8594.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___130_8594.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___130_8594.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___130_8594.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___130_8594.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___130_8594.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___130_8594.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___130_8594.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___130_8594.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___130_8594.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___130_8594.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___130_8594.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___130_8594.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___130_8594.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___130_8594.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8595;
           FStar_TypeChecker_Env.lax_universes =
             (uu___130_8594.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___130_8594.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___130_8594.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___130_8594.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___130_8594.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___130_8594.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___130_8594.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___130_8594.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____8597 = tc_modul env1 m in
       match uu____8597 with
       | (m1,env2) ->
           ((let uu____8609 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8609
             then
               let uu____8610 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8610
             else ());
            (let uu____8613 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8613
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
                       let uu____8644 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8644 with
                       | (univnames1,e) ->
                           let uu___131_8651 = lb in
                           let uu____8652 =
                             let uu____8657 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____8657 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___131_8651.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___131_8651.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___131_8651.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___131_8651.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____8652
                           } in
                     let uu___132_8658 = se in
                     let uu____8659 =
                       let uu____8660 =
                         let uu____8667 =
                           let uu____8674 = FStar_List.map update lbs in
                           (b, uu____8674) in
                         (uu____8667, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____8660 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____8659;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___132_8658.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___132_8658.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___132_8658.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___132_8658.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____8687 -> se in
               let normalized_module =
                 let uu___133_8689 = m1 in
                 let uu____8690 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___133_8689.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____8690;
                   FStar_Syntax_Syntax.exports =
                     (uu___133_8689.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___133_8689.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____8691 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____8691
             else ());
            (m1, env2)))