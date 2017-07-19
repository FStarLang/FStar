open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for () in
      match uu____7 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____12 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____12 l in
          let uu___89_13 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___89_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___89_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___89_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___89_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___89_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___89_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___89_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___89_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___89_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___89_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___89_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___89_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___89_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___89_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___89_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___89_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___89_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___89_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___89_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___89_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___89_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___89_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___89_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")))
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____22 = FStar_TypeChecker_Env.current_module env in
                let uu____23 =
                  let uu____24 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____24 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____22 uu____23
            | l::uu____26 -> l in
          let uu___90_29 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___90_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___90_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___90_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___90_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___90_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___90_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___90_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___90_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___90_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___90_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___90_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___90_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___90_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___90_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___90_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___90_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___90_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___90_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___90_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___90_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___90_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___90_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___90_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")))
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____37 =
         let uu____38 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____38 in
       Prims.op_Negation uu____37)
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____48 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____48 with
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
        (let uu____72 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____72
         then
           let uu____73 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____73
         else ());
        (let uu____75 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____75 with
         | (t',uu____83,uu____84) ->
             ((let uu____86 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____86
               then
                 let uu____87 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____87
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
        let uu____98 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____98
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____123 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____123)
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
        let fail uu____154 =
          let uu____155 =
            let uu____156 =
              let uu____161 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____161, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____156 in
          raise uu____155 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____211)::(wp,uu____213)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____230 -> fail ())
        | uu____231 -> fail ()
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____315 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____315 with
      | (effect_params_un,signature_un,opening) ->
          let uu____325 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____325 with
           | (effect_params,env,uu____334) ->
               let uu____335 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____335 with
                | (signature,uu____341) ->
                    let ed1 =
                      let uu___91_343 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___91_343.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___91_343.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___91_343.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___91_343.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___91_343.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___91_343.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___91_343.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___91_343.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___91_343.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___91_343.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___91_343.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___91_343.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___91_343.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___91_343.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___91_343.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___91_343.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___91_343.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____349 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening
                                (FStar_Pervasives_Native.snd ts) in
                            ([], t1) in
                          let uu___92_380 = ed1 in
                          let uu____381 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____382 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____383 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____384 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____385 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____386 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____387 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____388 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____389 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____390 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____391 =
                            let uu____392 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            FStar_Pervasives_Native.snd uu____392 in
                          let uu____403 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____404 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____405 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___93_409 = a in
                                 let uu____410 =
                                   let uu____411 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   FStar_Pervasives_Native.snd uu____411 in
                                 let uu____422 =
                                   let uu____423 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   FStar_Pervasives_Native.snd uu____423 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___93_409.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___93_409.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___93_409.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___93_409.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____410;
                                   FStar_Syntax_Syntax.action_typ = uu____422
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___92_380.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___92_380.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___92_380.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___92_380.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___92_380.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____381;
                            FStar_Syntax_Syntax.bind_wp = uu____382;
                            FStar_Syntax_Syntax.if_then_else = uu____383;
                            FStar_Syntax_Syntax.ite_wp = uu____384;
                            FStar_Syntax_Syntax.stronger = uu____385;
                            FStar_Syntax_Syntax.close_wp = uu____386;
                            FStar_Syntax_Syntax.assert_p = uu____387;
                            FStar_Syntax_Syntax.assume_p = uu____388;
                            FStar_Syntax_Syntax.null_wp = uu____389;
                            FStar_Syntax_Syntax.trivial = uu____390;
                            FStar_Syntax_Syntax.repr = uu____391;
                            FStar_Syntax_Syntax.return_repr = uu____403;
                            FStar_Syntax_Syntax.bind_repr = uu____404;
                            FStar_Syntax_Syntax.actions = uu____405
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____464 =
                          let uu____465 =
                            let uu____470 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____470, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____465 in
                        raise uu____464 in
                      let uu____479 =
                        let uu____480 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____480.FStar_Syntax_Syntax.n in
                      match uu____479 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____525)::(wp,uu____527)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____544 -> fail signature1)
                      | uu____545 -> fail signature1 in
                    let uu____546 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____546 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____576 =
                           let uu____577 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____577 with
                           | (signature1,uu____591) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____593 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____593 in
                         ((let uu____595 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____595
                           then
                             let uu____596 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____597 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____598 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____599 =
                               let uu____600 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____600 in
                             let uu____601 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____596 uu____597 uu____598 uu____599
                               uu____601
                           else ());
                          (let check_and_gen' env2 uu____617 k =
                             match uu____617 with
                             | (uu____625,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____637 =
                                 let uu____644 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____645 =
                                   let uu____648 =
                                     let uu____649 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____649 in
                                   [uu____648] in
                                 uu____644 :: uu____645 in
                               let uu____650 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____637 uu____650 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____656 = fresh_effect_signature () in
                             match uu____656 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____680 =
                                     let uu____687 =
                                       let uu____688 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____688 in
                                     [uu____687] in
                                   let uu____689 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____680
                                     uu____689 in
                                 let expected_k =
                                   let uu____699 =
                                     let uu____706 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____707 =
                                       let uu____710 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____711 =
                                         let uu____714 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____715 =
                                           let uu____718 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____719 =
                                             let uu____722 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____722] in
                                           uu____718 :: uu____719 in
                                         uu____714 :: uu____715 in
                                       uu____710 :: uu____711 in
                                     uu____706 :: uu____707 in
                                   let uu____723 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____699
                                     uu____723 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____730 =
                                 let uu____731 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____731
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____730 in
                             let expected_k =
                               let uu____745 =
                                 let uu____752 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____753 =
                                   let uu____756 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____757 =
                                     let uu____760 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____761 =
                                       let uu____764 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____764] in
                                     uu____760 :: uu____761 in
                                   uu____756 :: uu____757 in
                                 uu____752 :: uu____753 in
                               let uu____765 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____745 uu____765 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____776 =
                                 let uu____783 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____784 =
                                   let uu____787 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____787] in
                                 uu____783 :: uu____784 in
                               let uu____788 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____776 uu____788 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____794 = FStar_Syntax_Util.type_u () in
                             match uu____794 with
                             | (t,uu____800) ->
                                 let expected_k =
                                   let uu____806 =
                                     let uu____813 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____814 =
                                       let uu____817 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____818 =
                                         let uu____821 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____821] in
                                       uu____817 :: uu____818 in
                                     uu____813 :: uu____814 in
                                   let uu____822 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____806
                                     uu____822 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____829 =
                                 let uu____830 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____830
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____829 in
                             let b_wp_a =
                               let uu____844 =
                                 let uu____851 =
                                   let uu____852 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____852 in
                                 [uu____851] in
                               let uu____853 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____844 uu____853 in
                             let expected_k =
                               let uu____863 =
                                 let uu____870 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____871 =
                                   let uu____874 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____875 =
                                     let uu____878 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____878] in
                                   uu____874 :: uu____875 in
                                 uu____870 :: uu____871 in
                               let uu____879 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____863 uu____879 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____890 =
                                 let uu____897 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____898 =
                                   let uu____901 =
                                     let uu____902 =
                                       let uu____903 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____903
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____902 in
                                   let uu____912 =
                                     let uu____915 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____915] in
                                   uu____901 :: uu____912 in
                                 uu____897 :: uu____898 in
                               let uu____916 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____890 uu____916 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____927 =
                                 let uu____934 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____935 =
                                   let uu____938 =
                                     let uu____939 =
                                       let uu____940 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____940
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____939 in
                                   let uu____949 =
                                     let uu____952 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____952] in
                                   uu____938 :: uu____949 in
                                 uu____934 :: uu____935 in
                               let uu____953 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____927 uu____953 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____964 =
                                 let uu____971 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____971] in
                               let uu____972 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____964 uu____972 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____978 = FStar_Syntax_Util.type_u () in
                             match uu____978 with
                             | (t,uu____984) ->
                                 let expected_k =
                                   let uu____990 =
                                     let uu____997 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____998 =
                                       let uu____1001 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____1001] in
                                     uu____997 :: uu____998 in
                                   let uu____1002 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____990
                                     uu____1002 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____1007 =
                             let uu____1018 =
                               let uu____1019 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____1019.FStar_Syntax_Syntax.n in
                             match uu____1018 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____1036 ->
                                 let repr =
                                   let uu____1038 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____1038 with
                                   | (t,uu____1044) ->
                                       let expected_k =
                                         let uu____1050 =
                                           let uu____1057 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1058 =
                                             let uu____1061 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____1061] in
                                           uu____1057 :: uu____1058 in
                                         let uu____1062 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____1050
                                           uu____1062 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____1079 =
                                     let uu____1084 =
                                       let uu____1085 =
                                         let uu____1104 =
                                           let uu____1107 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____1108 =
                                             let uu____1111 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____1111] in
                                           uu____1107 :: uu____1108 in
                                         (repr1, uu____1104) in
                                       FStar_Syntax_Syntax.Tm_app uu____1085 in
                                     FStar_Syntax_Syntax.mk uu____1084 in
                                   uu____1079 FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____1129 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____1129 wp in
                                 let destruct_repr t =
                                   let uu____1146 =
                                     let uu____1147 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____1147.FStar_Syntax_Syntax.n in
                                   match uu____1146 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____1164,(t1,uu____1166)::(wp,uu____1168)::[])
                                       -> (t1, wp)
                                   | uu____1235 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____1250 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_All.pipe_right uu____1250
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____1251 = fresh_effect_signature () in
                                   match uu____1251 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____1275 =
                                           let uu____1282 =
                                             let uu____1283 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____1283 in
                                           [uu____1282] in
                                         let uu____1284 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____1275
                                           uu____1284 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           FStar_Pervasives_Native.None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           FStar_Pervasives_Native.None
                                           a_wp_b in
                                       let x_a =
                                         let uu____1292 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           FStar_Pervasives_Native.None
                                           uu____1292 in
                                       let wp_g_x =
                                         let uu____1298 =
                                           let uu____1299 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____1300 =
                                             let uu____1301 =
                                               let uu____1302 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1302 in
                                             [uu____1301] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____1299 uu____1300 in
                                         uu____1298
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____1315 =
                                             let uu____1316 =
                                               let uu____1317 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right
                                                 uu____1317
                                                 FStar_Pervasives_Native.snd in
                                             let uu____1326 =
                                               let uu____1327 =
                                                 let uu____1330 =
                                                   let uu____1333 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____1334 =
                                                     let uu____1337 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____1338 =
                                                       let uu____1341 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____1342 =
                                                         let uu____1345 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____1345] in
                                                       uu____1341 ::
                                                         uu____1342 in
                                                     uu____1337 :: uu____1338 in
                                                   uu____1333 :: uu____1334 in
                                                 r :: uu____1330 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1327 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____1316 uu____1326 in
                                           uu____1315
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____1353 =
                                           let uu____1360 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1361 =
                                             let uu____1364 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____1365 =
                                               let uu____1368 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____1369 =
                                                 let uu____1372 =
                                                   let uu____1373 =
                                                     let uu____1374 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____1374 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____1373 in
                                                 let uu____1375 =
                                                   let uu____1378 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____1379 =
                                                     let uu____1382 =
                                                       let uu____1383 =
                                                         let uu____1384 =
                                                           let uu____1391 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____1391] in
                                                         let uu____1392 =
                                                           let uu____1397 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____1397 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____1384
                                                           uu____1392 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____1383 in
                                                     [uu____1382] in
                                                   uu____1378 :: uu____1379 in
                                                 uu____1372 :: uu____1375 in
                                               uu____1368 :: uu____1369 in
                                             uu____1364 :: uu____1365 in
                                           uu____1360 :: uu____1361 in
                                         let uu____1398 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____1353
                                           uu____1398 in
                                       let uu____1403 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____1403 with
                                        | (expected_k1,uu____1411,uu____1412)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___94_1417 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___94_1417.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___94_1417.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___94_1417.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___94_1417.FStar_TypeChecker_Env.qname_and_index)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1427 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a"
                                       FStar_Pervasives_Native.None
                                       uu____1427 in
                                   let res =
                                     let wp =
                                       let uu____1438 =
                                         let uu____1439 =
                                           let uu____1440 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1440
                                             FStar_Pervasives_Native.snd in
                                         let uu____1449 =
                                           let uu____1450 =
                                             let uu____1453 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1454 =
                                               let uu____1457 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1457] in
                                             uu____1453 :: uu____1454 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1450 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1439 uu____1449 in
                                       uu____1438
                                         FStar_Pervasives_Native.None
                                         FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1465 =
                                       let uu____1472 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1473 =
                                         let uu____1476 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1476] in
                                       uu____1472 :: uu____1473 in
                                     let uu____1477 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1465
                                       uu____1477 in
                                   let uu____1482 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1482 with
                                   | (expected_k1,uu____1496,uu____1497) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (FStar_Pervasives_Native.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1501 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1501 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1522 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1541 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1541 with
                                     | (act_typ,uu____1549,g_t) ->
                                         let env' =
                                           let uu___95_1552 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___95_1552.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___95_1552.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___95_1552.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___95_1552.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___95_1552.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___95_1552.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___95_1552.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___95_1552.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___95_1552.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___95_1552.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___95_1552.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___95_1552.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___95_1552.FStar_TypeChecker_Env.qname_and_index)
                                           } in
                                         ((let uu____1554 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1554
                                           then
                                             let uu____1555 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1556 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1555 uu____1556
                                           else ());
                                          (let uu____1558 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1558 with
                                           | (act_defn,uu____1566,g_a) ->
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
                                               let uu____1570 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1602 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1602 with
                                                      | (bs1,uu____1612) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1623 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1623 in
                                                          let uu____1628 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1628
                                                           with
                                                           | (k1,uu____1640,g)
                                                               -> (k1, g)))
                                                 | uu____1642 ->
                                                     let uu____1643 =
                                                       let uu____1644 =
                                                         let uu____1649 =
                                                           let uu____1650 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1651 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1650
                                                             uu____1651 in
                                                         (uu____1649,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1644 in
                                                     raise uu____1643 in
                                               (match uu____1570 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1660 =
                                                        let uu____1661 =
                                                          let uu____1662 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1662 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1661 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1660);
                                                     (let act_typ2 =
                                                        let uu____1668 =
                                                          let uu____1669 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1669.FStar_Syntax_Syntax.n in
                                                        match uu____1668 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1700 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1700
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1711
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1711
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1747
                                                                    =
                                                                    let uu____1748
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1748] in
                                                                    let uu____1749
                                                                    =
                                                                    let uu____1760
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1760] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1747;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1749;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1761
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1761))
                                                        | uu____1766 ->
                                                            failwith "" in
                                                      let uu____1771 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1771 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let uu___96_1779 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___96_1779.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___96_1779.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___96_1779.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____1007 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1805 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1805 in
                               let uu____1810 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1810 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1818 =
                                        let uu____1823 =
                                          let uu____1824 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1824.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1823) in
                                      match uu____1818 with
                                      | ([],uu____1829) -> t1
                                      | (uu____1840,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1841,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1863 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1876 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1876 in
                                      let m =
                                        FStar_List.length
                                          (FStar_Pervasives_Native.fst ts1) in
                                      (let uu____1881 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1882 =
                                               FStar_Syntax_Util.is_unknown
                                                 (FStar_Pervasives_Native.snd
                                                    ts1) in
                                             Prims.op_Negation uu____1882))
                                           && (m <> n1) in
                                       if uu____1881
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1892 =
                                           let uu____1893 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1894 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1893 uu____1894 in
                                         failwith uu____1892
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1900 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1900 with
                                      | (univs2,defn) ->
                                          let uu____1907 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1907 with
                                           | (univs',typ) ->
                                               let uu___97_1917 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___97_1917.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___97_1917.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___97_1917.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___98_1922 = ed2 in
                                      let uu____1923 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1924 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1925 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1926 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1927 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1928 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1929 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1930 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1931 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1932 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1933 =
                                        let uu____1934 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1934 in
                                      let uu____1945 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1946 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1947 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___98_1922.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___98_1922.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1923;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1924;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1925;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1926;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1927;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1928;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1929;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1930;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1931;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1932;
                                        FStar_Syntax_Syntax.repr = uu____1933;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1945;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1946;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1947
                                      } in
                                    ((let uu____1951 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1951
                                      then
                                        let uu____1952 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1952
                                      else ());
                                     ed3)))))))
and cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ed  ->
      let uu____1956 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1956 with
      | (effect_binders_un,signature_un) ->
          let uu____1973 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1973 with
           | (effect_binders,env1,uu____1992) ->
               let uu____1993 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1993 with
                | (signature,uu____2009) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2025  ->
                           match uu____2025 with
                           | (bv,qual) ->
                               let uu____2036 =
                                 let uu___99_2037 = bv in
                                 let uu____2038 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___99_2037.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___99_2037.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2038
                                 } in
                               (uu____2036, qual)) effect_binders in
                    let uu____2043 =
                      let uu____2052 =
                        let uu____2053 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____2053.FStar_Syntax_Syntax.n in
                      match uu____2052 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____2067)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____2095 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____2043 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2125 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____2125
                           then
                             let uu____2126 =
                               let uu____2129 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____2129 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2126
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____2163 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____2163 with
                           | (t2,comp,uu____2176) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2185 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2185 with
                          | (repr,_comp) ->
                              ((let uu____2207 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2207
                                then
                                  let uu____2208 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2208
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
                                  let uu____2214 =
                                    let uu____2215 =
                                      let uu____2216 =
                                        let uu____2235 =
                                          let uu____2242 =
                                            let uu____2247 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2248 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2247, uu____2248) in
                                          [uu____2242] in
                                        (wp_type1, uu____2235) in
                                      FStar_Syntax_Syntax.Tm_app uu____2216 in
                                    mk1 uu____2215 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2214 in
                                let effect_signature =
                                  let binders =
                                    let uu____2275 =
                                      let uu____2280 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2280) in
                                    let uu____2281 =
                                      let uu____2288 =
                                        let uu____2289 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2289
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2288] in
                                    uu____2275 :: uu____2281 in
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
                                  let uu____2354 = item in
                                  match uu____2354 with
                                  | (u_item,item1) ->
                                      let uu____2375 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2375 with
                                       | (item2,item_comp) ->
                                           ((let uu____2391 =
                                               let uu____2392 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2392 in
                                             if uu____2391
                                             then
                                               let uu____2393 =
                                                 let uu____2394 =
                                                   let uu____2395 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2396 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2395 uu____2396 in
                                                 FStar_Errors.Err uu____2394 in
                                               raise uu____2393
                                             else ());
                                            (let uu____2398 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2398 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2418 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2418 with
                                | (dmff_env1,uu____2442,bind_wp,bind_elab) ->
                                    let uu____2445 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2445 with
                                     | (dmff_env2,uu____2469,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____2473 =
                                             let uu____2474 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2474.FStar_Syntax_Syntax.n in
                                           match uu____2473 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2544 =
                                                 let uu____2559 =
                                                   let uu____2564 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2564 in
                                                 match uu____2559 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2638 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2544 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2677 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2677 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2696 =
                                                          let uu____2697 =
                                                            let uu____2716 =
                                                              let uu____2723
                                                                =
                                                                let uu____2728
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2729
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2728,
                                                                  uu____2729) in
                                                              [uu____2723] in
                                                            (wp_type1,
                                                              uu____2716) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2697 in
                                                        mk1 uu____2696 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2744 =
                                                      let uu____2763 =
                                                        let uu____2764 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2764 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2763 in
                                                    (match uu____2744 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2813
                                                           =
                                                           let error_msg =
                                                             let uu____2815 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____2816 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   (FStar_Util.Inl
                                                                   lc) ->
                                                                   FStar_Syntax_Print.lcomp_to_string
                                                                    lc
                                                               | FStar_Pervasives_Native.Some
                                                                   (FStar_Util.Inr
                                                                   (lid,uu____2845))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2815
                                                               uu____2816 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____2894
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____2894
                                                               then
                                                                 let g_opt =
                                                                   FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    lc.FStar_Syntax_Syntax.res_typ
                                                                    FStar_Syntax_Util.ktype0 in
                                                                 (match g_opt
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                  | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ())
                                                               else fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               (FStar_Util.Inr
                                                               (lid,uu____2901))
                                                               ->
                                                               if
                                                                 Prims.op_Negation
                                                                   (FStar_Syntax_Util.is_pure_effect
                                                                    lid)
                                                               then fail ()
                                                               else ());
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
                                                             let uu____2935 =
                                                               let uu____2936
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2937
                                                                 =
                                                                 let uu____2938
                                                                   =
                                                                   let uu____2945
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2945,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2938] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2936
                                                                 uu____2937 in
                                                             uu____2935
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2970 =
                                                             let uu____2971 =
                                                               let uu____2978
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2978] in
                                                             b11 ::
                                                               uu____2971 in
                                                           let uu____2983 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2970
                                                             uu____2983
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Parser_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____3002 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____3004 =
                                             let uu____3005 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____3005.FStar_Syntax_Syntax.n in
                                           match uu____3004 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____3075 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____3075
                                                 (FStar_Pervasives_Native.Some
                                                    (FStar_Util.Inr
                                                       (FStar_Parser_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____3106 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____3108 =
                                             let uu____3109 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____3109.FStar_Syntax_Syntax.n in
                                           match uu____3108 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____3162 =
                                                 let uu____3163 =
                                                   let uu____3166 =
                                                     let uu____3167 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____3167 in
                                                   [uu____3166] in
                                                 FStar_List.append uu____3163
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____3162 body what
                                           | uu____3168 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____3194 =
                                                let uu____3195 =
                                                  let uu____3196 =
                                                    let uu____3215 =
                                                      let uu____3216 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3216 in
                                                    (t, uu____3215) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3196 in
                                                mk1 uu____3195 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3194) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3248 = f a2 in
                                               [uu____3248]
                                           | x::xs ->
                                               let uu____3253 =
                                                 apply_last1 f xs in
                                               x :: uu____3253 in
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
                                           let uu____3271 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____3271 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3301 =
                                                   FStar_Ident.string_of_lid
                                                     l' in
                                                 FStar_Util.print1
                                                   "DM4F: Applying override %s\n"
                                                   uu____3301);
                                                (let uu____3302 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3302))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3311 =
                                                 let uu____3316 = mk_lid name in
                                                 let uu____3317 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3316 uu____3317 in
                                               (match uu____3311 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3331 =
                                                        let uu____3334 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____3334 in
                                                      FStar_ST.write sigelts
                                                        uu____3331);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____3348 =
                                             let uu____3351 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3352 =
                                               FStar_ST.read sigelts in
                                             uu____3351 :: uu____3352 in
                                           FStar_ST.write sigelts uu____3348);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____3365 =
                                              let uu____3368 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____3369 =
                                                FStar_ST.read sigelts in
                                              uu____3368 :: uu____3369 in
                                            FStar_ST.write sigelts uu____3365);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____3382 =
                                               let uu____3385 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3386 =
                                                 FStar_ST.read sigelts in
                                               uu____3385 :: uu____3386 in
                                             FStar_ST.write sigelts
                                               uu____3382);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____3399 =
                                                let uu____3402 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____3403 =
                                                  FStar_ST.read sigelts in
                                                uu____3402 :: uu____3403 in
                                              FStar_ST.write sigelts
                                                uu____3399);
                                             (let uu____3414 =
                                                FStar_List.fold_left
                                                  (fun uu____3427  ->
                                                     fun action  ->
                                                       match uu____3427 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3448 =
                                                             let uu____3455 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3455
                                                               params_un in
                                                           (match uu____3448
                                                            with
                                                            | (action_params,env',uu____3464)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3480
                                                                     ->
                                                                    match uu____3480
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3491
                                                                    =
                                                                    let uu___100_3492
                                                                    = bv in
                                                                    let uu____3493
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___100_3492.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___100_3492.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3493
                                                                    } in
                                                                    (uu____3491,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3499
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3499
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
                                                                    uu____3539
                                                                    ->
                                                                    let uu____3540
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3540 in
                                                                    ((
                                                                    let uu____3546
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3546
                                                                    then
                                                                    let uu____3547
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3548
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3549
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3550
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3547
                                                                    uu____3548
                                                                    uu____3549
                                                                    uu____3550
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
                                                                    let uu____3554
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    let uu___101_3558
                                                                    = action in
                                                                    let uu____3559
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3560
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___101_3558.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___101_3558.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___101_3558.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3559;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3560
                                                                    } in
                                                                    uu____3557
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3554))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3414 with
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
                                                      let uu____3593 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3594 =
                                                        let uu____3597 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3597] in
                                                      uu____3593 ::
                                                        uu____3594 in
                                                    let uu____3598 =
                                                      let uu____3599 =
                                                        let uu____3600 =
                                                          let uu____3601 =
                                                            let uu____3620 =
                                                              let uu____3627
                                                                =
                                                                let uu____3632
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3633
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3632,
                                                                  uu____3633) in
                                                              [uu____3627] in
                                                            (repr,
                                                              uu____3620) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3601 in
                                                        mk1 uu____3600 in
                                                      let uu____3648 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3599
                                                        uu____3648 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3598
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3661 =
                                                    let uu____3670 =
                                                      let uu____3671 =
                                                        let uu____3676 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3676 in
                                                      uu____3671.FStar_Syntax_Syntax.n in
                                                    match uu____3670 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3688)
                                                        ->
                                                        let uu____3741 =
                                                          let uu____3758 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3758
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3816 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3741
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3868 =
                                                               let uu____3869
                                                                 =
                                                                 let uu____3874
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3874 in
                                                               uu____3869.FStar_Syntax_Syntax.n in
                                                             (match uu____3868
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3905
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3905
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3920
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3941
                                                                     ->
                                                                    match uu____3941
                                                                    with
                                                                    | 
                                                                    (bv,uu____3947)
                                                                    ->
                                                                    let uu____3948
                                                                    =
                                                                    let uu____3949
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3949
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3948
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3920
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
                                                                    uu____4010
                                                                    ->
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4018
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____4018 in
                                                                    failwith
                                                                    uu____4017 in
                                                                    let uu____4023
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____4028
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____4023,
                                                                    uu____4028)))
                                                              | uu____4047 ->
                                                                  let uu____4048
                                                                    =
                                                                    let uu____4049
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4049 in
                                                                  failwith
                                                                    uu____4048))
                                                    | uu____4058 ->
                                                        let uu____4059 =
                                                          let uu____4060 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____4060 in
                                                        failwith uu____4059 in
                                                  (match uu____3661 with
                                                   | (pre,post) ->
                                                       ((let uu____4090 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____4092 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____4094 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___102_4096
                                                             = ed in
                                                           let uu____4097 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____4098 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____4099 =
                                                             let uu____4100 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____4100) in
                                                           let uu____4111 =
                                                             let uu____4112 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____4112) in
                                                           let uu____4123 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____4124 =
                                                             let uu____4125 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____4125) in
                                                           let uu____4136 =
                                                             let uu____4137 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____4137) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4097;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4098;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4099;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4111;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___102_4096.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4123;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4124;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4136;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____4148 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____4148
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4166
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____4166
                                                               then
                                                                 let uu____4167
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____4167
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
                                                                    let uu____4179
                                                                    =
                                                                    let uu____4182
                                                                    =
                                                                    let uu____4193
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____4193) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4182 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____4179;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____4214
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4214
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____4216
                                                                 =
                                                                 let uu____4219
                                                                   =
                                                                   let uu____4222
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____4222 in
                                                                 FStar_List.append
                                                                   uu____4219
                                                                   sigelts' in
                                                               (uu____4216,
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
                (lex_t1,[],[],t,uu____4257,uu____4258);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____4260;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_29,uu____4264);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____4266;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_30,uu____4270);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____4272;_}::[]
              when
              ((_0_29 = (Prims.parse_int "0")) &&
                 (_0_30 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top1
                       FStar_Parser_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Parser_Const.lexcons_lid))
              ->
              let u =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r) in
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
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let utop =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r1) in
              let lex_top_t =
                let uu____4335 =
                  let uu____4340 =
                    let uu____4341 =
                      let uu____4350 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant
                          FStar_Pervasives_Native.None in
                      (uu____4350, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____4341 in
                  FStar_Syntax_Syntax.mk uu____4340 in
                uu____4335 FStar_Pervasives_Native.None r1 in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_top1, [utop], lex_top_t1,
                         FStar_Parser_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
                  FStar_Syntax_Syntax.sigrng = r1;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let ucons1 =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r2) in
              let ucons2 =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r2) in
              let lex_cons_t =
                let a =
                  let uu____4371 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1))
                      FStar_Pervasives_Native.None r2 in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4371 in
                let hd1 =
                  let uu____4373 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4373 in
                let tl1 =
                  let uu____4375 =
                    let uu____4376 =
                      let uu____4381 =
                        let uu____4382 =
                          let uu____4391 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant
                              FStar_Pervasives_Native.None in
                          (uu____4391, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____4382 in
                      FStar_Syntax_Syntax.mk uu____4381 in
                    uu____4376 FStar_Pervasives_Native.None r2 in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4375 in
                let res =
                  let uu____4403 =
                    let uu____4408 =
                      let uu____4409 =
                        let uu____4418 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant
                            FStar_Pervasives_Native.None in
                        (uu____4418,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____4409 in
                    FStar_Syntax_Syntax.mk uu____4408 in
                  uu____4403 FStar_Pervasives_Native.None r2 in
                let uu____4425 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a,
                     (FStar_Pervasives_Native.Some
                        FStar_Syntax_Syntax.imp_tag));
                  (hd1, FStar_Pervasives_Native.None);
                  (tl1, FStar_Pervasives_Native.None)] uu____4425 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_cons, [ucons1; ucons2], lex_cons_t1,
                         FStar_Parser_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
                  FStar_Syntax_Syntax.sigrng = r2;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let uu____4466 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____4466;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____4471 ->
              let uu____4474 =
                let uu____4475 =
                  let uu____4476 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____4476 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____4475 in
              failwith uu____4474
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
            let uu____4489 = FStar_Syntax_Util.type_u () in
            match uu____4489 with
            | (k,uu____4495) ->
                let phi1 =
                  let uu____4497 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4497
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
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env0 = env in
          let uu____4510 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____4510 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4543 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____4543 FStar_List.flatten in
              ((let uu____4557 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4557
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
                          let uu____4563 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4573,uu____4574,uu____4575,uu____4576,uu____4577)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4586 -> failwith "Impossible!" in
                          match uu____4563 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4597 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4601,uu____4602,uu____4603,uu____4604,uu____4605)
                        -> lid
                    | uu____4614 -> failwith "Impossible" in
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
                let uu____4621 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Parser_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____4621
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
                   let uu____4643 =
                     let uu____4646 =
                       let uu____4647 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____4647;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____4646 :: ses1 in
                   (uu____4643, data_ops_ses))))
and tc_decl:
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4677 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4702 ->
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
           let uu____4754 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4754 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4793 = FStar_Options.set_options t s in
             match uu____4793 with
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
                ((let uu____4819 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4819 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4827 = cps_and_elaborate env1 ne in
           (match uu____4827 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___103_4863 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___103_4863.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___103_4863.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___103_4863.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___104_4864 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___104_4864.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___104_4864.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___104_4864.FStar_Syntax_Syntax.sigmeta)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___105_4872 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___105_4872.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___105_4872.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___105_4872.FStar_Syntax_Syntax.sigmeta)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4880 =
             let uu____4889 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4889 in
           (match uu____4880 with
            | (a,wp_a_src) ->
                let uu____4908 =
                  let uu____4917 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4917 in
                (match uu____4908 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4937 =
                         let uu____4940 =
                           let uu____4941 =
                             let uu____4950 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4950) in
                           FStar_Syntax_Syntax.NT uu____4941 in
                         [uu____4940] in
                       FStar_Syntax_Subst.subst uu____4937 wp_b_tgt in
                     let expected_k =
                       let uu____4956 =
                         let uu____4963 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4964 =
                           let uu____4967 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4967] in
                         uu____4963 :: uu____4964 in
                       let uu____4968 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4956 uu____4968 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4995 =
                           let uu____4996 =
                             let uu____5001 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____5002 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____5001, uu____5002) in
                           FStar_Errors.Error uu____4996 in
                         raise uu____4995 in
                       let uu____5007 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____5007 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____5041 =
                             let uu____5042 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____5042 in
                           if uu____5041
                           then no_reify eff_name
                           else
                             (let uu____5050 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____5051 =
                                let uu____5056 =
                                  let uu____5057 =
                                    let uu____5076 =
                                      let uu____5079 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____5080 =
                                        let uu____5083 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____5083] in
                                      uu____5079 :: uu____5080 in
                                    (repr, uu____5076) in
                                  FStar_Syntax_Syntax.Tm_app uu____5057 in
                                FStar_Syntax_Syntax.mk uu____5056 in
                              uu____5051 FStar_Pervasives_Native.None
                                uu____5050) in
                     let uu____5090 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5118,lift_wp)) ->
                           let uu____5142 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5142)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5168 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5168
                             then
                               let uu____5169 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5169
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____5172 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5172 with
                             | (lift1,comp,uu____5187) ->
                                 let uu____5188 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5188 with
                                  | (uu____5201,lift_wp,lift_elab) ->
                                      let uu____5204 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5205 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____5090 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___106_5246 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___106_5246.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___106_5246.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___106_5246.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___106_5246.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___106_5246.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___106_5246.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___106_5246.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___106_5246.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___106_5246.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___106_5246.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___106_5246.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___106_5246.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___106_5246.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___106_5246.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___106_5246.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___106_5246.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___106_5246.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___106_5246.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___106_5246.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___106_5246.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___106_5246.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___106_5246.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___106_5246.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5252,lift1)
                                ->
                                let uu____5264 =
                                  let uu____5273 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5273 in
                                (match uu____5264 with
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
                                         let uu____5307 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5308 =
                                           let uu____5313 =
                                             let uu____5314 =
                                               let uu____5333 =
                                                 let uu____5336 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5337 =
                                                   let uu____5340 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5340] in
                                                 uu____5336 :: uu____5337 in
                                               (lift_wp1, uu____5333) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5314 in
                                           FStar_Syntax_Syntax.mk uu____5313 in
                                         uu____5308
                                           FStar_Pervasives_Native.None
                                           uu____5307 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5352 =
                                         let uu____5359 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5360 =
                                           let uu____5363 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5364 =
                                             let uu____5367 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5367] in
                                           uu____5363 :: uu____5364 in
                                         uu____5359 :: uu____5360 in
                                       let uu____5368 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5352
                                         uu____5368 in
                                     let uu____5373 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5373 with
                                      | (expected_k2,uu____5383,uu____5384)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___107_5387 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___107_5387.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___107_5387.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___108_5389 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___108_5389.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___108_5389.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___108_5389.FStar_Syntax_Syntax.sigmeta)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5408 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5408 with
            | (tps1,c1) ->
                let uu____5423 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5423 with
                 | (tps2,env3,us) ->
                     let uu____5441 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5441 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5462 =
                              let uu____5463 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5463 in
                            match uu____5462 with
                            | (uvs1,t) ->
                                let uu____5478 =
                                  let uu____5493 =
                                    let uu____5498 =
                                      let uu____5499 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5499.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5498) in
                                  match uu____5493 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5518,c4)) -> ([], c4)
                                  | (uu____5564,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5597 -> failwith "Impossible" in
                                (match uu____5478 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5647 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5647 with
                                         | (uu____5652,t1) ->
                                             let uu____5654 =
                                               let uu____5655 =
                                                 let uu____5660 =
                                                   let uu____5661 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5662 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5663 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5661 uu____5662
                                                     uu____5663 in
                                                 (uu____5660, r) in
                                               FStar_Errors.Error uu____5655 in
                                             raise uu____5654)
                                      else ();
                                      (let se1 =
                                         let uu___109_5666 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___109_5666.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___109_5666.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___109_5666.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5685,uu____5686,uu____5687) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_5690  ->
                   match uu___83_5690 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5691 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5696,uu____5697,uu____5698) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_5709  ->
                   match uu___83_5709 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5710 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5719 =
             if uvs = []
             then
               let uu____5720 =
                 let uu____5721 = FStar_Syntax_Util.type_u () in
                 FStar_Pervasives_Native.fst uu____5721 in
               check_and_gen env2 t uu____5720
             else
               (let uu____5727 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____5727 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____5735 =
                        let uu____5736 = FStar_Syntax_Util.type_u () in
                        FStar_Pervasives_Native.fst uu____5736 in
                      tc_check_trivial_guard env2 t1 uu____5735 in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
                    let uu____5742 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____5742)) in
           (match uu____5719 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___110_5758 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___110_5758.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___110_5758.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___110_5758.FStar_Syntax_Syntax.sigmeta)
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
           let uu____5775 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5775 with
            | (e1,c,g1) ->
                let uu____5793 =
                  let uu____5800 =
                    let uu____5803 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    FStar_Pervasives_Native.Some uu____5803 in
                  let uu____5804 =
                    let uu____5809 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5809) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5800 uu____5804 in
                (match uu____5793 with
                 | (e2,uu____5827,g) ->
                     ((let uu____5830 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5830);
                      (let se1 =
                         let uu___111_5832 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___111_5832.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___111_5832.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___111_5832.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5888 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5888
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5896 =
                      let uu____5897 =
                        let uu____5902 =
                          let uu____5903 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5904 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5905 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5903 uu____5904 uu____5905 in
                        (uu____5902, r) in
                      FStar_Errors.Error uu____5897 in
                    raise uu____5896) in
           let uu____5910 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____5951  ->
                     fun lb  ->
                       match uu____5951 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____5993 =
                             let uu____6004 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6004 with
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
                                   | uu____6093 ->
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
                                  (let uu____6098 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____6098, quals_opt1))) in
                           (match uu____5993 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____5910 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6194 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___84_6197  ->
                                match uu___84_6197 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6198 -> false)) in
                      if uu____6194
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6210 =
                    let uu____6215 =
                      let uu____6216 =
                        let uu____6231 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6231) in
                      FStar_Syntax_Syntax.Tm_let uu____6216 in
                    FStar_Syntax_Syntax.mk uu____6215 in
                  uu____6210 FStar_Pervasives_Native.None r in
                let uu____6254 =
                  let uu____6265 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___112_6272 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___112_6272.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___112_6272.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___112_6272.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___112_6272.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___112_6272.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___112_6272.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___112_6272.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___112_6272.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___112_6272.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___112_6272.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___112_6272.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___112_6272.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___112_6272.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___112_6272.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___112_6272.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___112_6272.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___112_6272.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___112_6272.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___112_6272.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___112_6272.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___112_6272.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___112_6272.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____6265 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____6285;
                       FStar_Syntax_Syntax.pos = uu____6286;
                       FStar_Syntax_Syntax.vars = uu____6287;_},uu____6288,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6323,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6332 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___85_6336  ->
                             match uu___85_6336 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____6339 =
                                   let uu____6340 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____6344 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____6344)
                                          else ();
                                          ok)
                                       (FStar_Pervasives_Native.snd lbs1) in
                                   Prims.op_Negation uu____6340 in
                                 if uu____6339
                                 then FStar_Pervasives_Native.None
                                 else
                                   FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> FStar_Pervasives_Native.Some q) quals1 in
                      ((let uu___113_6358 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___113_6358.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___113_6358.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____6369 -> failwith "impossible" in
                (match uu____6254 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6416 = log env2 in
                       if uu____6416
                       then
                         let uu____6417 =
                           let uu____6418 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6429 =
                                         let uu____6438 =
                                           let uu____6439 =
                                             let uu____6448 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6448.FStar_Syntax_Syntax.fv_name in
                                           uu____6439.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6438 in
                                       match uu____6429 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6459 -> false in
                                     if should_log
                                     then
                                       let uu____6468 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6469 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6468 uu____6469
                                     else "")) in
                           FStar_All.pipe_right uu____6418
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6417
                       else ());
                      ([se1], [])))))
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
             (fun uu___86_6514  ->
                match uu___86_6514 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____6515 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____6521) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____6527 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____6536 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____6541 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____6566 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6590) ->
          let uu____6599 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____6599
          then
            let for_export_bundle se1 uu____6630 =
              match uu____6630 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____6669,uu____6670) ->
                       let dec =
                         let uu___114_6680 = se1 in
                         let uu____6681 =
                           let uu____6682 =
                             let uu____6689 =
                               let uu____6694 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____6694 in
                             (l, us, uu____6689) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____6682 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____6681;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___114_6680.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___114_6680.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____6710,uu____6711,uu____6712) ->
                       let dec =
                         let uu___115_6718 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___115_6718.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___115_6718.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____6723 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____6745,uu____6746) ->
          let uu____6747 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____6747 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____6768 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____6768
          then
            ([(let uu___116_6783 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___116_6783.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___116_6783.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____6785 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___87_6788  ->
                       match uu___87_6788 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____6789 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____6794 -> true
                       | uu____6795 -> false)) in
             if uu____6785 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____6813 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____6818 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6823 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____6828 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6833 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____6851,uu____6852)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6877 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____6877
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
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____6910) ->
          let uu____6919 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____6919
          then
            let uu____6928 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___117_6938 = se in
                      let uu____6939 =
                        let uu____6940 =
                          let uu____6947 =
                            let uu____6948 =
                              let uu____6957 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____6957.FStar_Syntax_Syntax.fv_name in
                            uu____6948.FStar_Syntax_Syntax.v in
                          (uu____6947, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____6940 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____6939;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___117_6938.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___117_6938.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____6928, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____6983 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7000 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____7016 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                env)
           | uu____7020 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7021 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7028 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7028) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7029,uu____7030,uu____7031) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_7034  ->
                  match uu___88_7034 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7035 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7036,uu____7037,uu____7038) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_7049  ->
                  match uu___88_7049 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7050 -> false))
          -> env
      | uu____7051 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7111 se =
        match uu____7111 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7164 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7164
              then
                let uu____7165 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7165
              else ());
             (let uu____7167 = tc_decl env1 se in
              match uu____7167 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
                  ((let uu____7212 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____7212
                    then
                      let uu____7213 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____7216 =
                                 let uu____7217 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____7217 "\n" in
                               Prims.strcat s uu____7216) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____7213
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____7221 =
                      let accum_exports_hidden uu____7251 se1 =
                        match uu____7251 with
                        | (exports1,hidden1) ->
                            let uu____7279 = for_export hidden1 se1 in
                            (match uu____7279 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____7221 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____7374 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____7374 with
      | (ses1,exports,env1,uu____7422) ->
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
      (let uu____7459 = FStar_Options.debug_any () in
       if uu____7459
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
         let uu___118_7465 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___118_7465.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___118_7465.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___118_7465.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___118_7465.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___118_7465.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___118_7465.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___118_7465.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___118_7465.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___118_7465.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___118_7465.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___118_7465.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___118_7465.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___118_7465.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___118_7465.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___118_7465.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___118_7465.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___118_7465.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___118_7465.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___118_7465.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___118_7465.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___118_7465.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___118_7465.FStar_TypeChecker_Env.qname_and_index)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____7468 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____7468 with
        | (ses,exports,env3) ->
            ((let uu___119_7500 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___119_7500.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___119_7500.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___119_7500.FStar_Syntax_Syntax.is_interface)
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
        let uu____7522 = tc_decls env decls in
        match uu____7522 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___120_7553 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___120_7553.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___120_7553.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___120_7553.FStar_Syntax_Syntax.is_interface)
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
          let uu___121_7570 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___121_7570.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___121_7570.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___121_7570.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___121_7570.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___121_7570.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___121_7570.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___121_7570.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___121_7570.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___121_7570.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___121_7570.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___121_7570.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___121_7570.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___121_7570.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___121_7570.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___121_7570.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___121_7570.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___121_7570.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___121_7570.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___121_7570.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___121_7570.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___121_7570.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs1 t =
          let uu____7581 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____7581 with
          | (univs2,t1) ->
              ((let uu____7589 =
                  let uu____7590 =
                    let uu____7593 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____7593 in
                  FStar_All.pipe_left uu____7590
                    (FStar_Options.Other "Exports") in
                if uu____7589
                then
                  let uu____7594 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____7595 =
                    let uu____7596 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____7596
                      (FStar_String.concat ", ") in
                  let uu____7604 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____7594 uu____7595 uu____7604
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____7607 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____7607 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____7631 =
             let uu____7632 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____7633 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____7632 uu____7633 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____7631);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7640) ->
              let uu____7649 =
                let uu____7650 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____7650 in
              if uu____7649
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____7660,uu____7661) ->
              let t =
                let uu____7675 =
                  let uu____7680 =
                    let uu____7681 =
                      let uu____7696 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____7696) in
                    FStar_Syntax_Syntax.Tm_arrow uu____7681 in
                  FStar_Syntax_Syntax.mk uu____7680 in
                uu____7675 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____7704,uu____7705,uu____7706) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____7714 =
                let uu____7715 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____7715 in
              if uu____7714 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____7719,lbs),uu____7721,uu____7722) ->
              let uu____7741 =
                let uu____7742 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____7742 in
              if uu____7741
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
              let uu____7763 =
                let uu____7764 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____7764 in
              if uu____7763
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp)))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____7773 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____7774 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7779 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7780 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____7781 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____7782 -> () in
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
          let uu___122_7798 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___122_7798.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___122_7798.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____7801 =
           let uu____7802 = FStar_Options.lax () in
           Prims.op_Negation uu____7802 in
         if uu____7801 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____7808 =
           let uu____7809 = FStar_Options.interactive () in
           Prims.op_Negation uu____7809 in
         if uu____7808
         then
           let uu____7810 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____7810 FStar_Pervasives.ignore
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
      let uu____7822 = tc_partial_modul env modul in
      match uu____7822 with
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
      (let uu____7853 = FStar_Options.debug_any () in
       if uu____7853
       then
         let uu____7854 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____7854
       else ());
      (let env1 =
         let uu___123_7858 = env in
         let uu____7859 =
           let uu____7860 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____7860 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_7858.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_7858.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_7858.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_7858.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_7858.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_7858.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_7858.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_7858.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_7858.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_7858.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_7858.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_7858.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___123_7858.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___123_7858.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_7858.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_7858.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___123_7858.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___123_7858.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____7859;
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_7858.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___123_7858.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_7858.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___123_7858.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_7858.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____7861 = tc_modul env1 m in
       match uu____7861 with
       | (m1,env2) ->
           ((let uu____7873 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____7873
             then
               let uu____7874 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____7874
             else ());
            (let uu____7877 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____7877
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
                       let uu____7913 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____7913 with
                       | (univnames1,e) ->
                           let uu___124_7920 = lb in
                           let uu____7921 =
                             let uu____7926 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____7926 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___124_7920.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___124_7920.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___124_7920.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___124_7920.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____7921
                           } in
                     let uu___125_7927 = se in
                     let uu____7928 =
                       let uu____7929 =
                         let uu____7940 =
                           let uu____7947 = FStar_List.map update lbs in
                           (b, uu____7947) in
                         (uu____7940, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____7929 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____7928;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___125_7927.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___125_7927.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___125_7927.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____7962 -> se in
               let normalized_module =
                 let uu___126_7964 = m1 in
                 let uu____7965 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___126_7964.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____7965;
                   FStar_Syntax_Syntax.exports =
                     (uu___126_7964.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___126_7964.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____7966 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____7966
             else ());
            (m1, env2)))