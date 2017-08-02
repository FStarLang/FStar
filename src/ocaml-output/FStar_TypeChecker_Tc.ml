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
          let uu___95_15 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___95_15.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___95_15.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___95_15.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___95_15.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___95_15.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___95_15.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___95_15.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___95_15.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___95_15.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___95_15.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___95_15.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___95_15.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___95_15.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___95_15.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___95_15.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___95_15.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___95_15.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___95_15.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___95_15.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___95_15.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___95_15.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___95_15.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___95_15.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___95_15.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___95_15.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___95_15.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___95_15.FStar_TypeChecker_Env.identifier_info)
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
          let uu___96_31 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___96_31.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___96_31.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___96_31.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___96_31.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___96_31.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___96_31.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___96_31.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___96_31.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___96_31.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___96_31.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___96_31.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___96_31.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___96_31.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___96_31.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___96_31.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___96_31.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___96_31.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___96_31.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___96_31.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___96_31.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___96_31.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___96_31.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___96_31.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___96_31.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___96_31.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___96_31.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___96_31.FStar_TypeChecker_Env.identifier_info)
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
            let uu____61 =
              let uu____62 = FStar_Syntax_Subst.compress h' in
              uu____62.FStar_Syntax_Syntax.n in
            (match uu____61 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> env.FStar_TypeChecker_Env.is_native_tactic tac_lid
             | uu____66 -> false)
        | uu____67 -> false
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____80 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____80 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____104 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____104
         then
           let uu____105 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____105
         else ());
        (let uu____107 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____107 with
         | (t',uu____115,uu____116) ->
             ((let uu____118 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____118
               then
                 let uu____119 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____119
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
        let uu____133 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____133
let check_nogen:
  'Auu____142 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____142 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k in
        let uu____162 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1 in
        ([], uu____162)
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
        let fail uu____192 =
          let uu____193 =
            let uu____194 =
              let uu____199 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____199, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____194 in
          FStar_Exn.raise uu____193 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____239)::(wp,uu____241)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____256 -> fail ())
        | uu____257 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____269 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____269 with
      | (effect_params_un,signature_un,opening) ->
          let uu____279 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____279 with
           | (effect_params,env,uu____288) ->
               let uu____289 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____289 with
                | (signature,uu____295) ->
                    let ed1 =
                      let uu___97_297 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___97_297.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___97_297.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___97_297.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___97_297.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___97_297.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___97_297.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___97_297.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___97_297.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___97_297.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___97_297.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___97_297.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___97_297.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___97_297.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___97_297.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___97_297.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___97_297.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___97_297.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____303 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening
                                (FStar_Pervasives_Native.snd ts) in
                            ([], t1) in
                          let uu___98_334 = ed1 in
                          let uu____335 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____336 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____337 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____338 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____339 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____340 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____341 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____342 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____343 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____344 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____345 =
                            let uu____346 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            FStar_Pervasives_Native.snd uu____346 in
                          let uu____357 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____358 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____359 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___99_367 = a in
                                 let uu____368 =
                                   let uu____369 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   FStar_Pervasives_Native.snd uu____369 in
                                 let uu____380 =
                                   let uu____381 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   FStar_Pervasives_Native.snd uu____381 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___99_367.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___99_367.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___99_367.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___99_367.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____368;
                                   FStar_Syntax_Syntax.action_typ = uu____380
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___98_334.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___98_334.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___98_334.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___98_334.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___98_334.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____335;
                            FStar_Syntax_Syntax.bind_wp = uu____336;
                            FStar_Syntax_Syntax.if_then_else = uu____337;
                            FStar_Syntax_Syntax.ite_wp = uu____338;
                            FStar_Syntax_Syntax.stronger = uu____339;
                            FStar_Syntax_Syntax.close_wp = uu____340;
                            FStar_Syntax_Syntax.assert_p = uu____341;
                            FStar_Syntax_Syntax.assume_p = uu____342;
                            FStar_Syntax_Syntax.null_wp = uu____343;
                            FStar_Syntax_Syntax.trivial = uu____344;
                            FStar_Syntax_Syntax.repr = uu____345;
                            FStar_Syntax_Syntax.return_repr = uu____357;
                            FStar_Syntax_Syntax.bind_repr = uu____358;
                            FStar_Syntax_Syntax.actions = uu____359
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____418 =
                          let uu____419 =
                            let uu____424 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____424, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____419 in
                        FStar_Exn.raise uu____418 in
                      let uu____431 =
                        let uu____432 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____432.FStar_Syntax_Syntax.n in
                      match uu____431 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____467)::(wp,uu____469)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____484 -> fail signature1)
                      | uu____485 -> fail signature1 in
                    let uu____486 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____486 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____508 =
                           let uu____509 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____509 with
                           | (signature1,uu____521) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____523 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____523 in
                         ((let uu____525 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____525
                           then
                             let uu____526 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____527 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____528 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____529 =
                               let uu____530 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____530 in
                             let uu____531 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____526 uu____527 uu____528 uu____529
                               uu____531
                           else ());
                          (let check_and_gen' env2 uu____547 k =
                             match uu____547 with
                             | (uu____555,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____565 =
                                 let uu____572 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____573 =
                                   let uu____576 =
                                     let uu____577 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____577 in
                                   [uu____576] in
                                 uu____572 :: uu____573 in
                               let uu____578 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____565 uu____578 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____582 = fresh_effect_signature () in
                             match uu____582 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____598 =
                                     let uu____605 =
                                       let uu____606 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____606 in
                                     [uu____605] in
                                   let uu____607 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____598
                                     uu____607 in
                                 let expected_k =
                                   let uu____613 =
                                     let uu____620 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_range in
                                     let uu____621 =
                                       let uu____624 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____625 =
                                         let uu____628 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____629 =
                                           let uu____632 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____633 =
                                             let uu____636 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____636] in
                                           uu____632 :: uu____633 in
                                         uu____628 :: uu____629 in
                                       uu____624 :: uu____625 in
                                     uu____620 :: uu____621 in
                                   let uu____637 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____613
                                     uu____637 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____642 =
                                 let uu____643 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____643
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____642 in
                             let expected_k =
                               let uu____655 =
                                 let uu____662 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____663 =
                                   let uu____666 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____667 =
                                     let uu____670 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____671 =
                                       let uu____674 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____674] in
                                     uu____670 :: uu____671 in
                                   uu____666 :: uu____667 in
                                 uu____662 :: uu____663 in
                               let uu____675 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____655 uu____675 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____682 =
                                 let uu____689 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____690 =
                                   let uu____693 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____693] in
                                 uu____689 :: uu____690 in
                               let uu____694 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____682 uu____694 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____698 = FStar_Syntax_Util.type_u () in
                             match uu____698 with
                             | (t,uu____704) ->
                                 let expected_k =
                                   let uu____708 =
                                     let uu____715 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____716 =
                                       let uu____719 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____720 =
                                         let uu____723 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____723] in
                                       uu____719 :: uu____720 in
                                     uu____715 :: uu____716 in
                                   let uu____724 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____708
                                     uu____724 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____729 =
                                 let uu____730 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____730
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____729 in
                             let b_wp_a =
                               let uu____742 =
                                 let uu____749 =
                                   let uu____750 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____750 in
                                 [uu____749] in
                               let uu____751 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____742 uu____751 in
                             let expected_k =
                               let uu____757 =
                                 let uu____764 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____765 =
                                   let uu____768 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____769 =
                                     let uu____772 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____772] in
                                   uu____768 :: uu____769 in
                                 uu____764 :: uu____765 in
                               let uu____773 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____757 uu____773 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____780 =
                                 let uu____787 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____788 =
                                   let uu____791 =
                                     let uu____792 =
                                       let uu____793 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____793
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____792 in
                                   let uu____802 =
                                     let uu____805 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____805] in
                                   uu____791 :: uu____802 in
                                 uu____787 :: uu____788 in
                               let uu____806 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____780 uu____806 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____813 =
                                 let uu____820 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____821 =
                                   let uu____824 =
                                     let uu____825 =
                                       let uu____826 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____826
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____825 in
                                   let uu____835 =
                                     let uu____838 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____838] in
                                   uu____824 :: uu____835 in
                                 uu____820 :: uu____821 in
                               let uu____839 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____813 uu____839 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____846 =
                                 let uu____853 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____853] in
                               let uu____854 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____846 uu____854 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____858 = FStar_Syntax_Util.type_u () in
                             match uu____858 with
                             | (t,uu____864) ->
                                 let expected_k =
                                   let uu____868 =
                                     let uu____875 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____876 =
                                       let uu____879 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____879] in
                                     uu____875 :: uu____876 in
                                   let uu____880 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____868
                                     uu____880 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____883 =
                             let uu____894 =
                               let uu____895 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____895.FStar_Syntax_Syntax.n in
                             match uu____894 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____910 ->
                                 let repr =
                                   let uu____912 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____912 with
                                   | (t,uu____918) ->
                                       let expected_k =
                                         let uu____922 =
                                           let uu____929 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____930 =
                                             let uu____933 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____933] in
                                           uu____929 :: uu____930 in
                                         let uu____934 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____922
                                           uu____934 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____947 =
                                     let uu____950 =
                                       let uu____951 =
                                         let uu____966 =
                                           let uu____969 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____970 =
                                             let uu____973 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____973] in
                                           uu____969 :: uu____970 in
                                         (repr1, uu____966) in
                                       FStar_Syntax_Syntax.Tm_app uu____951 in
                                     FStar_Syntax_Syntax.mk uu____950 in
                                   uu____947 FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____988 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____988 wp in
                                 let destruct_repr t =
                                   let uu____1001 =
                                     let uu____1002 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____1002.FStar_Syntax_Syntax.n in
                                   match uu____1001 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____1013,(t1,uu____1015)::(wp,uu____1017)::[])
                                       -> (t1, wp)
                                   | uu____1060 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____1071 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_All.pipe_right uu____1071
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____1072 = fresh_effect_signature () in
                                   match uu____1072 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____1088 =
                                           let uu____1095 =
                                             let uu____1096 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____1096 in
                                           [uu____1095] in
                                         let uu____1097 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____1088
                                           uu____1097 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           FStar_Pervasives_Native.None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           FStar_Pervasives_Native.None
                                           a_wp_b in
                                       let x_a =
                                         let uu____1103 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           FStar_Pervasives_Native.None
                                           uu____1103 in
                                       let wp_g_x =
                                         let uu____1107 =
                                           let uu____1108 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____1109 =
                                             let uu____1110 =
                                               let uu____1111 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1111 in
                                             [uu____1110] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____1108 uu____1109 in
                                         uu____1107
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____1120 =
                                             let uu____1121 =
                                               let uu____1122 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right
                                                 uu____1122
                                                 FStar_Pervasives_Native.snd in
                                             let uu____1131 =
                                               let uu____1132 =
                                                 let uu____1135 =
                                                   let uu____1138 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____1139 =
                                                     let uu____1142 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____1143 =
                                                       let uu____1146 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____1147 =
                                                         let uu____1150 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____1150] in
                                                       uu____1146 ::
                                                         uu____1147 in
                                                     uu____1142 :: uu____1143 in
                                                   uu____1138 :: uu____1139 in
                                                 r :: uu____1135 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1132 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____1121 uu____1131 in
                                           uu____1120
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____1156 =
                                           let uu____1163 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1164 =
                                             let uu____1167 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____1168 =
                                               let uu____1171 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____1172 =
                                                 let uu____1175 =
                                                   let uu____1176 =
                                                     let uu____1177 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____1177 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____1176 in
                                                 let uu____1178 =
                                                   let uu____1181 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____1182 =
                                                     let uu____1185 =
                                                       let uu____1186 =
                                                         let uu____1187 =
                                                           let uu____1194 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____1194] in
                                                         let uu____1195 =
                                                           let uu____1198 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____1198 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____1187
                                                           uu____1195 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____1186 in
                                                     [uu____1185] in
                                                   uu____1181 :: uu____1182 in
                                                 uu____1175 :: uu____1178 in
                                               uu____1171 :: uu____1172 in
                                             uu____1167 :: uu____1168 in
                                           uu____1163 :: uu____1164 in
                                         let uu____1199 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____1156
                                           uu____1199 in
                                       let uu____1202 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____1202 with
                                        | (expected_k1,uu____1210,uu____1211)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___100_1216 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___100_1216.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___100_1216.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___100_1216.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___100_1216.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.is_native_tactic);
                                                FStar_TypeChecker_Env.identifier_info
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.identifier_info)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1226 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a"
                                       FStar_Pervasives_Native.None
                                       uu____1226 in
                                   let res =
                                     let wp =
                                       let uu____1233 =
                                         let uu____1234 =
                                           let uu____1235 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1235
                                             FStar_Pervasives_Native.snd in
                                         let uu____1244 =
                                           let uu____1245 =
                                             let uu____1248 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1249 =
                                               let uu____1252 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1252] in
                                             uu____1248 :: uu____1249 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1245 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1234 uu____1244 in
                                       uu____1233
                                         FStar_Pervasives_Native.None
                                         FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1258 =
                                       let uu____1265 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1266 =
                                         let uu____1269 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1269] in
                                       uu____1265 :: uu____1266 in
                                     let uu____1270 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1258
                                       uu____1270 in
                                   let uu____1273 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1273 with
                                   | (expected_k1,uu____1287,uu____1288) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (FStar_Pervasives_Native.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1292 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1292 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1313 ->
                                                 FStar_Exn.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1338 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1338 with
                                     | (act_typ,uu____1346,g_t) ->
                                         let env' =
                                           let uu___101_1349 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___101_1349.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___101_1349.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___101_1349.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___101_1349.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___101_1349.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___101_1349.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___101_1349.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___101_1349.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___101_1349.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___101_1349.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___101_1349.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___101_1349.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___101_1349.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___101_1349.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.is_native_tactic);
                                             FStar_TypeChecker_Env.identifier_info
                                               =
                                               (uu___101_1349.FStar_TypeChecker_Env.identifier_info)
                                           } in
                                         ((let uu____1351 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1351
                                           then
                                             let uu____1352 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1353 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1352 uu____1353
                                           else ());
                                          (let uu____1355 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1355 with
                                           | (act_defn,uu____1363,g_a) ->
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
                                               let uu____1367 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1395 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1395 with
                                                      | (bs1,uu____1405) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1412 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1412 in
                                                          let uu____1415 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1415
                                                           with
                                                           | (k1,uu____1427,g)
                                                               -> (k1, g)))
                                                 | uu____1429 ->
                                                     let uu____1430 =
                                                       let uu____1431 =
                                                         let uu____1436 =
                                                           let uu____1437 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1438 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1437
                                                             uu____1438 in
                                                         (uu____1436,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1431 in
                                                     FStar_Exn.raise
                                                       uu____1430 in
                                               (match uu____1367 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1447 =
                                                        let uu____1448 =
                                                          let uu____1449 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1449 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1448 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1447);
                                                     (let act_typ2 =
                                                        let uu____1453 =
                                                          let uu____1454 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1454.FStar_Syntax_Syntax.n in
                                                        match uu____1453 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1477 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1477
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1486
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1486
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1508
                                                                    =
                                                                    let uu____1509
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1509] in
                                                                    let uu____1510
                                                                    =
                                                                    let uu____1519
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1519] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1508;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1510;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1520
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1520))
                                                        | uu____1523 ->
                                                            failwith "" in
                                                      let uu____1526 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1526 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let act_typ4 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              univs1 act_typ3 in
                                                          let uu___102_1535 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___102_1535.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___102_1535.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___102_1535.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ4
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____883 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1559 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1559 in
                               let uu____1562 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1562 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1570 =
                                        let uu____1575 =
                                          let uu____1576 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1576.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1575) in
                                      match uu____1570 with
                                      | ([],uu____1579) -> t1
                                      | (uu____1590,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1591,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1609 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1622 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1622 in
                                      let m =
                                        FStar_List.length
                                          (FStar_Pervasives_Native.fst ts1) in
                                      (let uu____1627 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1629 =
                                               FStar_Syntax_Util.is_unknown
                                                 (FStar_Pervasives_Native.snd
                                                    ts1) in
                                             Prims.op_Negation uu____1629))
                                           && (m <> n1) in
                                       if uu____1627
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1644 =
                                           let uu____1645 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1646 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1645 uu____1646 in
                                         failwith uu____1644
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1652 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1652 with
                                      | (univs2,defn) ->
                                          let uu____1659 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1659 with
                                           | (univs',typ) ->
                                               let uu___103_1669 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___103_1669.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___103_1669.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___103_1669.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___104_1674 = ed2 in
                                      let uu____1675 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1676 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1677 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1678 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1679 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1680 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1681 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1682 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1683 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1684 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1685 =
                                        let uu____1686 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1686 in
                                      let uu____1697 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1698 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1699 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___104_1674.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___104_1674.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1675;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1676;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1677;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1678;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1679;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1680;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1681;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1682;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1683;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1684;
                                        FStar_Syntax_Syntax.repr = uu____1685;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1697;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1698;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1699
                                      } in
                                    ((let uu____1703 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1703
                                      then
                                        let uu____1704 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1704
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
      let uu____1724 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1724 with
      | (effect_binders_un,signature_un) ->
          let uu____1741 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1741 with
           | (effect_binders,env1,uu____1760) ->
               let uu____1761 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1761 with
                | (signature,uu____1777) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1797  ->
                           match uu____1797 with
                           | (bv,qual) ->
                               let uu____1808 =
                                 let uu___105_1809 = bv in
                                 let uu____1810 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___105_1809.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___105_1809.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1810
                                 } in
                               (uu____1808, qual)) effect_binders in
                    let uu____1813 =
                      let uu____1820 =
                        let uu____1821 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1821.FStar_Syntax_Syntax.n in
                      match uu____1820 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1831)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1853 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1813 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1877 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1877
                           then
                             let uu____1878 =
                               let uu____1881 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____1881 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1878
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1915 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1915 with
                           | (t2,comp,uu____1928) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1935 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1935 with
                          | (repr,_comp) ->
                              ((let uu____1957 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1957
                                then
                                  let uu____1958 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1958
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
                                  let uu____1964 =
                                    let uu____1965 =
                                      let uu____1966 =
                                        let uu____1981 =
                                          let uu____1988 =
                                            let uu____1993 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1994 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1993, uu____1994) in
                                          [uu____1988] in
                                        (wp_type1, uu____1981) in
                                      FStar_Syntax_Syntax.Tm_app uu____1966 in
                                    mk1 uu____1965 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1964 in
                                let effect_signature =
                                  let binders =
                                    let uu____2019 =
                                      let uu____2024 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2024) in
                                    let uu____2025 =
                                      let uu____2032 =
                                        let uu____2033 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2033
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2032] in
                                    uu____2019 :: uu____2025 in
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
                                  let uu____2096 = item in
                                  match uu____2096 with
                                  | (u_item,item1) ->
                                      let uu____2117 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2117 with
                                       | (item2,item_comp) ->
                                           ((let uu____2133 =
                                               let uu____2134 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2134 in
                                             if uu____2133
                                             then
                                               let uu____2135 =
                                                 let uu____2136 =
                                                   let uu____2137 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2138 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2137 uu____2138 in
                                                 FStar_Errors.Err uu____2136 in
                                               FStar_Exn.raise uu____2135
                                             else ());
                                            (let uu____2140 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2140 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2160 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2160 with
                                | (dmff_env1,uu____2184,bind_wp,bind_elab) ->
                                    let uu____2187 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2187 with
                                     | (dmff_env2,uu____2211,return_wp,return_elab)
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
                                           let uu____2218 =
                                             let uu____2219 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2219.FStar_Syntax_Syntax.n in
                                           match uu____2218 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2263 =
                                                 let uu____2278 =
                                                   let uu____2283 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2283 in
                                                 match uu____2278 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2347 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2263 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2386 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2386 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2403 =
                                                          let uu____2404 =
                                                            let uu____2419 =
                                                              let uu____2426
                                                                =
                                                                let uu____2431
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2432
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2431,
                                                                  uu____2432) in
                                                              [uu____2426] in
                                                            (wp_type1,
                                                              uu____2419) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2404 in
                                                        mk1 uu____2403 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2447 =
                                                      let uu____2456 =
                                                        let uu____2457 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2457 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2456 in
                                                    (match uu____2447 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2476
                                                           =
                                                           let error_msg =
                                                             let uu____2478 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2478
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
                                                                (let uu____2484
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
                                                                   uu____2484
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
                                                             let uu____2511 =
                                                               let uu____2512
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2513
                                                                 =
                                                                 let uu____2514
                                                                   =
                                                                   let uu____2521
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2521,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2514] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2512
                                                                 uu____2513 in
                                                             uu____2511
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2546 =
                                                             let uu____2547 =
                                                               let uu____2554
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2554] in
                                                             b11 ::
                                                               uu____2547 in
                                                           let uu____2559 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2546
                                                             uu____2559
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2560 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2562 =
                                             let uu____2563 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2563.FStar_Syntax_Syntax.n in
                                           match uu____2562 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2607 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2607
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2620 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2622 =
                                             let uu____2623 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2623.FStar_Syntax_Syntax.n in
                                           match uu____2622 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2650 =
                                                 let uu____2651 =
                                                   let uu____2654 =
                                                     let uu____2655 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2655 in
                                                   [uu____2654] in
                                                 FStar_List.append uu____2651
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2650 body what
                                           | uu____2656 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2674 =
                                                let uu____2675 =
                                                  let uu____2676 =
                                                    let uu____2691 =
                                                      let uu____2692 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2692 in
                                                    (t, uu____2691) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2676 in
                                                mk1 uu____2675 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2674) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2722 = f a2 in
                                               [uu____2722]
                                           | x::xs ->
                                               let uu____2727 =
                                                 apply_last1 f xs in
                                               x :: uu____2727 in
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
                                           let uu____2747 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2747 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____2777 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2777
                                                 then
                                                   let uu____2778 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2778
                                                 else ());
                                                (let uu____2780 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2780))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____2789 =
                                                 let uu____2794 = mk_lid name in
                                                 let uu____2795 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2794 uu____2795 in
                                               (match uu____2789 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2799 =
                                                        let uu____2802 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____2802 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____2799);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2872 =
                                             let uu____2875 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2876 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____2875 :: uu____2876 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____2872);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2945 =
                                              let uu____2948 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2949 =
                                                FStar_ST.op_Bang sigelts in
                                              uu____2948 :: uu____2949 in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____2945);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____3018 =
                                               let uu____3021 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3022 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3021 :: uu____3022 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3018);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____3091 =
                                                let uu____3094 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____3095 =
                                                  FStar_ST.op_Bang sigelts in
                                                uu____3094 :: uu____3095 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____3091);
                                             (let uu____3162 =
                                                FStar_List.fold_left
                                                  (fun uu____3202  ->
                                                     fun action  ->
                                                       match uu____3202 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3223 =
                                                             let uu____3230 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3230
                                                               params_un in
                                                           (match uu____3223
                                                            with
                                                            | (action_params,env',uu____3239)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3259
                                                                     ->
                                                                    match uu____3259
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3270
                                                                    =
                                                                    let uu___106_3271
                                                                    = bv in
                                                                    let uu____3272
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___106_3271.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___106_3271.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3272
                                                                    } in
                                                                    (uu____3270,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3276
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3276
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
                                                                    uu____3306
                                                                    ->
                                                                    let uu____3307
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3307 in
                                                                    ((
                                                                    let uu____3311
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3311
                                                                    then
                                                                    let uu____3312
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3313
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3314
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3315
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3312
                                                                    uu____3313
                                                                    uu____3314
                                                                    uu____3315
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
                                                                    let uu____3319
                                                                    =
                                                                    let uu____3322
                                                                    =
                                                                    let uu___107_3323
                                                                    = action in
                                                                    let uu____3324
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3325
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___107_3323.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___107_3323.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___107_3323.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3324;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3325
                                                                    } in
                                                                    uu____3322
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3319))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3162 with
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
                                                      let uu____3358 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3359 =
                                                        let uu____3362 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3362] in
                                                      uu____3358 ::
                                                        uu____3359 in
                                                    let uu____3363 =
                                                      let uu____3364 =
                                                        let uu____3365 =
                                                          let uu____3366 =
                                                            let uu____3381 =
                                                              let uu____3388
                                                                =
                                                                let uu____3393
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3394
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3393,
                                                                  uu____3394) in
                                                              [uu____3388] in
                                                            (repr,
                                                              uu____3381) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3366 in
                                                        mk1 uu____3365 in
                                                      let uu____3409 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3364
                                                        uu____3409 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3363
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3412 =
                                                    let uu____3419 =
                                                      let uu____3420 =
                                                        let uu____3423 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3423 in
                                                      uu____3420.FStar_Syntax_Syntax.n in
                                                    match uu____3419 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3433)
                                                        ->
                                                        let uu____3462 =
                                                          let uu____3479 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3479
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3537 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3462
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3587 =
                                                               let uu____3588
                                                                 =
                                                                 let uu____3591
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3591 in
                                                               uu____3588.FStar_Syntax_Syntax.n in
                                                             (match uu____3587
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3616
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3616
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3629
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3654
                                                                     ->
                                                                    match uu____3654
                                                                    with
                                                                    | 
                                                                    (bv,uu____3660)
                                                                    ->
                                                                    let uu____3661
                                                                    =
                                                                    let uu____3662
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3662
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3661
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3629
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
                                                                    uu____3721
                                                                    ->
                                                                    let uu____3728
                                                                    =
                                                                    let uu____3729
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____3729 in
                                                                    failwith
                                                                    uu____3728 in
                                                                    let uu____3734
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____3737
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____3734,
                                                                    uu____3737)))
                                                              | uu____3744 ->
                                                                  let uu____3745
                                                                    =
                                                                    let uu____3746
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3746 in
                                                                  failwith
                                                                    uu____3745))
                                                    | uu____3753 ->
                                                        let uu____3754 =
                                                          let uu____3755 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____3755 in
                                                        failwith uu____3754 in
                                                  (match uu____3412 with
                                                   | (pre,post) ->
                                                       ((let uu____3779 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____3781 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____3783 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___108_3785
                                                             = ed in
                                                           let uu____3786 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____3787 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____3788 =
                                                             let uu____3789 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____3789) in
                                                           let uu____3796 =
                                                             let uu____3797 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____3797) in
                                                           let uu____3804 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____3805 =
                                                             let uu____3806 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____3806) in
                                                           let uu____3813 =
                                                             let uu____3814 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____3814) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3786;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3787;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3788;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3796;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___108_3785.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3804;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3805;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3813;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____3821 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____3821
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3839
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____3839
                                                               then
                                                                 let uu____3840
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____3840
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
                                                                    let uu____3852
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3864
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____3864) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3855 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3852;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____3879
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____3879
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____3881
                                                                 =
                                                                 let uu____3884
                                                                   =
                                                                   let uu____3887
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____3887 in
                                                                 FStar_List.append
                                                                   uu____3884
                                                                   sigelts' in
                                                               (uu____3881,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____3936 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____3936 Prims.list ->
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
                (lex_t1,[],[],t,uu____3979,uu____3980);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____3982;
              FStar_Syntax_Syntax.sigattrs = uu____3983;_}::{
                                                              FStar_Syntax_Syntax.sigel
                                                                =
                                                                FStar_Syntax_Syntax.Sig_datacon
                                                                (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____3987);
                                                              FStar_Syntax_Syntax.sigrng
                                                                = r1;
                                                              FStar_Syntax_Syntax.sigquals
                                                                = [];
                                                              FStar_Syntax_Syntax.sigmeta
                                                                = uu____3989;
                                                              FStar_Syntax_Syntax.sigattrs
                                                                = uu____3990;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____3994);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____3996;
                FStar_Syntax_Syntax.sigattrs = uu____3997;_}::[]
              when
              ((_0_39 = (Prims.parse_int "0")) &&
                 (_0_40 = (Prims.parse_int "0")))
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
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                } in
              let utop =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r1) in
              let lex_top_t =
                let uu____4062 =
                  let uu____4065 =
                    let uu____4066 =
                      let uu____4073 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant
                          FStar_Pervasives_Native.None in
                      (uu____4073, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____4066 in
                  FStar_Syntax_Syntax.mk uu____4065 in
                uu____4062 FStar_Pervasives_Native.None r1 in
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
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                } in
              let ucons1 =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r2) in
              let ucons2 =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r2) in
              let lex_cons_t =
                let a =
                  let uu____4091 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1))
                      FStar_Pervasives_Native.None r2 in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4091 in
                let hd1 =
                  let uu____4093 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4093 in
                let tl1 =
                  let uu____4095 =
                    let uu____4096 =
                      let uu____4099 =
                        let uu____4100 =
                          let uu____4107 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant
                              FStar_Pervasives_Native.None in
                          (uu____4107, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____4100 in
                      FStar_Syntax_Syntax.mk uu____4099 in
                    uu____4096 FStar_Pervasives_Native.None r2 in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4095 in
                let res =
                  let uu____4116 =
                    let uu____4119 =
                      let uu____4120 =
                        let uu____4127 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant
                            FStar_Pervasives_Native.None in
                        (uu____4127,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____4120 in
                    FStar_Syntax_Syntax.mk uu____4119 in
                  uu____4116 FStar_Pervasives_Native.None r2 in
                let uu____4133 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a,
                     (FStar_Pervasives_Native.Some
                        FStar_Syntax_Syntax.imp_tag));
                  (hd1, FStar_Pervasives_Native.None);
                  (tl1, FStar_Pervasives_Native.None)] uu____4133 in
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
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                } in
              let uu____4172 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____4172;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }
          | uu____4177 ->
              let uu____4180 =
                let uu____4181 =
                  let uu____4182 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____4182 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____4181 in
              failwith uu____4180
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
            let uu____4212 = FStar_Syntax_Util.type_u () in
            match uu____4212 with
            | (k,uu____4218) ->
                let phi1 =
                  let uu____4220 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4220
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4222 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4222 with
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
          let uu____4268 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4268 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4301 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4301 FStar_List.flatten in
              ((let uu____4315 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4315
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
                          let uu____4326 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4336,uu____4337,uu____4338,uu____4339,uu____4340)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4349 -> failwith "Impossible!" in
                          match uu____4326 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4360 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4364,uu____4365,uu____4366,uu____4367,uu____4368)
                        -> lid
                    | uu____4377 -> failwith "Impossible" in
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
                  let uu____4395 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4395
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
                     let uu____4418 =
                       let uu____4421 =
                         let uu____4422 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4422;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4421 :: ses1 in
                     (uu____4418, data_ops_ses)) in
                (let uu____4432 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4468 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4493 ->
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
           let uu____4545 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4545 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4584 = FStar_Options.set_options t s in
             match uu____4584 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 FStar_Exn.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s1 ->
                 FStar_Exn.raise
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
                ((let uu____4610 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4610 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4618 = cps_and_elaborate env1 ne in
           (match uu____4618 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___109_4655 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___109_4655.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___109_4655.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___109_4655.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___109_4655.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___110_4657 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___110_4657.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___110_4657.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___110_4657.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___110_4657.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___111_4665 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___111_4665.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___111_4665.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___111_4665.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___111_4665.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4673 =
             let uu____4680 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4680 in
           (match uu____4673 with
            | (a,wp_a_src) ->
                let uu____4695 =
                  let uu____4702 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4702 in
                (match uu____4695 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4718 =
                         let uu____4721 =
                           let uu____4722 =
                             let uu____4729 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4729) in
                           FStar_Syntax_Syntax.NT uu____4722 in
                         [uu____4721] in
                       FStar_Syntax_Subst.subst uu____4718 wp_b_tgt in
                     let expected_k =
                       let uu____4733 =
                         let uu____4740 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4741 =
                           let uu____4744 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4744] in
                         uu____4740 :: uu____4741 in
                       let uu____4745 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4733 uu____4745 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4766 =
                           let uu____4767 =
                             let uu____4772 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____4773 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____4772, uu____4773) in
                           FStar_Errors.Error uu____4767 in
                         FStar_Exn.raise uu____4766 in
                       let uu____4776 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____4776 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____4808 =
                             let uu____4809 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____4809 in
                           if uu____4808
                           then no_reify eff_name
                           else
                             (let uu____4815 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____4816 =
                                let uu____4819 =
                                  let uu____4820 =
                                    let uu____4835 =
                                      let uu____4838 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____4839 =
                                        let uu____4842 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____4842] in
                                      uu____4838 :: uu____4839 in
                                    (repr, uu____4835) in
                                  FStar_Syntax_Syntax.Tm_app uu____4820 in
                                FStar_Syntax_Syntax.mk uu____4819 in
                              uu____4816 FStar_Pervasives_Native.None
                                uu____4815) in
                     let uu____4848 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____4876,lift_wp)) ->
                           let uu____4900 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____4900)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____4926 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____4926
                             then
                               let uu____4927 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____4927
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____4930 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____4930 with
                             | (lift1,comp,uu____4945) ->
                                 let uu____4946 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____4946 with
                                  | (uu____4959,lift_wp,lift_elab) ->
                                      let uu____4962 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____4963 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____4848 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___112_5004 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___112_5004.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___112_5004.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___112_5004.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___112_5004.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___112_5004.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___112_5004.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___112_5004.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___112_5004.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___112_5004.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___112_5004.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___112_5004.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___112_5004.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___112_5004.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___112_5004.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___112_5004.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___112_5004.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___112_5004.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___112_5004.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___112_5004.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___112_5004.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___112_5004.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___112_5004.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___112_5004.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___112_5004.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___112_5004.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___112_5004.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___112_5004.FStar_TypeChecker_Env.identifier_info)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5010,lift1)
                                ->
                                let uu____5022 =
                                  let uu____5029 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5029 in
                                (match uu____5022 with
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
                                         let uu____5053 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5054 =
                                           let uu____5057 =
                                             let uu____5058 =
                                               let uu____5073 =
                                                 let uu____5076 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5077 =
                                                   let uu____5080 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5080] in
                                                 uu____5076 :: uu____5077 in
                                               (lift_wp1, uu____5073) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5058 in
                                           FStar_Syntax_Syntax.mk uu____5057 in
                                         uu____5054
                                           FStar_Pervasives_Native.None
                                           uu____5053 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5089 =
                                         let uu____5096 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5097 =
                                           let uu____5100 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5101 =
                                             let uu____5104 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5104] in
                                           uu____5100 :: uu____5101 in
                                         uu____5096 :: uu____5097 in
                                       let uu____5105 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5089
                                         uu____5105 in
                                     let uu____5108 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5108 with
                                      | (expected_k2,uu____5118,uu____5119)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___113_5122 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___113_5122.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___113_5122.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___114_5124 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___114_5124.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___114_5124.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___114_5124.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___114_5124.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5143 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5143 with
            | (tps1,c1) ->
                let uu____5158 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5158 with
                 | (tps2,env3,us) ->
                     let uu____5176 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5176 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5197 =
                              let uu____5198 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5198 in
                            match uu____5197 with
                            | (uvs1,t) ->
                                let uu____5213 =
                                  let uu____5226 =
                                    let uu____5231 =
                                      let uu____5232 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5232.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5231) in
                                  match uu____5226 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5247,c4)) -> ([], c4)
                                  | (uu____5287,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5314 -> failwith "Impossible" in
                                (match uu____5213 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5358 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5358 with
                                         | (uu____5363,t1) ->
                                             let uu____5365 =
                                               let uu____5366 =
                                                 let uu____5371 =
                                                   let uu____5372 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5373 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5374 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5372 uu____5373
                                                     uu____5374 in
                                                 (uu____5371, r) in
                                               FStar_Errors.Error uu____5366 in
                                             FStar_Exn.raise uu____5365)
                                      else ();
                                      (let se1 =
                                         let uu___115_5377 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___115_5377.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___115_5377.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___115_5377.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___115_5377.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5394,uu____5395,uu____5396) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___89_5400  ->
                   match uu___89_5400 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5401 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5406,uu____5407) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___89_5415  ->
                   match uu___89_5415 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5416 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5426 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5426
             then
               let uu____5427 =
                 let uu____5428 =
                   let uu____5433 =
                     FStar_Util.format1
                       "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                       (FStar_Ident.text_of_lid lid) in
                   (uu____5433, r) in
                 FStar_Errors.Error uu____5428 in
               FStar_Exn.raise uu____5427
             else ());
            (let uu____5435 =
               if uvs = []
               then
                 let uu____5436 =
                   let uu____5437 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5437 in
                 check_and_gen env2 t uu____5436
               else
                 (let uu____5443 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5443 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5451 =
                          let uu____5452 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5452 in
                        tc_check_trivial_guard env2 t1 uu____5451 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5458 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5458)) in
             match uu____5435 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___116_5474 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___116_5474.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___116_5474.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___116_5474.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___116_5474.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5484 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5484 with
            | (uu____5497,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5507 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5507 with
            | (e1,c,g1) ->
                let uu____5525 =
                  let uu____5532 =
                    let uu____5535 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5535 in
                  let uu____5536 =
                    let uu____5541 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5541) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5532 uu____5536 in
                (match uu____5525 with
                 | (e2,uu____5555,g) ->
                     ((let uu____5558 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5558);
                      (let se1 =
                         let uu___117_5560 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_5560.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_5560.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_5560.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___117_5560.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5611 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5611
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5619 =
                      let uu____5620 =
                        let uu____5625 =
                          let uu____5626 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5627 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5628 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5626 uu____5627 uu____5628 in
                        (uu____5625, r) in
                      FStar_Errors.Error uu____5620 in
                    FStar_Exn.raise uu____5619) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____5654 =
                   let uu____5655 = FStar_Syntax_Subst.compress def in
                   uu____5655.FStar_Syntax_Syntax.n in
                 match uu____5654 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5665,uu____5666)
                     -> binders
                 | uu____5687 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5697;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5775) -> val_bs1
                     | (uu____5798,[]) -> val_bs1
                     | ((body_bv,uu____5822)::bt,(val_bv,aqual)::vt) ->
                         let uu____5859 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____5875) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___118_5877 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___119_5880 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___119_5880.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___118_5877.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___118_5877.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____5859 in
                   let uu____5881 =
                     let uu____5884 =
                       let uu____5885 =
                         let uu____5898 = rename_binders1 def_bs val_bs in
                         (uu____5898, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____5885 in
                     FStar_Syntax_Syntax.mk uu____5884 in
                   uu____5881 FStar_Pervasives_Native.None r1
               | uu____5916 -> typ1 in
             let uu___120_5917 = lb in
             let uu____5918 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___120_5917.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___120_5917.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____5918;
               FStar_Syntax_Syntax.lbeff =
                 (uu___120_5917.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___120_5917.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____5921 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____5972  ->
                     fun lb  ->
                       match uu____5972 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6014 =
                             let uu____6025 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6025 with
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
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____6110 ->
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_ascribed
                                            ((lb.FStar_Syntax_Syntax.lbdef),
                                              ((FStar_Util.Inl
                                                  (lb.FStar_Syntax_Syntax.lbtyp)),
                                                FStar_Pervasives_Native.None),
                                              FStar_Pervasives_Native.None))
                                         FStar_Pervasives_Native.None
                                         (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos in
                                 (if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inline universes are incoherent with annotation from val declaration",
                                           r))
                                  else ();
                                  (let uu____6153 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6153, quals_opt1))) in
                           (match uu____6014 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____5921 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6247 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___90_6251  ->
                                match uu___90_6251 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6252 -> false)) in
                      if uu____6247
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6262 =
                    let uu____6265 =
                      let uu____6266 =
                        let uu____6279 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6279) in
                      FStar_Syntax_Syntax.Tm_let uu____6266 in
                    FStar_Syntax_Syntax.mk uu____6265 in
                  uu____6262 FStar_Pervasives_Native.None r in
                let uu____6297 =
                  let uu____6308 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___121_6317 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___121_6317.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___121_6317.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___121_6317.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___121_6317.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___121_6317.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___121_6317.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___121_6317.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___121_6317.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___121_6317.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___121_6317.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___121_6317.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___121_6317.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___121_6317.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___121_6317.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___121_6317.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___121_6317.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___121_6317.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___121_6317.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___121_6317.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___121_6317.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___121_6317.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___121_6317.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___121_6317.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___121_6317.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___121_6317.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___121_6317.FStar_TypeChecker_Env.identifier_info)
                       }) e in
                  match uu____6308 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6330;
                       FStar_Syntax_Syntax.vars = uu____6331;_},uu____6332,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6361 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6361) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6379,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6384 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___91_6390  ->
                             match uu___91_6390 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____6393 =
                                   let uu____6394 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____6401 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____6401)
                                          else ();
                                          ok)
                                       (FStar_Pervasives_Native.snd lbs2) in
                                   Prims.op_Negation uu____6394 in
                                 if uu____6393
                                 then FStar_Pervasives_Native.None
                                 else
                                   FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> FStar_Pervasives_Native.Some q) quals1 in
                      ((let uu___122_6416 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___122_6416.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___122_6416.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___122_6416.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6425 -> failwith "impossible" in
                (match uu____6297 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6474 = log env2 in
                       if uu____6474
                       then
                         let uu____6475 =
                           let uu____6476 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6491 =
                                         let uu____6500 =
                                           let uu____6501 =
                                             let uu____6504 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6504.FStar_Syntax_Syntax.fv_name in
                                           uu____6501.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6500 in
                                       match uu____6491 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6511 -> false in
                                     if should_log
                                     then
                                       let uu____6520 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6521 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6520 uu____6521
                                     else "")) in
                           FStar_All.pipe_right uu____6476
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6475
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6552 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6552 with
                              | (bs1,c1) ->
                                  let uu____6559 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6559
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6571 =
                                            let uu____6572 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6572.FStar_Syntax_Syntax.n in
                                          (match uu____6571 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6597 =
                                                 let uu____6598 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6598.FStar_Syntax_Syntax.n in
                                               (match uu____6597 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6608 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6608 in
                                                    let uu____6609 =
                                                      let uu____6610 =
                                                        let uu____6611 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6611 args in
                                                      uu____6610
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6609 u
                                                | uu____6614 -> c1)
                                           | uu____6615 -> c1)
                                      | uu____6616 -> c1 in
                                    let uu___123_6617 = t1 in
                                    let uu____6618 =
                                      let uu____6619 =
                                        let uu____6632 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6632) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6619 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6618;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___123_6617.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___123_6617.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6656 =
                               let uu____6657 = FStar_Syntax_Subst.compress h in
                               uu____6657.FStar_Syntax_Syntax.n in
                             (match uu____6656 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6667 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6667 in
                                  let uu____6668 =
                                    let uu____6669 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6669
                                      args in
                                  uu____6668 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6672 -> t1)
                         | uu____6673 -> t1 in
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
                           let uu____6701 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6701 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6718 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____6718, (FStar_Pervasives_Native.snd x)))
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
                           let uu____6749 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6749 in
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
                         let uu___124_6756 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___125_6768 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_6768.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_6768.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_6768.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_6768.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___124_6756.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___124_6756.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___124_6756.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___124_6756.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6785 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____6785 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____6819 =
                                    let uu____6820 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6820.FStar_Syntax_Syntax.n in
                                  (match uu____6819 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____6853 =
                                           let uu____6856 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____6856.FStar_Syntax_Syntax.fv_name in
                                         uu____6853.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____6858 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____6858 in
                                       let uu____6859 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____6861 =
                                              let uu____6862 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____6862 in
                                            Prims.op_Negation uu____6861) in
                                       if uu____6859
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
                                   | uu____6904 ->
                                       FStar_Pervasives_Native.None))
                         | uu____6909 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____6931 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____6931
                             then
                               let uu____6932 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____6933 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____6932 uu____6933
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
             (fun uu___92_6986  ->
                match uu___92_6986 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____6987 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____6993) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____6999 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7008 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7013 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____7038 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7062) ->
          let uu____7071 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7071
          then
            let for_export_bundle se1 uu____7102 =
              match uu____7102 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7141,uu____7142) ->
                       let dec =
                         let uu___126_7152 = se1 in
                         let uu____7153 =
                           let uu____7154 =
                             let uu____7161 =
                               let uu____7164 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7164 in
                             (l, us, uu____7161) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7154 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7153;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___126_7152.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___126_7152.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___126_7152.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7176,uu____7177,uu____7178) ->
                       let dec =
                         let uu___127_7184 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___127_7184.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___127_7184.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___127_7184.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7189 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7211,uu____7212,uu____7213) ->
          let uu____7214 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7214 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7235 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7235
          then
            ([(let uu___128_7251 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___128_7251.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___128_7251.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___128_7251.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7253 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___93_7257  ->
                       match uu___93_7257 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7258 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7263 -> true
                       | uu____7264 -> false)) in
             if uu____7253 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7282 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7287 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7292 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7297 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7302 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7320) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7337 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7337
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
          let uu____7368 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7368
          then
            let uu____7377 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___129_7390 = se in
                      let uu____7391 =
                        let uu____7392 =
                          let uu____7399 =
                            let uu____7400 =
                              let uu____7403 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7403.FStar_Syntax_Syntax.fv_name in
                            uu____7400.FStar_Syntax_Syntax.v in
                          (uu____7399, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7392 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7391;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___129_7390.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___129_7390.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___129_7390.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7377, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7425 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7442 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____7458 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____7462 = FStar_Options.using_facts_from () in
                 match uu____7462 with
                 | FStar_Pervasives_Native.Some ns ->
                     let proof_ns =
                       let uu____7483 =
                         let uu____7492 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____7492 [([], false)] in
                       [uu____7483] in
                     let uu___130_7547 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___130_7547.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___130_7547.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___130_7547.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___130_7547.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___130_7547.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___130_7547.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___130_7547.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___130_7547.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___130_7547.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___130_7547.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___130_7547.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___130_7547.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___130_7547.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___130_7547.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___130_7547.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___130_7547.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___130_7547.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___130_7547.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___130_7547.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___130_7547.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___130_7547.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___130_7547.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___130_7547.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___130_7547.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___130_7547.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___130_7547.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___130_7547.FStar_TypeChecker_Env.identifier_info)
                     }
                 | FStar_Pervasives_Native.None  -> env))
           | uu____7550 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7551 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7561 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7561) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7562,uu____7563,uu____7564) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_7568  ->
                  match uu___94_7568 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7569 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7570,uu____7571) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_7579  ->
                  match uu___94_7579 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7580 -> false))
          -> env
      | uu____7581 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7643 se =
        match uu____7643 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7696 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7696
              then
                let uu____7697 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7697
              else ());
             (let uu____7699 = tc_decl env1 se in
              match uu____7699 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7749 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7749
                             then
                               let uu____7750 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7750
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  (FStar_TypeChecker_Env.promote_id_info env1
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
                    (let uu____7773 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____7773
                     then
                       let uu____7774 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7780 =
                                  let uu____7781 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____7781 "\n" in
                                Prims.strcat s uu____7780) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____7774
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7786 =
                       let accum_exports_hidden uu____7816 se1 =
                         match uu____7816 with
                         | (exports1,hidden1) ->
                             let uu____7844 = for_export hidden1 se1 in
                             (match uu____7844 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____7786 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___131_7923 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___131_7923.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___131_7923.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___131_7923.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___131_7923.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8001 = acc in
        match uu____8001 with
        | (uu____8036,uu____8037,env1,uu____8039) ->
            let uu____8052 =
              FStar_Util.record_time
                (fun uu____8098  -> process_one_decl acc se) in
            (match uu____8052 with
             | (r,ms_elapsed) ->
                 ((let uu____8162 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8162
                   then
                     let uu____8163 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8164 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8163 uu____8164
                   else ());
                  r)) in
      let uu____8166 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8166 with
      | (ses1,exports,env1,uu____8214) ->
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
      (let uu____8253 = FStar_Options.debug_any () in
       if uu____8253
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
         let uu___132_8259 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___132_8259.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___132_8259.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___132_8259.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___132_8259.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___132_8259.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___132_8259.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___132_8259.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___132_8259.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___132_8259.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___132_8259.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___132_8259.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___132_8259.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___132_8259.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___132_8259.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___132_8259.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___132_8259.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___132_8259.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___132_8259.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___132_8259.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___132_8259.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___132_8259.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___132_8259.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___132_8259.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___132_8259.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___132_8259.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___132_8259.FStar_TypeChecker_Env.identifier_info)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____8262 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____8262 with
        | (ses,exports,env3) ->
            ((let uu___133_8295 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___133_8295.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___133_8295.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___133_8295.FStar_Syntax_Syntax.is_interface)
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
        let uu____8320 = tc_decls env decls in
        match uu____8320 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___134_8351 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___134_8351.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___134_8351.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___134_8351.FStar_Syntax_Syntax.is_interface)
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
          let uu___135_8371 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___135_8371.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___135_8371.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___135_8371.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___135_8371.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___135_8371.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___135_8371.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___135_8371.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___135_8371.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___135_8371.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___135_8371.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___135_8371.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___135_8371.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___135_8371.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___135_8371.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___135_8371.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___135_8371.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___135_8371.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___135_8371.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___135_8371.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___135_8371.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___135_8371.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___135_8371.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___135_8371.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___135_8371.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___135_8371.FStar_TypeChecker_Env.identifier_info)
          } in
        let check_term lid univs1 t =
          let uu____8382 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8382 with
          | (univs2,t1) ->
              ((let uu____8390 =
                  let uu____8391 =
                    let uu____8394 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8394 in
                  FStar_All.pipe_left uu____8391
                    (FStar_Options.Other "Exports") in
                if uu____8390
                then
                  let uu____8395 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8396 =
                    let uu____8397 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8397
                      (FStar_String.concat ", ") in
                  let uu____8406 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8395 uu____8396 uu____8406
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8409 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8409 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____8433 =
             let uu____8434 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8435 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8434 uu____8435 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8433);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8442) ->
              let uu____8451 =
                let uu____8452 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8452 in
              if uu____8451
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8462,uu____8463) ->
              let t =
                let uu____8475 =
                  let uu____8478 =
                    let uu____8479 =
                      let uu____8492 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8492) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8479 in
                  FStar_Syntax_Syntax.mk uu____8478 in
                uu____8475 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8499,uu____8500,uu____8501) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8509 =
                let uu____8510 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8510 in
              if uu____8509 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8514,lbs),uu____8516) ->
              let uu____8531 =
                let uu____8532 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8532 in
              if uu____8531
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
              let uu____8551 =
                let uu____8552 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8552 in
              if uu____8551
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8559 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8560 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8567 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8568 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8569 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8570 -> () in
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
          let uu___136_8589 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___136_8589.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___136_8589.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____8592 =
           let uu____8593 = FStar_Options.lax () in
           Prims.op_Negation uu____8593 in
         if uu____8592 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____8599 =
           let uu____8600 = FStar_Options.interactive () in
           Prims.op_Negation uu____8600 in
         if uu____8599
         then
           let uu____8601 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____8601 FStar_Pervasives.ignore
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
      let uu____8615 = tc_partial_modul env modul in
      match uu____8615 with
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
      (let uu____8648 = FStar_Options.debug_any () in
       if uu____8648
       then
         let uu____8649 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8649
       else ());
      (let env1 =
         let uu___137_8653 = env in
         let uu____8654 =
           let uu____8655 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8655 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___137_8653.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___137_8653.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___137_8653.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___137_8653.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___137_8653.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___137_8653.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___137_8653.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___137_8653.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___137_8653.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___137_8653.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___137_8653.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___137_8653.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___137_8653.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___137_8653.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___137_8653.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___137_8653.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___137_8653.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___137_8653.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8654;
           FStar_TypeChecker_Env.lax_universes =
             (uu___137_8653.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___137_8653.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___137_8653.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___137_8653.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___137_8653.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___137_8653.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___137_8653.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___137_8653.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___137_8653.FStar_TypeChecker_Env.identifier_info)
         } in
       let uu____8656 = tc_modul env1 m in
       match uu____8656 with
       | (m1,env2) ->
           ((let uu____8668 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8668
             then
               let uu____8669 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8669
             else ());
            (let uu____8672 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8672
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
                       let uu____8703 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8703 with
                       | (univnames1,e) ->
                           let uu___138_8710 = lb in
                           let uu____8711 =
                             let uu____8714 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____8714 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___138_8710.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___138_8710.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___138_8710.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___138_8710.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____8711
                           } in
                     let uu___139_8715 = se in
                     let uu____8716 =
                       let uu____8717 =
                         let uu____8724 =
                           let uu____8731 = FStar_List.map update lbs in
                           (b, uu____8731) in
                         (uu____8724, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____8717 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____8716;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___139_8715.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___139_8715.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___139_8715.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___139_8715.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____8744 -> se in
               let normalized_module =
                 let uu___140_8746 = m1 in
                 let uu____8747 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___140_8746.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____8747;
                   FStar_Syntax_Syntax.exports =
                     (uu___140_8746.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___140_8746.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____8748 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____8748
             else ());
            (m1, env2)))