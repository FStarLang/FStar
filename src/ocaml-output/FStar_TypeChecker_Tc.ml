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
            FStar_TypeChecker_Env.failhard =
              (uu___95_15.FStar_TypeChecker_Env.failhard);
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
            FStar_TypeChecker_Env.failhard =
              (uu___96_31.FStar_TypeChecker_Env.failhard);
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
                                                FStar_TypeChecker_Env.failhard
                                                  =
                                                  (uu___100_1216.FStar_TypeChecker_Env.failhard);
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
                                             FStar_TypeChecker_Env.failhard =
                                               (uu___101_1349.FStar_TypeChecker_Env.failhard);
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
                                                            failwith
                                                              "Impossible (expected_k is an arrow)" in
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
                                      | uu____1609 ->
                                          failwith
                                            "Impossible : t is an arrow" in
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
                                         let err_msg =
                                           let uu____1645 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1646 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1645 uu____1646 in
                                         FStar_Exn.raise
                                           (FStar_Errors.Error
                                              (err_msg,
                                                ((FStar_Pervasives_Native.snd
                                                    ts1).FStar_Syntax_Syntax.pos)))
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1654 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1654 with
                                      | (univs2,defn) ->
                                          let uu____1661 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1661 with
                                           | (univs',typ) ->
                                               let uu___103_1671 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___103_1671.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___103_1671.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___103_1671.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___104_1676 = ed2 in
                                      let uu____1677 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1678 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1679 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1680 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1681 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1682 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1683 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1684 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1685 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1686 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1687 =
                                        let uu____1688 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1688 in
                                      let uu____1699 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1700 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1701 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___104_1676.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___104_1676.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1677;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1678;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1679;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1680;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1681;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1682;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1683;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1684;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1685;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1686;
                                        FStar_Syntax_Syntax.repr = uu____1687;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1699;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1700;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1701
                                      } in
                                    ((let uu____1705 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1705
                                      then
                                        let uu____1706 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1706
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
      let uu____1726 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1726 with
      | (effect_binders_un,signature_un) ->
          let uu____1743 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1743 with
           | (effect_binders,env1,uu____1762) ->
               let uu____1763 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1763 with
                | (signature,uu____1779) ->
                    let raise_error err_msg =
                      FStar_Exn.raise
                        (FStar_Errors.Error
                           (err_msg, (signature.FStar_Syntax_Syntax.pos))) in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1807  ->
                           match uu____1807 with
                           | (bv,qual) ->
                               let uu____1818 =
                                 let uu___105_1819 = bv in
                                 let uu____1820 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___105_1819.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___105_1819.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1820
                                 } in
                               (uu____1818, qual)) effect_binders in
                    let uu____1823 =
                      let uu____1830 =
                        let uu____1831 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1831.FStar_Syntax_Syntax.n in
                      match uu____1830 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1841)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1863 ->
                          raise_error
                            "bad shape for effect-for-free signature" in
                    (match uu____1823 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1887 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1887
                           then
                             let uu____1888 =
                               let uu____1891 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____1891 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1888
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1925 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1925 with
                           | (t2,comp,uu____1938) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1945 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1945 with
                          | (repr,_comp) ->
                              ((let uu____1967 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1967
                                then
                                  let uu____1968 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1968
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
                                  let uu____1974 =
                                    let uu____1975 =
                                      let uu____1976 =
                                        let uu____1991 =
                                          let uu____1998 =
                                            let uu____2003 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2004 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2003, uu____2004) in
                                          [uu____1998] in
                                        (wp_type1, uu____1991) in
                                      FStar_Syntax_Syntax.Tm_app uu____1976 in
                                    mk1 uu____1975 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1974 in
                                let effect_signature =
                                  let binders =
                                    let uu____2029 =
                                      let uu____2034 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2034) in
                                    let uu____2035 =
                                      let uu____2042 =
                                        let uu____2043 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2043
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2042] in
                                    uu____2029 :: uu____2035 in
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
                                  let uu____2106 = item in
                                  match uu____2106 with
                                  | (u_item,item1) ->
                                      let uu____2127 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2127 with
                                       | (item2,item_comp) ->
                                           ((let uu____2143 =
                                               let uu____2144 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2144 in
                                             if uu____2143
                                             then
                                               let uu____2145 =
                                                 let uu____2146 =
                                                   let uu____2147 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2148 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2147 uu____2148 in
                                                 FStar_Errors.Err uu____2146 in
                                               FStar_Exn.raise uu____2145
                                             else ());
                                            (let uu____2150 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2150 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2170 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2170 with
                                | (dmff_env1,uu____2194,bind_wp,bind_elab) ->
                                    let uu____2197 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2197 with
                                     | (dmff_env2,uu____2221,return_wp,return_elab)
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
                                           let uu____2228 =
                                             let uu____2229 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2229.FStar_Syntax_Syntax.n in
                                           match uu____2228 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2273 =
                                                 let uu____2288 =
                                                   let uu____2293 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2293 in
                                                 match uu____2288 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2357 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2273 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2396 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2396 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2413 =
                                                          let uu____2414 =
                                                            let uu____2429 =
                                                              let uu____2436
                                                                =
                                                                let uu____2441
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2442
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2441,
                                                                  uu____2442) in
                                                              [uu____2436] in
                                                            (wp_type1,
                                                              uu____2429) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2414 in
                                                        mk1 uu____2413 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2457 =
                                                      let uu____2466 =
                                                        let uu____2467 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2467 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2466 in
                                                    (match uu____2457 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2486
                                                           =
                                                           let error_msg =
                                                             let uu____2488 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2488
                                                               (match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                           raise_error
                                                             error_msg in
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
                                                                (let uu____2494
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
                                                                   uu____2494
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
                                                             let uu____2521 =
                                                               let uu____2522
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2523
                                                                 =
                                                                 let uu____2524
                                                                   =
                                                                   let uu____2531
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2531,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2524] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2522
                                                                 uu____2523 in
                                                             uu____2521
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2556 =
                                                             let uu____2557 =
                                                               let uu____2564
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2564] in
                                                             b11 ::
                                                               uu____2557 in
                                                           let uu____2569 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2556
                                                             uu____2569
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2570 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2572 =
                                             let uu____2573 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2573.FStar_Syntax_Syntax.n in
                                           match uu____2572 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2617 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2617
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2630 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2632 =
                                             let uu____2633 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2633.FStar_Syntax_Syntax.n in
                                           match uu____2632 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2660 =
                                                 let uu____2661 =
                                                   let uu____2664 =
                                                     let uu____2665 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2665 in
                                                   [uu____2664] in
                                                 FStar_List.append uu____2661
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2660 body what
                                           | uu____2666 ->
                                               raise_error
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2684 =
                                                let uu____2685 =
                                                  let uu____2686 =
                                                    let uu____2701 =
                                                      let uu____2702 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2702 in
                                                    (t, uu____2701) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2686 in
                                                mk1 uu____2685 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2684) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2732 = f a2 in
                                               [uu____2732]
                                           | x::xs ->
                                               let uu____2737 =
                                                 apply_last1 f xs in
                                               x :: uu____2737 in
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
                                           let uu____2757 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2757 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____2787 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2787
                                                 then
                                                   let uu____2788 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2788
                                                 else ());
                                                (let uu____2790 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2790))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____2799 =
                                                 let uu____2804 = mk_lid name in
                                                 let uu____2805 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2804 uu____2805 in
                                               (match uu____2799 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2809 =
                                                        let uu____2812 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____2812 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____2809);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2882 =
                                             let uu____2885 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2886 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____2885 :: uu____2886 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____2882);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2955 =
                                              let uu____2958 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____2959 =
                                                FStar_ST.op_Bang sigelts in
                                              uu____2958 :: uu____2959 in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____2955);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____3028 =
                                               let uu____3031 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3032 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3031 :: uu____3032 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3028);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____3101 =
                                                let uu____3104 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____3105 =
                                                  FStar_ST.op_Bang sigelts in
                                                uu____3104 :: uu____3105 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____3101);
                                             (let uu____3172 =
                                                FStar_List.fold_left
                                                  (fun uu____3212  ->
                                                     fun action  ->
                                                       match uu____3212 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3233 =
                                                             let uu____3240 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3240
                                                               params_un in
                                                           (match uu____3233
                                                            with
                                                            | (action_params,env',uu____3249)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3269
                                                                     ->
                                                                    match uu____3269
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3280
                                                                    =
                                                                    let uu___106_3281
                                                                    = bv in
                                                                    let uu____3282
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___106_3281.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___106_3281.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3282
                                                                    } in
                                                                    (uu____3280,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3286
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3286
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
                                                                    uu____3316
                                                                    ->
                                                                    let uu____3317
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3317 in
                                                                    ((
                                                                    let uu____3321
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3321
                                                                    then
                                                                    let uu____3322
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3323
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3324
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3325
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3322
                                                                    uu____3323
                                                                    uu____3324
                                                                    uu____3325
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
                                                                    let uu____3329
                                                                    =
                                                                    let uu____3332
                                                                    =
                                                                    let uu___107_3333
                                                                    = action in
                                                                    let uu____3334
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3335
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___107_3333.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___107_3333.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___107_3333.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3334;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3335
                                                                    } in
                                                                    uu____3332
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3329))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3172 with
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
                                                      let uu____3368 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3369 =
                                                        let uu____3372 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3372] in
                                                      uu____3368 ::
                                                        uu____3369 in
                                                    let uu____3373 =
                                                      let uu____3374 =
                                                        let uu____3375 =
                                                          let uu____3376 =
                                                            let uu____3391 =
                                                              let uu____3398
                                                                =
                                                                let uu____3403
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3404
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3403,
                                                                  uu____3404) in
                                                              [uu____3398] in
                                                            (repr,
                                                              uu____3391) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3376 in
                                                        mk1 uu____3375 in
                                                      let uu____3419 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3374
                                                        uu____3419 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3373
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3422 =
                                                    let uu____3429 =
                                                      let uu____3430 =
                                                        let uu____3433 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3433 in
                                                      uu____3430.FStar_Syntax_Syntax.n in
                                                    match uu____3429 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3443)
                                                        ->
                                                        let uu____3472 =
                                                          let uu____3489 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3489
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3547 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3472
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3597 =
                                                               let uu____3598
                                                                 =
                                                                 let uu____3601
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3601 in
                                                               uu____3598.FStar_Syntax_Syntax.n in
                                                             (match uu____3597
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3626
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3626
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3639
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3664
                                                                     ->
                                                                    match uu____3664
                                                                    with
                                                                    | 
                                                                    (bv,uu____3670)
                                                                    ->
                                                                    let uu____3671
                                                                    =
                                                                    let uu____3672
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3672
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3671
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3639
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
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3736
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3736 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg)
                                                                    | 
                                                                    uu____3741
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3749
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3749 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg) in
                                                                    let uu____3754
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____3757
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____3754,
                                                                    uu____3757)))
                                                              | uu____3764 ->
                                                                  let uu____3765
                                                                    =
                                                                    let uu____3766
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3766 in
                                                                  raise_error
                                                                    uu____3765))
                                                    | uu____3773 ->
                                                        let uu____3774 =
                                                          let uu____3775 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____3775 in
                                                        raise_error
                                                          uu____3774 in
                                                  (match uu____3422 with
                                                   | (pre,post) ->
                                                       ((let uu____3799 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____3801 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____3803 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___108_3805
                                                             = ed in
                                                           let uu____3806 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____3807 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____3808 =
                                                             let uu____3809 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____3809) in
                                                           let uu____3816 =
                                                             let uu____3817 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____3817) in
                                                           let uu____3824 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____3825 =
                                                             let uu____3826 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____3826) in
                                                           let uu____3833 =
                                                             let uu____3834 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____3834) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3806;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3807;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3808;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3816;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___108_3805.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3824;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3825;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3833;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____3841 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____3841
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3859
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____3859
                                                               then
                                                                 let uu____3860
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____3860
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
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3875
                                                                    =
                                                                    let uu____3884
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____3884) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3875 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3872;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____3899
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____3899
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____3901
                                                                 =
                                                                 let uu____3904
                                                                   =
                                                                   let uu____3907
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____3907 in
                                                                 FStar_List.append
                                                                   uu____3904
                                                                   sigelts' in
                                                               (uu____3901,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____3956 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____3956 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____3989 = FStar_List.hd ses in
            uu____3989.FStar_Syntax_Syntax.sigrng in
          (match lids with
           | lex_t1::lex_top1::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top1
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu____3994 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Invalid (partial) redefinition of lex_t", err_range)));
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____3999,uu____4000);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4002;
               FStar_Syntax_Syntax.sigattrs = uu____4003;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_41,uu____4007);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4009;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4010;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_42,uu____4014);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4016;
                 FStar_Syntax_Syntax.sigattrs = uu____4017;_}::[]
               when
               ((_0_41 = (Prims.parse_int "0")) &&
                  (_0_42 = (Prims.parse_int "0")))
                 &&
                 (((FStar_Ident.lid_equals lex_t1
                      FStar_Parser_Const.lex_t_lid)
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
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
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
                 let uu____4082 =
                   let uu____4085 =
                     let uu____4086 =
                       let uu____4093 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4093, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4086 in
                   FStar_Syntax_Syntax.mk uu____4085 in
                 uu____4082 FStar_Pervasives_Native.None r1 in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
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
                   let uu____4111 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4111 in
                 let hd1 =
                   let uu____4113 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4113 in
                 let tl1 =
                   let uu____4115 =
                     let uu____4116 =
                       let uu____4119 =
                         let uu____4120 =
                           let uu____4127 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4127, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4120 in
                       FStar_Syntax_Syntax.mk uu____4119 in
                     uu____4116 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4115 in
                 let res =
                   let uu____4136 =
                     let uu____4139 =
                       let uu____4140 =
                         let uu____4147 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4147,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____4140 in
                     FStar_Syntax_Syntax.mk uu____4139 in
                   uu____4136 FStar_Pervasives_Native.None r2 in
                 let uu____4153 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4153 in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let uu____4192 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4192;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4197 ->
               let err_msg =
                 let uu____4201 =
                   let uu____4202 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____4202 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4201 in
               FStar_Exn.raise (FStar_Errors.Error (err_msg, err_range)))
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
            let uu____4232 = FStar_Syntax_Util.type_u () in
            match uu____4232 with
            | (k,uu____4238) ->
                let phi1 =
                  let uu____4240 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4240
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4242 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4242 with
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
          let uu____4288 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4288 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4321 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4321 FStar_List.flatten in
              ((let uu____4335 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4335
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
                          let uu____4346 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4356,uu____4357,uu____4358,uu____4359,uu____4360)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4369 -> failwith "Impossible!" in
                          match uu____4346 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4380 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4384,uu____4385,uu____4386,uu____4387,uu____4388)
                        -> lid
                    | uu____4397 -> failwith "Impossible" in
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
                  let uu____4415 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4415
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
                     let uu____4438 =
                       let uu____4441 =
                         let uu____4442 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4442;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4441 :: ses1 in
                     (uu____4438, data_ops_ses)) in
                (let uu____4452 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4488 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4513 ->
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
           let uu____4565 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4565 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4604 = FStar_Options.set_options t s in
             match uu____4604 with
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
                ((let uu____4630 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4630 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4638 = cps_and_elaborate env1 ne in
           (match uu____4638 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___109_4675 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___109_4675.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___109_4675.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___109_4675.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___109_4675.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___110_4677 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___110_4677.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___110_4677.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___110_4677.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___110_4677.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___111_4685 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___111_4685.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___111_4685.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___111_4685.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___111_4685.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4693 =
             let uu____4700 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4700 in
           (match uu____4693 with
            | (a,wp_a_src) ->
                let uu____4715 =
                  let uu____4722 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4722 in
                (match uu____4715 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4738 =
                         let uu____4741 =
                           let uu____4742 =
                             let uu____4749 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4749) in
                           FStar_Syntax_Syntax.NT uu____4742 in
                         [uu____4741] in
                       FStar_Syntax_Subst.subst uu____4738 wp_b_tgt in
                     let expected_k =
                       let uu____4753 =
                         let uu____4760 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4761 =
                           let uu____4764 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4764] in
                         uu____4760 :: uu____4761 in
                       let uu____4765 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4753 uu____4765 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4786 =
                           let uu____4787 =
                             let uu____4792 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____4793 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____4792, uu____4793) in
                           FStar_Errors.Error uu____4787 in
                         FStar_Exn.raise uu____4786 in
                       let uu____4796 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____4796 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____4828 =
                             let uu____4829 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____4829 in
                           if uu____4828
                           then no_reify eff_name
                           else
                             (let uu____4835 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____4836 =
                                let uu____4839 =
                                  let uu____4840 =
                                    let uu____4855 =
                                      let uu____4858 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____4859 =
                                        let uu____4862 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____4862] in
                                      uu____4858 :: uu____4859 in
                                    (repr, uu____4855) in
                                  FStar_Syntax_Syntax.Tm_app uu____4840 in
                                FStar_Syntax_Syntax.mk uu____4839 in
                              uu____4836 FStar_Pervasives_Native.None
                                uu____4835) in
                     let uu____4868 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____4896,lift_wp)) ->
                           let uu____4920 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____4920)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____4946 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____4946
                             then
                               let uu____4947 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____4947
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____4950 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____4950 with
                             | (lift1,comp,uu____4965) ->
                                 let uu____4966 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____4966 with
                                  | (uu____4979,lift_wp,lift_elab) ->
                                      let uu____4982 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____4983 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____4868 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___112_5024 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___112_5024.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___112_5024.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___112_5024.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___112_5024.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___112_5024.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___112_5024.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___112_5024.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___112_5024.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___112_5024.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___112_5024.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___112_5024.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___112_5024.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___112_5024.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___112_5024.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___112_5024.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___112_5024.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___112_5024.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___112_5024.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___112_5024.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___112_5024.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.type_of =
                                (uu___112_5024.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___112_5024.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___112_5024.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___112_5024.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___112_5024.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___112_5024.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___112_5024.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___112_5024.FStar_TypeChecker_Env.identifier_info)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5030,lift1)
                                ->
                                let uu____5042 =
                                  let uu____5049 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5049 in
                                (match uu____5042 with
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
                                         let uu____5073 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5074 =
                                           let uu____5077 =
                                             let uu____5078 =
                                               let uu____5093 =
                                                 let uu____5096 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5097 =
                                                   let uu____5100 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5100] in
                                                 uu____5096 :: uu____5097 in
                                               (lift_wp1, uu____5093) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5078 in
                                           FStar_Syntax_Syntax.mk uu____5077 in
                                         uu____5074
                                           FStar_Pervasives_Native.None
                                           uu____5073 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5109 =
                                         let uu____5116 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5117 =
                                           let uu____5120 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5121 =
                                             let uu____5124 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5124] in
                                           uu____5120 :: uu____5121 in
                                         uu____5116 :: uu____5117 in
                                       let uu____5125 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5109
                                         uu____5125 in
                                     let uu____5128 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5128 with
                                      | (expected_k2,uu____5138,uu____5139)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___113_5142 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___113_5142.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___113_5142.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___114_5144 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___114_5144.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___114_5144.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___114_5144.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___114_5144.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5163 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5163 with
            | (tps1,c1) ->
                let uu____5178 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5178 with
                 | (tps2,env3,us) ->
                     let uu____5196 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5196 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5217 =
                              let uu____5218 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5218 in
                            match uu____5217 with
                            | (uvs1,t) ->
                                let uu____5233 =
                                  let uu____5246 =
                                    let uu____5251 =
                                      let uu____5252 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5252.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5251) in
                                  match uu____5246 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5267,c4)) -> ([], c4)
                                  | (uu____5307,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5334 ->
                                      failwith "Impossible (t is an arrow)" in
                                (match uu____5233 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5378 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5378 with
                                         | (uu____5383,t1) ->
                                             let uu____5385 =
                                               let uu____5386 =
                                                 let uu____5391 =
                                                   let uu____5392 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5393 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5394 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5392 uu____5393
                                                     uu____5394 in
                                                 (uu____5391, r) in
                                               FStar_Errors.Error uu____5386 in
                                             FStar_Exn.raise uu____5385)
                                      else ();
                                      (let se1 =
                                         let uu___115_5397 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___115_5397.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___115_5397.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___115_5397.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___115_5397.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5414,uu____5415,uu____5416) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___89_5420  ->
                   match uu___89_5420 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5421 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5426,uu____5427) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___89_5435  ->
                   match uu___89_5435 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5436 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5446 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5446
             then
               let uu____5447 =
                 let uu____5448 =
                   let uu____5453 =
                     FStar_Util.format1
                       "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                       (FStar_Ident.text_of_lid lid) in
                   (uu____5453, r) in
                 FStar_Errors.Error uu____5448 in
               FStar_Exn.raise uu____5447
             else ());
            (let uu____5455 =
               if uvs = []
               then
                 let uu____5456 =
                   let uu____5457 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5457 in
                 check_and_gen env2 t uu____5456
               else
                 (let uu____5463 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5463 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5471 =
                          let uu____5472 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5472 in
                        tc_check_trivial_guard env2 t1 uu____5471 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5478 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5478)) in
             match uu____5455 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___116_5494 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___116_5494.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___116_5494.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___116_5494.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___116_5494.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5504 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5504 with
            | (uu____5517,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5527 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5527 with
            | (e1,c,g1) ->
                let uu____5545 =
                  let uu____5552 =
                    let uu____5555 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5555 in
                  let uu____5556 =
                    let uu____5561 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5561) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5552 uu____5556 in
                (match uu____5545 with
                 | (e2,uu____5575,g) ->
                     ((let uu____5578 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5578);
                      (let se1 =
                         let uu___117_5580 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_5580.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_5580.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_5580.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___117_5580.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5631 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5631
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5639 =
                      let uu____5640 =
                        let uu____5645 =
                          let uu____5646 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5647 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5648 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5646 uu____5647 uu____5648 in
                        (uu____5645, r) in
                      FStar_Errors.Error uu____5640 in
                    FStar_Exn.raise uu____5639) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____5674 =
                   let uu____5675 = FStar_Syntax_Subst.compress def in
                   uu____5675.FStar_Syntax_Syntax.n in
                 match uu____5674 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5685,uu____5686)
                     -> binders
                 | uu____5707 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5717;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5795) -> val_bs1
                     | (uu____5818,[]) -> val_bs1
                     | ((body_bv,uu____5842)::bt,(val_bv,aqual)::vt) ->
                         let uu____5879 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____5895) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___118_5897 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___119_5900 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___119_5900.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___118_5897.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___118_5897.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____5879 in
                   let uu____5901 =
                     let uu____5904 =
                       let uu____5905 =
                         let uu____5918 = rename_binders1 def_bs val_bs in
                         (uu____5918, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____5905 in
                     FStar_Syntax_Syntax.mk uu____5904 in
                   uu____5901 FStar_Pervasives_Native.None r1
               | uu____5936 -> typ1 in
             let uu___120_5937 = lb in
             let uu____5938 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___120_5937.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___120_5937.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____5938;
               FStar_Syntax_Syntax.lbeff =
                 (uu___120_5937.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___120_5937.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____5941 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____5992  ->
                     fun lb  ->
                       match uu____5992 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6034 =
                             let uu____6045 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6045 with
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
                                   | uu____6130 ->
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
                                  (let uu____6173 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6173, quals_opt1))) in
                           (match uu____6034 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____5941 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6267 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___90_6271  ->
                                match uu___90_6271 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6272 -> false)) in
                      if uu____6267
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6282 =
                    let uu____6285 =
                      let uu____6286 =
                        let uu____6299 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6299) in
                      FStar_Syntax_Syntax.Tm_let uu____6286 in
                    FStar_Syntax_Syntax.mk uu____6285 in
                  uu____6282 FStar_Pervasives_Native.None r in
                let uu____6317 =
                  let uu____6328 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___121_6337 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___121_6337.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___121_6337.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___121_6337.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___121_6337.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___121_6337.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___121_6337.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___121_6337.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___121_6337.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___121_6337.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___121_6337.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___121_6337.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___121_6337.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___121_6337.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___121_6337.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___121_6337.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___121_6337.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___121_6337.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___121_6337.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___121_6337.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.type_of =
                           (uu___121_6337.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___121_6337.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___121_6337.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___121_6337.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___121_6337.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___121_6337.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___121_6337.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___121_6337.FStar_TypeChecker_Env.identifier_info)
                       }) e in
                  match uu____6328 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6350;
                       FStar_Syntax_Syntax.vars = uu____6351;_},uu____6352,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6381 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6381) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6399,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6404 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___91_6410  ->
                             match uu___91_6410 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____6413 =
                                   let uu____6414 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____6421 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____6421)
                                          else ();
                                          ok)
                                       (FStar_Pervasives_Native.snd lbs2) in
                                   Prims.op_Negation uu____6414 in
                                 if uu____6413
                                 then FStar_Pervasives_Native.None
                                 else
                                   FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> FStar_Pervasives_Native.Some q) quals1 in
                      ((let uu___122_6436 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___122_6436.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___122_6436.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___122_6436.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6445 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)" in
                (match uu____6317 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6494 = log env2 in
                       if uu____6494
                       then
                         let uu____6495 =
                           let uu____6496 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6511 =
                                         let uu____6520 =
                                           let uu____6521 =
                                             let uu____6524 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6524.FStar_Syntax_Syntax.fv_name in
                                           uu____6521.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6520 in
                                       match uu____6511 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6531 -> false in
                                     if should_log
                                     then
                                       let uu____6540 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6541 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6540 uu____6541
                                     else "")) in
                           FStar_All.pipe_right uu____6496
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6495
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6572 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6572 with
                              | (bs1,c1) ->
                                  let uu____6579 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6579
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6591 =
                                            let uu____6592 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6592.FStar_Syntax_Syntax.n in
                                          (match uu____6591 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6617 =
                                                 let uu____6618 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6618.FStar_Syntax_Syntax.n in
                                               (match uu____6617 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6628 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6628 in
                                                    let uu____6629 =
                                                      let uu____6630 =
                                                        let uu____6631 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6631 args in
                                                      uu____6630
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6629 u
                                                | uu____6634 -> c1)
                                           | uu____6635 -> c1)
                                      | uu____6636 -> c1 in
                                    let uu___123_6637 = t1 in
                                    let uu____6638 =
                                      let uu____6639 =
                                        let uu____6652 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6652) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6639 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6638;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___123_6637.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___123_6637.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6676 =
                               let uu____6677 = FStar_Syntax_Subst.compress h in
                               uu____6677.FStar_Syntax_Syntax.n in
                             (match uu____6676 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6687 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6687 in
                                  let uu____6688 =
                                    let uu____6689 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6689
                                      args in
                                  uu____6688 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6692 -> t1)
                         | uu____6693 -> t1 in
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
                           let uu____6721 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6721 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6738 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____6738, (FStar_Pervasives_Native.snd x)))
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
                           let uu____6769 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6769 in
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
                         let uu___124_6776 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___125_6788 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_6788.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_6788.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_6788.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_6788.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___124_6776.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___124_6776.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___124_6776.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___124_6776.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6805 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____6805 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____6839 =
                                    let uu____6840 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6840.FStar_Syntax_Syntax.n in
                                  (match uu____6839 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____6873 =
                                           let uu____6876 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____6876.FStar_Syntax_Syntax.fv_name in
                                         uu____6873.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____6878 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____6878 in
                                       let uu____6879 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____6881 =
                                              let uu____6882 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____6882 in
                                            Prims.op_Negation uu____6881) in
                                       if uu____6879
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
                                   | uu____6924 ->
                                       FStar_Pervasives_Native.None))
                         | uu____6929 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____6951 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____6951
                             then
                               let uu____6952 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____6953 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____6952 uu____6953
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
             (fun uu___92_7006  ->
                match uu___92_7006 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7007 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7013) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7019 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7028 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7033 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7058 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7082) ->
          let uu____7091 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7091
          then
            let for_export_bundle se1 uu____7122 =
              match uu____7122 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7161,uu____7162) ->
                       let dec =
                         let uu___126_7172 = se1 in
                         let uu____7173 =
                           let uu____7174 =
                             let uu____7181 =
                               let uu____7184 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7184 in
                             (l, us, uu____7181) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7174 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7173;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___126_7172.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___126_7172.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___126_7172.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7196,uu____7197,uu____7198) ->
                       let dec =
                         let uu___127_7204 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___127_7204.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___127_7204.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___127_7204.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7209 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7231,uu____7232,uu____7233) ->
          let uu____7234 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7234 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7255 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7255
          then
            ([(let uu___128_7271 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___128_7271.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___128_7271.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___128_7271.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7273 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___93_7277  ->
                       match uu___93_7277 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7278 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7283 -> true
                       | uu____7284 -> false)) in
             if uu____7273 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7302 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7307 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7312 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7317 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7322 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7340) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7357 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7357
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
          let uu____7388 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7388
          then
            let uu____7397 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___129_7410 = se in
                      let uu____7411 =
                        let uu____7412 =
                          let uu____7419 =
                            let uu____7420 =
                              let uu____7423 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7423.FStar_Syntax_Syntax.fv_name in
                            uu____7420.FStar_Syntax_Syntax.v in
                          (uu____7419, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7412 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7411;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___129_7410.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___129_7410.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___129_7410.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7397, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7445 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7462 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.SetOptions uu____7478 ->
               let uu____7479 = FStar_Options.using_facts_from () in
               (match uu____7479 with
                | FStar_Pervasives_Native.Some ns ->
                    let proof_ns =
                      let uu____7500 =
                        let uu____7509 =
                          FStar_List.map
                            (fun s  -> ((FStar_Ident.path_of_text s), true))
                            ns in
                        FStar_List.append uu____7509 [([], false)] in
                      [uu____7500] in
                    let uu___130_7564 = env in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___130_7564.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___130_7564.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___130_7564.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___130_7564.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___130_7564.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___130_7564.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___130_7564.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___130_7564.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___130_7564.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___130_7564.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___130_7564.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___130_7564.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___130_7564.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___130_7564.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___130_7564.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___130_7564.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___130_7564.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___130_7564.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___130_7564.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___130_7564.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___130_7564.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.type_of =
                        (uu___130_7564.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___130_7564.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___130_7564.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___130_7564.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns = proof_ns;
                      FStar_TypeChecker_Env.synth =
                        (uu___130_7564.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___130_7564.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___130_7564.FStar_TypeChecker_Env.identifier_info)
                    }
                | FStar_Pervasives_Native.None  ->
                    let uu___131_7567 = env in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___131_7567.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___131_7567.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___131_7567.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___131_7567.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___131_7567.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___131_7567.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___131_7567.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___131_7567.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___131_7567.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___131_7567.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___131_7567.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___131_7567.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___131_7567.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___131_7567.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___131_7567.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___131_7567.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___131_7567.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___131_7567.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___131_7567.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___131_7567.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___131_7567.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.type_of =
                        (uu___131_7567.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___131_7567.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___131_7567.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___131_7567.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns = [[]];
                      FStar_TypeChecker_Env.synth =
                        (uu___131_7567.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___131_7567.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___131_7567.FStar_TypeChecker_Env.identifier_info)
                    })
           | FStar_Syntax_Syntax.ResetOptions uu____7584 ->
               let uu____7587 = FStar_Options.using_facts_from () in
               (match uu____7587 with
                | FStar_Pervasives_Native.Some ns ->
                    let proof_ns =
                      let uu____7608 =
                        let uu____7617 =
                          FStar_List.map
                            (fun s  -> ((FStar_Ident.path_of_text s), true))
                            ns in
                        FStar_List.append uu____7617 [([], false)] in
                      [uu____7608] in
                    let uu___130_7672 = env in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___130_7672.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___130_7672.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___130_7672.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___130_7672.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___130_7672.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___130_7672.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___130_7672.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___130_7672.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___130_7672.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___130_7672.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___130_7672.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___130_7672.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___130_7672.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___130_7672.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___130_7672.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___130_7672.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___130_7672.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___130_7672.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___130_7672.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___130_7672.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___130_7672.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.type_of =
                        (uu___130_7672.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___130_7672.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___130_7672.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___130_7672.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns = proof_ns;
                      FStar_TypeChecker_Env.synth =
                        (uu___130_7672.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___130_7672.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___130_7672.FStar_TypeChecker_Env.identifier_info)
                    }
                | FStar_Pervasives_Native.None  ->
                    let uu___131_7675 = env in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___131_7675.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___131_7675.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___131_7675.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___131_7675.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___131_7675.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___131_7675.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___131_7675.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___131_7675.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___131_7675.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___131_7675.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___131_7675.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___131_7675.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___131_7675.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___131_7675.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___131_7675.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___131_7675.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___131_7675.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___131_7675.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___131_7675.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___131_7675.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___131_7675.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.type_of =
                        (uu___131_7675.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___131_7675.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___131_7675.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___131_7675.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns = [[]];
                      FStar_TypeChecker_Env.synth =
                        (uu___131_7675.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___131_7675.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___131_7675.FStar_TypeChecker_Env.identifier_info)
                    })
           | uu____7692 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7693 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7703 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7703) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7704,uu____7705,uu____7706) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_7710  ->
                  match uu___94_7710 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7711 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7712,uu____7713) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_7721  ->
                  match uu___94_7721 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7722 -> false))
          -> env
      | uu____7723 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7785 se =
        match uu____7785 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7838 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7838
              then
                let uu____7839 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7839
              else ());
             (let uu____7841 = tc_decl env1 se in
              match uu____7841 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7891 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7891
                             then
                               let uu____7892 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7892
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
                    (let uu____7915 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____7915
                     then
                       let uu____7916 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7922 =
                                  let uu____7923 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____7923 "\n" in
                                Prims.strcat s uu____7922) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____7916
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7928 =
                       let accum_exports_hidden uu____7958 se1 =
                         match uu____7958 with
                         | (exports1,hidden1) ->
                             let uu____7986 = for_export hidden1 se1 in
                             (match uu____7986 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____7928 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___132_8065 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___132_8065.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___132_8065.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___132_8065.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___132_8065.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8143 = acc in
        match uu____8143 with
        | (uu____8178,uu____8179,env1,uu____8181) ->
            let uu____8194 =
              FStar_Util.record_time
                (fun uu____8240  -> process_one_decl acc se) in
            (match uu____8194 with
             | (r,ms_elapsed) ->
                 ((let uu____8304 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8304
                   then
                     let uu____8305 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8306 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8305 uu____8306
                   else ());
                  r)) in
      let uu____8308 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8308 with
      | (ses1,exports,env1,uu____8356) ->
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
      (let uu____8395 = FStar_Options.debug_any () in
       if uu____8395
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
         let uu___133_8401 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___133_8401.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___133_8401.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___133_8401.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___133_8401.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___133_8401.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___133_8401.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___133_8401.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___133_8401.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___133_8401.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___133_8401.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___133_8401.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___133_8401.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___133_8401.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___133_8401.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___133_8401.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___133_8401.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___133_8401.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___133_8401.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___133_8401.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.type_of =
             (uu___133_8401.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___133_8401.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___133_8401.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___133_8401.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___133_8401.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___133_8401.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___133_8401.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___133_8401.FStar_TypeChecker_Env.identifier_info)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____8404 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____8404 with
        | (ses,exports,env3) ->
            ((let uu___134_8437 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___134_8437.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___134_8437.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___134_8437.FStar_Syntax_Syntax.is_interface)
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
        let uu____8462 = tc_decls env decls in
        match uu____8462 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___135_8493 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___135_8493.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___135_8493.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___135_8493.FStar_Syntax_Syntax.is_interface)
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
          let uu___136_8513 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___136_8513.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___136_8513.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___136_8513.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___136_8513.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___136_8513.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___136_8513.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___136_8513.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___136_8513.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___136_8513.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___136_8513.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___136_8513.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___136_8513.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___136_8513.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___136_8513.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___136_8513.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___136_8513.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___136_8513.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___136_8513.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.type_of =
              (uu___136_8513.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___136_8513.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___136_8513.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___136_8513.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___136_8513.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___136_8513.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___136_8513.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___136_8513.FStar_TypeChecker_Env.identifier_info)
          } in
        let check_term lid univs1 t =
          let uu____8524 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8524 with
          | (univs2,t1) ->
              ((let uu____8532 =
                  let uu____8533 =
                    let uu____8536 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8536 in
                  FStar_All.pipe_left uu____8533
                    (FStar_Options.Other "Exports") in
                if uu____8532
                then
                  let uu____8537 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8538 =
                    let uu____8539 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8539
                      (FStar_String.concat ", ") in
                  let uu____8548 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8537 uu____8538 uu____8548
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8551 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8551 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____8575 =
             let uu____8576 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8577 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8576 uu____8577 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8575);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8584) ->
              let uu____8593 =
                let uu____8594 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8594 in
              if uu____8593
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8604,uu____8605) ->
              let t =
                let uu____8617 =
                  let uu____8620 =
                    let uu____8621 =
                      let uu____8634 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8634) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8621 in
                  FStar_Syntax_Syntax.mk uu____8620 in
                uu____8617 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8641,uu____8642,uu____8643) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8651 =
                let uu____8652 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8652 in
              if uu____8651 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8656,lbs),uu____8658) ->
              let uu____8673 =
                let uu____8674 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8674 in
              if uu____8673
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
              let uu____8693 =
                let uu____8694 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8694 in
              if uu____8693
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8701 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8702 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8709 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8710 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8711 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8712 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let load_checked_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun modul  ->
      let env1 =
        FStar_TypeChecker_Env.set_current_module env
          modul.FStar_Syntax_Syntax.name in
      let env2 =
        FStar_List.fold_left FStar_TypeChecker_Env.push_sigelt env1
          modul.FStar_Syntax_Syntax.exports in
      let env3 = FStar_TypeChecker_Env.finish_module env2 modul in
      (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
        env3 modul;
      (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
      (let uu____8728 =
         let uu____8729 = FStar_Options.interactive () in
         Prims.op_Negation uu____8729 in
       if uu____8728
       then
         let uu____8730 = FStar_Options.restore_cmd_line_options true in
         FStar_All.pipe_right uu____8730 FStar_Pervasives.ignore
       else ());
      env3
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
          let uu___137_8749 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___137_8749.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___137_8749.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____8752 =
           let uu____8753 = FStar_Options.lax () in
           Prims.op_Negation uu____8753 in
         if uu____8752 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____8759 =
           let uu____8760 = FStar_Options.interactive () in
           Prims.op_Negation uu____8760 in
         if uu____8759
         then
           let uu____8761 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____8761 FStar_Pervasives.ignore
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
      let uu____8775 = tc_partial_modul env modul in
      match uu____8775 with
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
      (let uu____8808 = FStar_Options.debug_any () in
       if uu____8808
       then
         let uu____8809 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8809
       else ());
      (let env1 =
         let uu___138_8813 = env in
         let uu____8814 =
           let uu____8815 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8815 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___138_8813.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___138_8813.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___138_8813.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___138_8813.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___138_8813.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___138_8813.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___138_8813.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___138_8813.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___138_8813.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___138_8813.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___138_8813.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___138_8813.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___138_8813.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___138_8813.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___138_8813.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___138_8813.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___138_8813.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___138_8813.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8814;
           FStar_TypeChecker_Env.lax_universes =
             (uu___138_8813.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___138_8813.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.type_of =
             (uu___138_8813.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___138_8813.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___138_8813.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___138_8813.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___138_8813.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___138_8813.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___138_8813.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___138_8813.FStar_TypeChecker_Env.identifier_info)
         } in
       let uu____8816 = tc_modul env1 m in
       match uu____8816 with
       | (m1,env2) ->
           ((let uu____8828 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8828
             then
               let uu____8829 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8829
             else ());
            (let uu____8832 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8832
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
                       let uu____8863 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8863 with
                       | (univnames1,e) ->
                           let uu___139_8870 = lb in
                           let uu____8871 =
                             let uu____8874 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____8874 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___139_8870.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___139_8870.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___139_8870.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___139_8870.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____8871
                           } in
                     let uu___140_8875 = se in
                     let uu____8876 =
                       let uu____8877 =
                         let uu____8884 =
                           let uu____8891 = FStar_List.map update lbs in
                           (b, uu____8891) in
                         (uu____8884, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____8877 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____8876;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___140_8875.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___140_8875.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___140_8875.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___140_8875.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____8904 -> se in
               let normalized_module =
                 let uu___141_8906 = m1 in
                 let uu____8907 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___141_8906.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____8907;
                   FStar_Syntax_Syntax.exports =
                     (uu___141_8906.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___141_8906.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____8908 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____8908
             else ());
            (m1, env2)))