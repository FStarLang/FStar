open Prims
let set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____9 = FStar_Options.reuse_hint_for ()  in
      match uu____9 with
      | Some l ->
          let lid =
            let uu____13 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____13 l  in
          let uu___91_14 = env  in
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
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___91_14.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___91_14.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___91_14.FStar_TypeChecker_Env.is_native_tactic)
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____20 = FStar_TypeChecker_Env.current_module env  in
                let uu____21 =
                  let uu____22 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____22 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____20 uu____21
            | l::uu____24 -> l  in
          let uu___92_26 = env  in
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
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___92_26.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___92_26.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___92_26.FStar_TypeChecker_Env.is_native_tactic)
          }
  
let log : FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____33 =
         let uu____34 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____34  in
       Prims.op_Negation uu____33)
  
let is_native_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____48) ->
            let uu____53 =
              let uu____54 = FStar_Syntax_Subst.compress h'  in
              uu____54.FStar_Syntax_Syntax.n  in
            (match uu____53 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.tactic_lid
                 -> env.FStar_TypeChecker_Env.is_native_tactic tac_lid
             | uu____58 -> false)
        | uu____59 -> false
  
let tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____72 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____72 with
        | (t1,c,g) ->
            (FStar_ST.write t1.FStar_Syntax_Syntax.tk
               (Some ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t1)
  
let recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____97 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____97
         then
           let uu____98 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____98
         else ());
        (let uu____100 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____100 with
         | (t',uu____105,uu____106) ->
             ((let uu____108 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____108
               then
                 let uu____109 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____109
               else ());
              t))
  
let check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____123 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____123
  
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k  in
  let uu____149 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1
     in
  ([], uu____149) 
let monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv *
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
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s
                 in
              (uu____179, (FStar_Ident.range_of_lid m))  in
            FStar_Errors.Error uu____176  in
          raise uu____175  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____207)::(wp,uu____209)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____218 -> fail ())
        | uu____219 -> fail ()
  
let rec tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____281 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____281 with
      | (effect_params_un,signature_un,opening) ->
          let uu____288 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un  in
          (match uu____288 with
           | (effect_params,env,uu____294) ->
               let uu____295 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un
                  in
               (match uu____295 with
                | (signature,uu____299) ->
                    let ed1 =
                      let uu___93_301 = ed  in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___93_301.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___93_301.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___93_301.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___93_301.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___93_301.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___93_301.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___93_301.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___93_301.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___93_301.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___93_301.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___93_301.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___93_301.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___93_301.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___93_301.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___93_301.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___93_301.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___93_301.FStar_Syntax_Syntax.actions)
                      }  in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____305 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts)  in
                            ([], t1)  in
                          let uu___94_323 = ed1  in
                          let uu____324 = op ed1.FStar_Syntax_Syntax.ret_wp
                             in
                          let uu____325 = op ed1.FStar_Syntax_Syntax.bind_wp
                             in
                          let uu____326 =
                            op ed1.FStar_Syntax_Syntax.if_then_else  in
                          let uu____327 = op ed1.FStar_Syntax_Syntax.ite_wp
                             in
                          let uu____328 = op ed1.FStar_Syntax_Syntax.stronger
                             in
                          let uu____329 = op ed1.FStar_Syntax_Syntax.close_wp
                             in
                          let uu____330 = op ed1.FStar_Syntax_Syntax.assert_p
                             in
                          let uu____331 = op ed1.FStar_Syntax_Syntax.assume_p
                             in
                          let uu____332 = op ed1.FStar_Syntax_Syntax.null_wp
                             in
                          let uu____333 = op ed1.FStar_Syntax_Syntax.trivial
                             in
                          let uu____334 =
                            let uu____335 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr))  in
                            snd uu____335  in
                          let uu____341 =
                            op ed1.FStar_Syntax_Syntax.return_repr  in
                          let uu____342 =
                            op ed1.FStar_Syntax_Syntax.bind_repr  in
                          let uu____343 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___95_346 = a  in
                                 let uu____347 =
                                   let uu____348 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn))
                                      in
                                   snd uu____348  in
                                 let uu____354 =
                                   let uu____355 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ))
                                      in
                                   snd uu____355  in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___95_346.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___95_346.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___95_346.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___95_346.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____347;
                                   FStar_Syntax_Syntax.action_typ = uu____354
                                 }) ed1.FStar_Syntax_Syntax.actions
                             in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___94_323.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___94_323.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___94_323.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___94_323.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___94_323.FStar_Syntax_Syntax.signature);
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
                          }
                       in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____383 =
                          let uu____384 =
                            let uu____387 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t
                               in
                            (uu____387, (FStar_Ident.range_of_lid mname))  in
                          FStar_Errors.Error uu____384  in
                        raise uu____383  in
                      let uu____392 =
                        let uu____393 =
                          FStar_Syntax_Subst.compress signature1  in
                        uu____393.FStar_Syntax_Syntax.n  in
                      match uu____392 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs  in
                          (match bs1 with
                           | (a,uu____418)::(wp,uu____420)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____429 -> fail signature1)
                      | uu____430 -> fail signature1  in
                    let uu____431 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature
                       in
                    (match uu____431 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____449 =
                           let uu____450 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un
                              in
                           match uu____450 with
                           | (signature1,uu____458) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1
                            in
                         let env1 =
                           let uu____460 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature
                              in
                           FStar_TypeChecker_Env.push_bv env uu____460  in
                         ((let uu____462 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED")
                              in
                           if uu____462
                           then
                             let uu____463 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname
                                in
                             let uu____464 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders
                                in
                             let uu____465 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature
                                in
                             let uu____466 =
                               let uu____467 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               FStar_Syntax_Print.term_to_string uu____467
                                in
                             let uu____468 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort
                                in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____463 uu____464 uu____465 uu____466
                               uu____468
                           else ());
                          (let check_and_gen' env2 uu____481 k =
                             match uu____481 with
                             | (uu____486,t) -> check_and_gen env2 t k  in
                           let return_wp =
                             let expected_k =
                               let uu____494 =
                                 let uu____498 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____499 =
                                   let uu____501 =
                                     let uu____502 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____502
                                      in
                                   [uu____501]  in
                                 uu____498 :: uu____499  in
                               let uu____503 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a  in
                               FStar_Syntax_Util.arrow uu____494 uu____503
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k
                              in
                           let bind_wp =
                             let uu____507 = fresh_effect_signature ()  in
                             match uu____507 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____521 =
                                     let uu____525 =
                                       let uu____526 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____526
                                        in
                                     [uu____525]  in
                                   let uu____527 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____521
                                     uu____527
                                    in
                                 let expected_k =
                                   let uu____533 =
                                     let uu____537 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range
                                        in
                                     let uu____538 =
                                       let uu____540 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____541 =
                                         let uu____543 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let uu____544 =
                                           let uu____546 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a
                                              in
                                           let uu____547 =
                                             let uu____549 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b
                                                in
                                             [uu____549]  in
                                           uu____546 :: uu____547  in
                                         uu____543 :: uu____544  in
                                       uu____540 :: uu____541  in
                                     uu____537 :: uu____538  in
                                   let uu____550 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____533
                                     uu____550
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k
                              in
                           let if_then_else1 =
                             let p =
                               let uu____555 =
                                 let uu____556 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____556
                                   FStar_Pervasives.fst
                                  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____555
                                in
                             let expected_k =
                               let uu____564 =
                                 let uu____568 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____569 =
                                   let uu____571 =
                                     FStar_Syntax_Syntax.mk_binder p  in
                                   let uu____572 =
                                     let uu____574 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     let uu____575 =
                                       let uu____577 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____577]  in
                                     uu____574 :: uu____575  in
                                   uu____571 :: uu____572  in
                                 uu____568 :: uu____569  in
                               let uu____578 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____564 uu____578
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k
                              in
                           let ite_wp =
                             let expected_k =
                               let uu____585 =
                                 let uu____589 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____590 =
                                   let uu____592 =
                                     FStar_Syntax_Syntax.null_binder wp_a  in
                                   [uu____592]  in
                                 uu____589 :: uu____590  in
                               let uu____593 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____585 uu____593
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k
                              in
                           let stronger =
                             let uu____597 = FStar_Syntax_Util.type_u ()  in
                             match uu____597 with
                             | (t,uu____601) ->
                                 let expected_k =
                                   let uu____605 =
                                     let uu____609 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____610 =
                                       let uu____612 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       let uu____613 =
                                         let uu____615 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a
                                            in
                                         [uu____615]  in
                                       uu____612 :: uu____613  in
                                     uu____609 :: uu____610  in
                                   let uu____616 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   FStar_Syntax_Util.arrow uu____605
                                     uu____616
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k
                              in
                           let close_wp =
                             let b =
                               let uu____621 =
                                 let uu____622 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____622
                                   FStar_Pervasives.fst
                                  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____621
                                in
                             let b_wp_a =
                               let uu____630 =
                                 let uu____634 =
                                   let uu____635 =
                                     FStar_Syntax_Syntax.bv_to_name b  in
                                   FStar_Syntax_Syntax.null_binder uu____635
                                    in
                                 [uu____634]  in
                               let uu____636 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____630 uu____636
                                in
                             let expected_k =
                               let uu____642 =
                                 let uu____646 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____647 =
                                   let uu____649 =
                                     FStar_Syntax_Syntax.mk_binder b  in
                                   let uu____650 =
                                     let uu____652 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a
                                        in
                                     [uu____652]  in
                                   uu____649 :: uu____650  in
                                 uu____646 :: uu____647  in
                               let uu____653 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____642 uu____653
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k
                              in
                           let assert_p =
                             let expected_k =
                               let uu____660 =
                                 let uu____664 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____665 =
                                   let uu____667 =
                                     let uu____668 =
                                       let uu____669 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____669
                                         FStar_Pervasives.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____668
                                      in
                                   let uu____674 =
                                     let uu____676 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____676]  in
                                   uu____667 :: uu____674  in
                                 uu____664 :: uu____665  in
                               let uu____677 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____660 uu____677
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k
                              in
                           let assume_p =
                             let expected_k =
                               let uu____684 =
                                 let uu____688 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____689 =
                                   let uu____691 =
                                     let uu____692 =
                                       let uu____693 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____693
                                         FStar_Pervasives.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____692
                                      in
                                   let uu____698 =
                                     let uu____700 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____700]  in
                                   uu____691 :: uu____698  in
                                 uu____688 :: uu____689  in
                               let uu____701 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____684 uu____701
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k
                              in
                           let null_wp =
                             let expected_k =
                               let uu____708 =
                                 let uu____712 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 [uu____712]  in
                               let uu____713 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____708 uu____713
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k
                              in
                           let trivial_wp =
                             let uu____717 = FStar_Syntax_Util.type_u ()  in
                             match uu____717 with
                             | (t,uu____721) ->
                                 let expected_k =
                                   let uu____725 =
                                     let uu____729 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____730 =
                                       let uu____732 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____732]  in
                                     uu____729 :: uu____730  in
                                   let uu____733 =
                                     FStar_Syntax_Syntax.mk_GTotal t  in
                                   FStar_Syntax_Util.arrow uu____725
                                     uu____733
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k
                              in
                           let uu____736 =
                             let uu____742 =
                               let uu____743 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr
                                  in
                               uu____743.FStar_Syntax_Syntax.n  in
                             match uu____742 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____752 ->
                                 let repr =
                                   let uu____754 =
                                     FStar_Syntax_Util.type_u ()  in
                                   match uu____754 with
                                   | (t,uu____758) ->
                                       let expected_k =
                                         let uu____762 =
                                           let uu____766 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____767 =
                                             let uu____769 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             [uu____769]  in
                                           uu____766 :: uu____767  in
                                         let uu____770 =
                                           FStar_Syntax_Syntax.mk_GTotal t
                                            in
                                         FStar_Syntax_Util.arrow uu____762
                                           uu____770
                                          in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k
                                    in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr
                                      in
                                   let uu____783 =
                                     let uu____786 =
                                       let uu____787 =
                                         let uu____797 =
                                           let uu____799 =
                                             FStar_Syntax_Syntax.as_arg t  in
                                           let uu____800 =
                                             let uu____802 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____802]  in
                                           uu____799 :: uu____800  in
                                         (repr1, uu____797)  in
                                       FStar_Syntax_Syntax.Tm_app uu____787
                                        in
                                     FStar_Syntax_Syntax.mk uu____786  in
                                   uu____783 None FStar_Range.dummyRange  in
                                 let mk_repr a1 wp =
                                   let uu____821 =
                                     FStar_Syntax_Syntax.bv_to_name a1  in
                                   mk_repr' uu____821 wp  in
                                 let destruct_repr t =
                                   let uu____832 =
                                     let uu____833 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____833.FStar_Syntax_Syntax.n  in
                                   match uu____832 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____842,(t1,uu____844)::(wp,uu____846)::[])
                                       -> (t1, wp)
                                   | uu____880 ->
                                       failwith "Unexpected repr type"
                                    in
                                 let bind_repr =
                                   let r =
                                     let uu____889 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_All.pipe_right uu____889
                                       FStar_Syntax_Syntax.fv_to_tm
                                      in
                                   let uu____890 = fresh_effect_signature ()
                                      in
                                   match uu____890 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____904 =
                                           let uu____908 =
                                             let uu____909 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____909
                                              in
                                           [uu____908]  in
                                         let uu____910 =
                                           FStar_Syntax_Syntax.mk_Total wp_b
                                            in
                                         FStar_Syntax_Util.arrow uu____904
                                           uu____910
                                          in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a
                                          in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b
                                          in
                                       let x_a =
                                         let uu____916 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____916
                                          in
                                       let wp_g_x =
                                         let uu____920 =
                                           let uu____921 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g
                                              in
                                           let uu____922 =
                                             let uu____923 =
                                               let uu____924 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____924
                                                in
                                             [uu____923]  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____921 uu____922
                                            in
                                         uu____920 None
                                           FStar_Range.dummyRange
                                          in
                                       let res =
                                         let wp =
                                           let uu____935 =
                                             let uu____936 =
                                               let uu____937 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp
                                                  in
                                               FStar_All.pipe_right uu____937
                                                 FStar_Pervasives.snd
                                                in
                                             let uu____942 =
                                               let uu____943 =
                                                 let uu____945 =
                                                   let uu____947 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   let uu____948 =
                                                     let uu____950 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b
                                                        in
                                                     let uu____951 =
                                                       let uu____953 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f
                                                          in
                                                       let uu____954 =
                                                         let uu____956 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g
                                                            in
                                                         [uu____956]  in
                                                       uu____953 :: uu____954
                                                        in
                                                     uu____950 :: uu____951
                                                      in
                                                   uu____947 :: uu____948  in
                                                 r :: uu____945  in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____943
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____936 uu____942
                                              in
                                           uu____935 None
                                             FStar_Range.dummyRange
                                            in
                                         mk_repr b wp  in
                                       let expected_k =
                                         let uu____964 =
                                           let uu____968 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____969 =
                                             let uu____971 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b
                                                in
                                             let uu____972 =
                                               let uu____974 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f
                                                  in
                                               let uu____975 =
                                                 let uu____977 =
                                                   let uu____978 =
                                                     let uu____979 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f
                                                        in
                                                     mk_repr a uu____979  in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____978
                                                    in
                                                 let uu____980 =
                                                   let uu____982 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g
                                                      in
                                                   let uu____983 =
                                                     let uu____985 =
                                                       let uu____986 =
                                                         let uu____987 =
                                                           let uu____991 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a
                                                              in
                                                           [uu____991]  in
                                                         let uu____992 =
                                                           let uu____995 =
                                                             mk_repr b wp_g_x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____995
                                                            in
                                                         FStar_Syntax_Util.arrow
                                                           uu____987
                                                           uu____992
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____986
                                                        in
                                                     [uu____985]  in
                                                   uu____982 :: uu____983  in
                                                 uu____977 :: uu____980  in
                                               uu____974 :: uu____975  in
                                             uu____971 :: uu____972  in
                                           uu____968 :: uu____969  in
                                         let uu____996 =
                                           FStar_Syntax_Syntax.mk_Total res
                                            in
                                         FStar_Syntax_Util.arrow uu____964
                                           uu____996
                                          in
                                       let uu____999 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k
                                          in
                                       (match uu____999 with
                                        | (expected_k1,uu____1004,uu____1005)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let env3 =
                                              let uu___96_1009 = env2  in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___96_1009.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___96_1009.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___96_1009.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___96_1009.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.is_native_tactic)
                                              }  in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1
                                               in
                                            br)
                                    in
                                 let return_repr =
                                   let x_a =
                                     let uu____1016 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____1016
                                      in
                                   let res =
                                     let wp =
                                       let uu____1023 =
                                         let uu____1024 =
                                           let uu____1025 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp
                                              in
                                           FStar_All.pipe_right uu____1025
                                             FStar_Pervasives.snd
                                            in
                                         let uu____1030 =
                                           let uu____1031 =
                                             let uu____1033 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             let uu____1034 =
                                               let uu____1036 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               [uu____1036]  in
                                             uu____1033 :: uu____1034  in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1031
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1024 uu____1030
                                          in
                                       uu____1023 None FStar_Range.dummyRange
                                        in
                                     mk_repr a wp  in
                                   let expected_k =
                                     let uu____1044 =
                                       let uu____1048 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____1049 =
                                         let uu____1051 =
                                           FStar_Syntax_Syntax.mk_binder x_a
                                            in
                                         [uu____1051]  in
                                       uu____1048 :: uu____1049  in
                                     let uu____1052 =
                                       FStar_Syntax_Syntax.mk_Total res  in
                                     FStar_Syntax_Util.arrow uu____1044
                                       uu____1052
                                      in
                                   let uu____1055 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k
                                      in
                                   match uu____1055 with
                                   | (expected_k1,uu____1063,uu____1064) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                          in
                                       let uu____1067 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1
                                          in
                                       (match uu____1067 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1079 ->
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos)))))
                                    in
                                 let actions =
                                   let check_action act =
                                     let uu____1099 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ
                                        in
                                     match uu____1099 with
                                     | (act_typ,uu____1104,g_t) ->
                                         let env' =
                                           let uu___97_1107 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ
                                              in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___97_1107.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___97_1107.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___97_1107.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___97_1107.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___97_1107.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___97_1107.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___97_1107.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___97_1107.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___97_1107.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___97_1107.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___97_1107.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___97_1107.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___97_1107.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___97_1107.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.is_native_tactic)
                                           }  in
                                         ((let uu____1109 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED")
                                              in
                                           if uu____1109
                                           then
                                             let uu____1110 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn
                                                in
                                             let uu____1111 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ
                                                in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1110 uu____1111
                                           else ());
                                          (let uu____1113 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn
                                              in
                                           match uu____1113 with
                                           | (act_defn,uu____1118,g_a) ->
                                               let act_defn1 =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant]
                                                   env1 act_defn
                                                  in
                                               let act_typ1 =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant;
                                                   FStar_TypeChecker_Normalize.Eager_unfolding;
                                                   FStar_TypeChecker_Normalize.Beta]
                                                   env1 act_typ
                                                  in
                                               let uu____1122 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1
                                                    in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1140 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c
                                                        in
                                                     (match uu____1140 with
                                                      | (bs1,uu____1146) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let k =
                                                            let uu____1153 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res
                                                               in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1153
                                                             in
                                                          let uu____1156 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k
                                                             in
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
                                                               act_typ2
                                                              in
                                                           let uu____1172 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2
                                                              in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1171
                                                             uu____1172
                                                            in
                                                         (uu____1170,
                                                           (act_defn1.FStar_Syntax_Syntax.pos))
                                                          in
                                                       FStar_Errors.Error
                                                         uu____1167
                                                        in
                                                     raise uu____1166
                                                  in
                                               (match uu____1122 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k
                                                       in
                                                    ((let uu____1179 =
                                                        let uu____1180 =
                                                          let uu____1181 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g
                                                             in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1181
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1180
                                                         in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1179);
                                                     (let act_typ2 =
                                                        let uu____1185 =
                                                          let uu____1186 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k
                                                             in
                                                          uu____1186.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____1185 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1203 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____1203
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1210
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)
                                                                    in
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
                                                                    env1 a1
                                                                     in
                                                                    [uu____1231]
                                                                     in
                                                                    let uu____1232
                                                                    =
                                                                    let uu____1238
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1238]
                                                                     in
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
                                                                    }  in
                                                                    let uu____1239
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1239))
                                                        | uu____1242 ->
                                                            failwith ""
                                                         in
                                                      let uu____1245 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1
                                                         in
                                                      match uu____1245 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2
                                                             in
                                                          let uu___98_1251 =
                                                            act  in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___98_1251.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___98_1251.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___98_1251.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          })))))
                                      in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action)
                                    in
                                 (repr, bind_repr, return_repr, actions)
                              in
                           match uu____736 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1267 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature
                                    in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1267
                                  in
                               let uu____1270 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t
                                  in
                               (match uu____1270 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1276 =
                                        let uu____1279 =
                                          let uu____1280 =
                                            FStar_Syntax_Subst.compress t1
                                             in
                                          uu____1280.FStar_Syntax_Syntax.n
                                           in
                                        (effect_params, uu____1279)  in
                                      match uu____1276 with
                                      | ([],uu____1283) -> t1
                                      | (uu____1289,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1290,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1302 -> failwith "Impossible"
                                       in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1313 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts
                                           in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1313
                                         in
                                      let m = FStar_List.length (fst ts1)  in
                                      (let uu____1319 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1320 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1)
                                                in
                                             Prims.op_Negation uu____1320))
                                           && (m <> n1)
                                          in
                                       if uu____1319
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic"
                                            in
                                         let uu____1334 =
                                           let uu____1335 =
                                             FStar_Util.string_of_int n1  in
                                           let uu____1336 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1
                                              in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1335 uu____1336
                                            in
                                         failwith uu____1334
                                       else ());
                                      ts1  in
                                    let close_action act =
                                      let uu____1342 =
                                        close1 (~- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn))
                                         in
                                      match uu____1342 with
                                      | (univs2,defn) ->
                                          let uu____1347 =
                                            close1 (~- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ))
                                             in
                                          (match uu____1347 with
                                           | (univs',typ) ->
                                               let uu___99_1353 = act  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___99_1353.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___99_1353.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___99_1353.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               })
                                       in
                                    let ed3 =
                                      let uu___100_1356 = ed2  in
                                      let uu____1357 =
                                        close1 (Prims.parse_int "0")
                                          return_wp
                                         in
                                      let uu____1358 =
                                        close1 (Prims.parse_int "1") bind_wp
                                         in
                                      let uu____1359 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1
                                         in
                                      let uu____1360 =
                                        close1 (Prims.parse_int "0") ite_wp
                                         in
                                      let uu____1361 =
                                        close1 (Prims.parse_int "0") stronger
                                         in
                                      let uu____1362 =
                                        close1 (Prims.parse_int "1") close_wp
                                         in
                                      let uu____1363 =
                                        close1 (Prims.parse_int "0") assert_p
                                         in
                                      let uu____1364 =
                                        close1 (Prims.parse_int "0") assume_p
                                         in
                                      let uu____1365 =
                                        close1 (Prims.parse_int "0") null_wp
                                         in
                                      let uu____1366 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp
                                         in
                                      let uu____1367 =
                                        let uu____1368 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr)
                                           in
                                        snd uu____1368  in
                                      let uu____1374 =
                                        close1 (Prims.parse_int "0")
                                          return_repr
                                         in
                                      let uu____1375 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr
                                         in
                                      let uu____1376 =
                                        FStar_List.map close_action actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___100_1356.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___100_1356.FStar_Syntax_Syntax.mname);
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
                                      }  in
                                    ((let uu____1379 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED"))
                                         in
                                      if uu____1379
                                      then
                                        let uu____1380 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print_string uu____1380
                                      else ());
                                     ed3)))))))

and cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt option)
  =
  fun env  ->
    fun ed  ->
      let uu____1384 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____1384 with
      | (effect_binders_un,signature_un) ->
          let uu____1394 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____1394 with
           | (effect_binders,env1,uu____1405) ->
               let uu____1406 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____1406 with
                | (signature,uu____1415) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1424  ->
                           match uu____1424 with
                           | (bv,qual) ->
                               let uu____1431 =
                                 let uu___101_1432 = bv  in
                                 let uu____1433 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___101_1432.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___101_1432.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1433
                                 }  in
                               (uu____1431, qual)) effect_binders
                       in
                    let uu____1436 =
                      let uu____1441 =
                        let uu____1442 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____1442.FStar_Syntax_Syntax.n  in
                      match uu____1441 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1450)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1465 ->
                          failwith "bad shape for effect-for-free signature"
                       in
                    (match uu____1436 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1482 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____1482
                           then
                             let uu____1483 =
                               let uu____1485 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               Some uu____1485  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1483
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____1509 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____1509 with
                           | (t2,comp,uu____1517) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____1528 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____1528 with
                          | (repr,_comp) ->
                              ((let uu____1541 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____1541
                                then
                                  let uu____1542 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1542
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange)
                                   in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr
                                   in
                                let wp_type1 = recheck_debug "*" env1 wp_type
                                   in
                                let wp_a =
                                  let uu____1548 =
                                    let uu____1549 =
                                      let uu____1550 =
                                        let uu____1560 =
                                          let uu____1564 =
                                            let uu____1567 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____1568 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____1567, uu____1568)  in
                                          [uu____1564]  in
                                        (wp_type1, uu____1560)  in
                                      FStar_Syntax_Syntax.Tm_app uu____1550
                                       in
                                    mk1 uu____1549  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1548
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____1583 =
                                      let uu____1586 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____1586)  in
                                    let uu____1587 =
                                      let uu____1591 =
                                        let uu____1592 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a
                                           in
                                        FStar_All.pipe_right uu____1592
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____1591]  in
                                    uu____1583 :: uu____1587  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let effect_signature1 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature
                                   in
                                let sigelts = FStar_Util.mk_ref []  in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name  in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1
                                     in
                                  let uu____1635 = item  in
                                  match uu____1635 with
                                  | (u_item,item1) ->
                                      let uu____1647 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____1647 with
                                       | (item2,item_comp) ->
                                           ((let uu____1657 =
                                               let uu____1658 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____1658
                                                in
                                             if uu____1657
                                             then
                                               let uu____1659 =
                                                 let uu____1660 =
                                                   let uu____1661 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____1662 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1661 uu____1662
                                                    in
                                                 FStar_Errors.Err uu____1660
                                                  in
                                               raise uu____1659
                                             else ());
                                            (let uu____1664 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____1664 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1))))
                                   in
                                let uu____1677 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____1677 with
                                | (dmff_env1,uu____1690,bind_wp,bind_elab) ->
                                    let uu____1693 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____1693 with
                                     | (dmff_env2,uu____1706,return_wp,return_elab)
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
                                           }  in
                                         let lift_from_pure_wp =
                                           let uu____1713 =
                                             let uu____1714 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____1714.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1713 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1742 =
                                                 let uu____1750 =
                                                   let uu____1753 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1753
                                                    in
                                                 match uu____1750 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1787 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____1742 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1809 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1809 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1820 =
                                                          let uu____1821 =
                                                            let uu____1831 =
                                                              let uu____1835
                                                                =
                                                                let uu____1838
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11)
                                                                   in
                                                                let uu____1839
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____1838,
                                                                  uu____1839)
                                                                 in
                                                              [uu____1835]
                                                               in
                                                            (wp_type1,
                                                              uu____1831)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1821
                                                           in
                                                        mk1 uu____1820  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____1847 =
                                                      let uu____1852 =
                                                        let uu____1853 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1853
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1852
                                                       in
                                                    (match uu____1847 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1866
                                                           =
                                                           let error_msg =
                                                             let uu____1868 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1868
                                                               (match what'
                                                                with
                                                                | None  ->
                                                                    "None"
                                                                | Some rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                              in
                                                           failwith error_msg
                                                            in
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
                                                                (let uu____1874
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
                                                                    FStar_Syntax_Util.ktype0
                                                                     in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    Some g'
                                                                    ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    None  ->
                                                                    fail ())
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____1874
                                                                   FStar_Pervasives.ignore)));
                                                          (let wp =
                                                             let t2 =
                                                               (fst b21).FStar_Syntax_Syntax.sort
                                                                in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2
                                                                in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp" None
                                                               pure_wp_type
                                                              in
                                                           let body3 =
                                                             let uu____1894 =
                                                               let uu____1895
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____1896
                                                                 =
                                                                 let uu____1897
                                                                   =
                                                                   let uu____1901
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____1901,
                                                                    None)
                                                                    in
                                                                 [uu____1897]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1895
                                                                 uu____1896
                                                                in
                                                             uu____1894 None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____1917 =
                                                             let uu____1918 =
                                                               let uu____1922
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____1922]
                                                                in
                                                             b11 ::
                                                               uu____1918
                                                              in
                                                           let uu____1925 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____1917
                                                             uu____1925
                                                             (Some rc_gtot)))))
                                           | uu____1926 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let return_wp1 =
                                           let uu____1928 =
                                             let uu____1929 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____1929.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1928 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1957 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1957
                                                 (Some rc_gtot)
                                           | uu____1964 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let bind_wp1 =
                                           let uu____1966 =
                                             let uu____1967 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____1967.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1966 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None
                                                  in
                                               let uu____1986 =
                                                 let uu____1987 =
                                                   let uu____1989 =
                                                     let uu____1990 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____1990
                                                      in
                                                   [uu____1989]  in
                                                 FStar_List.append uu____1987
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____1986 body what
                                           | uu____1991 ->
                                               failwith
                                                 "unexpected shape for bind"
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2011 =
                                                let uu____2012 =
                                                  let uu____2013 =
                                                    let uu____2023 =
                                                      let uu____2024 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      snd uu____2024  in
                                                    (t, uu____2023)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2013
                                                   in
                                                mk1 uu____2012  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2011)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2047 = f a2  in
                                               [uu____2047]
                                           | x::xs ->
                                               let uu____2051 =
                                                 apply_last1 f xs  in
                                               x :: uu____2051
                                            in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname
                                              in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p
                                              in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange
                                              in
                                           let uu____2066 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____2066 with
                                           | Some (_us,_t) ->
                                               ((let uu____2083 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____2083
                                                 then
                                                   let uu____2084 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2084
                                                 else ());
                                                (let uu____2086 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2086))
                                           | None  ->
                                               let uu____2091 =
                                                 let uu____2094 = mk_lid name
                                                    in
                                                 let uu____2095 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2094 uu____2095
                                                  in
                                               (match uu____2091 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2099 =
                                                        let uu____2101 =
                                                          FStar_ST.read
                                                            sigelts
                                                           in
                                                        sigelt :: uu____2101
                                                         in
                                                      FStar_ST.write sigelts
                                                        uu____2099);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____2112 =
                                             let uu____2114 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____2115 =
                                               FStar_ST.read sigelts  in
                                             uu____2114 :: uu____2115  in
                                           FStar_ST.write sigelts uu____2112);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____2125 =
                                              let uu____2127 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false"))
                                                 in
                                              let uu____2128 =
                                                FStar_ST.read sigelts  in
                                              uu____2127 :: uu____2128  in
                                            FStar_ST.write sigelts uu____2125);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____2138 =
                                               let uu____2140 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____2141 =
                                                 FStar_ST.read sigelts  in
                                               uu____2140 :: uu____2141  in
                                             FStar_ST.write sigelts
                                               uu____2138);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____2151 =
                                                let uu____2153 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false"))
                                                   in
                                                let uu____2154 =
                                                  FStar_ST.read sigelts  in
                                                uu____2153 :: uu____2154  in
                                              FStar_ST.write sigelts
                                                uu____2151);
                                             (let uu____2162 =
                                                FStar_List.fold_left
                                                  (fun uu____2169  ->
                                                     fun action  ->
                                                       match uu____2169 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____2182 =
                                                             let uu____2186 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2186
                                                               params_un
                                                              in
                                                           (match uu____2182
                                                            with
                                                            | (action_params,env',uu____2192)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2201
                                                                     ->
                                                                    match uu____2201
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2208
                                                                    =
                                                                    let uu___102_2209
                                                                    = bv  in
                                                                    let uu____2210
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___102_2209.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___102_2209.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2210
                                                                    }  in
                                                                    (uu____2208,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____2214
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____2214
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
                                                                     in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp
                                                                     in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1
                                                                     in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab
                                                                     in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp
                                                                     in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    None  in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____2235
                                                                    ->
                                                                    let uu____2236
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2236
                                                                     in
                                                                    ((
                                                                    let uu____2240
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____2240
                                                                    then
                                                                    let uu____2241
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____2242
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____2243
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2244
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2241
                                                                    uu____2242
                                                                    uu____2243
                                                                    uu____2244
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2
                                                                     in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2248
                                                                    =
                                                                    let uu____2250
                                                                    =
                                                                    let uu___103_2251
                                                                    = action
                                                                     in
                                                                    let uu____2252
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____2253
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___103_2251.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___103_2251.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___103_2251.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2252;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2253
                                                                    }  in
                                                                    uu____2250
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____2248))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____2162 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a
                                                       in
                                                    let binders =
                                                      let uu____2273 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____2274 =
                                                        let uu____2276 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____2276]  in
                                                      uu____2273 ::
                                                        uu____2274
                                                       in
                                                    let uu____2277 =
                                                      let uu____2278 =
                                                        let uu____2279 =
                                                          let uu____2280 =
                                                            let uu____2290 =
                                                              let uu____2294
                                                                =
                                                                let uu____2297
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____2298
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____2297,
                                                                  uu____2298)
                                                                 in
                                                              [uu____2294]
                                                               in
                                                            (repr,
                                                              uu____2290)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2280
                                                           in
                                                        mk1 uu____2279  in
                                                      let uu____2306 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2278
                                                        uu____2306
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2277 None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____2309 =
                                                    let uu____2314 =
                                                      let uu____2315 =
                                                        let uu____2318 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2318
                                                         in
                                                      uu____2315.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____2314 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2326)
                                                        ->
                                                        let uu____2343 =
                                                          let uu____2352 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____2352
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2383 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____2343
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2411 =
                                                               let uu____2412
                                                                 =
                                                                 let uu____2415
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2415
                                                                  in
                                                               uu____2412.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____2411
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2432
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____2432
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2441
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2452
                                                                     ->
                                                                    match uu____2452
                                                                    with
                                                                    | 
                                                                    (bv,uu____2456)
                                                                    ->
                                                                    let uu____2457
                                                                    =
                                                                    let uu____2458
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2458
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2457
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2441
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
                                                                    uu____2491
                                                                    ->
                                                                    let uu____2495
                                                                    =
                                                                    let uu____2496
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2496
                                                                     in
                                                                    failwith
                                                                    uu____2495
                                                                     in
                                                                    let uu____2499
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____2502
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None  in
                                                                    (uu____2499,
                                                                    uu____2502)))
                                                              | uu____2507 ->
                                                                  let uu____2508
                                                                    =
                                                                    let uu____2509
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2509
                                                                     in
                                                                  failwith
                                                                    uu____2508))
                                                    | uu____2514 ->
                                                        let uu____2515 =
                                                          let uu____2516 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1
                                                             in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2516
                                                           in
                                                        failwith uu____2515
                                                     in
                                                  (match uu____2309 with
                                                   | (pre,post) ->
                                                       ((let uu____2533 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____2535 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____2537 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___104_2539
                                                             = ed  in
                                                           let uu____2540 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____2541 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____2542 =
                                                             let uu____2543 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____2543)
                                                              in
                                                           let uu____2549 =
                                                             let uu____2550 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____2550)
                                                              in
                                                           let uu____2556 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____2557 =
                                                             let uu____2558 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____2558)
                                                              in
                                                           let uu____2564 =
                                                             let uu____2565 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____2565)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2540;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2541;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2542;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2549;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2556;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2557;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2564;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____2571 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____2571
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2582
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____2582
                                                               then
                                                                 let uu____2583
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____2583
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____2595
                                                                    =
                                                                    let uu____2597
                                                                    =
                                                                    let uu____2603
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____2603)
                                                                     in
                                                                    Some
                                                                    uu____2597
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2595;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    }  in
                                                                   let uu____2614
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   Some
                                                                    uu____2614
                                                                 else None
                                                                  in
                                                               let uu____2616
                                                                 =
                                                                 let uu____2618
                                                                   =
                                                                   let uu____2620
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____2620
                                                                    in
                                                                 FStar_List.append
                                                                   uu____2618
                                                                   sigelts'
                                                                  in
                                                               (uu____2616,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))

and tc_lex_t :
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
                (lex_t1,[],[],t,uu____2643,uu____2644);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2646;
              FStar_Syntax_Syntax.sigattrs = uu____2647;_}::{
                                                              FStar_Syntax_Syntax.sigel
                                                                =
                                                                FStar_Syntax_Syntax.Sig_datacon
                                                                (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2651);
                                                              FStar_Syntax_Syntax.sigrng
                                                                = r1;
                                                              FStar_Syntax_Syntax.sigquals
                                                                = [];
                                                              FStar_Syntax_Syntax.sigmeta
                                                                = uu____2653;
                                                              FStar_Syntax_Syntax.sigattrs
                                                                = uu____2654;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2658);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2660;
                FStar_Syntax_Syntax.sigattrs = uu____2661;_}::[]
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
              let u = FStar_Syntax_Syntax.new_univ_name (Some r)  in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r
                 in
              let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1  in
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
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }  in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1)  in
              let lex_top_t =
                let uu____2703 =
                  let uu____2706 =
                    let uu____2707 =
                      let uu____2712 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None
                         in
                      (uu____2712, [FStar_Syntax_Syntax.U_name utop])  in
                    FStar_Syntax_Syntax.Tm_uinst uu____2707  in
                  FStar_Syntax_Syntax.mk uu____2706  in
                uu____2703 None r1  in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
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
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }  in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2)  in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2)  in
              let lex_cons_t =
                let a =
                  let uu____2732 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2
                     in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2732  in
                let hd1 =
                  let uu____2738 = FStar_Syntax_Syntax.bv_to_name a  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2738  in
                let tl1 =
                  let uu____2740 =
                    let uu____2741 =
                      let uu____2744 =
                        let uu____2745 =
                          let uu____2750 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None
                             in
                          (uu____2750, [FStar_Syntax_Syntax.U_name ucons2])
                           in
                        FStar_Syntax_Syntax.Tm_uinst uu____2745  in
                      FStar_Syntax_Syntax.mk uu____2744  in
                    uu____2741 None r2  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2740  in
                let res =
                  let uu____2763 =
                    let uu____2766 =
                      let uu____2767 =
                        let uu____2772 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None
                           in
                        (uu____2772,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]])
                         in
                      FStar_Syntax_Syntax.Tm_uinst uu____2767  in
                    FStar_Syntax_Syntax.mk uu____2766  in
                  uu____2763 None r2  in
                let uu____2782 = FStar_Syntax_Syntax.mk_Total res  in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2782
                 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t
                 in
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
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }  in
              let uu____2804 = FStar_TypeChecker_Env.get_range env  in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2804;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }
          | uu____2807 ->
              let uu____2809 =
                let uu____2810 =
                  let uu____2811 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                     in
                  FStar_Syntax_Print.sigelt_to_string uu____2811  in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2810  in
              failwith uu____2809

and tc_assume :
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
            let env1 = FStar_TypeChecker_Env.set_range env r  in
            let uu____2821 = FStar_Syntax_Util.type_u ()  in
            match uu____2821 with
            | (k,uu____2825) ->
                let phi1 =
                  let uu____2827 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____2827
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_assume (lid, phi1));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = quals;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 })

and tc_inductive :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env0 = env  in
          let uu____2837 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids
             in
          match uu____2837 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2856 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas
                   in
                FStar_All.pipe_right uu____2856 FStar_List.flatten  in
              ((let uu____2864 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____2864
                then ()
                else
                  (let env1 =
                     FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env1
                           in
                        if Prims.op_Negation b
                        then
                          let uu____2870 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2876,uu____2877,uu____2878,uu____2879,uu____2880)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2885 -> failwith "Impossible!"  in
                          match uu____2870 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2894 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2898,uu____2899,uu____2900,uu____2901,uu____2902)
                        -> lid
                    | uu____2907 -> failwith "Impossible"  in
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"]  in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip
                   in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals
                   in
                let uu____2913 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq
                   in
                if uu____2913
                then ([sig_bndle], data_ops_ses)
                else
                  (let is_unopteq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals
                      in
                   let ses1 =
                     if is_unopteq
                     then
                       FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                     else
                       FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                      in
                   let uu____2931 =
                     let uu____2933 =
                       let uu____2934 = FStar_TypeChecker_Env.get_range env0
                          in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____2934;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     uu____2933 :: ses1  in
                   (uu____2931, data_ops_ses))))

and tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list)
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2952 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____2965 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids
              in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____2995 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____2995 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3020 = FStar_Options.set_options t s  in
             match uu____3020 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s1 ->
                 raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s1), r))
              in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____3037 =
                    FStar_Options.restore_cmd_line_options false  in
                  FStar_All.pipe_right uu____3037 FStar_Pervasives.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____3043 = cps_and_elaborate env1 ne  in
           (match uu____3043 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [(let uu___105_3064 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___105_3064.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_3064.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_3064.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___105_3064.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | None  ->
                      [(let uu___106_3065 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___106_3065.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___106_3065.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___106_3065.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___106_3065.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___107_3071 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___107_3071.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___107_3071.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___107_3071.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___107_3071.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target
              in
           let uu____3077 =
             let uu____3082 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3082
              in
           (match uu____3077 with
            | (a,wp_a_src) ->
                let uu____3093 =
                  let uu____3098 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3098
                   in
                (match uu____3093 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3110 =
                         let uu____3112 =
                           let uu____3113 =
                             let uu____3118 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____3118)  in
                           FStar_Syntax_Syntax.NT uu____3113  in
                         [uu____3112]  in
                       FStar_Syntax_Subst.subst uu____3110 wp_b_tgt  in
                     let expected_k =
                       let uu____3122 =
                         let uu____3126 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____3127 =
                           let uu____3129 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____3129]  in
                         uu____3126 :: uu____3127  in
                       let uu____3130 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____3122 uu____3130  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3151 =
                           let uu____3152 =
                             let uu____3155 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str
                                in
                             let uu____3156 =
                               FStar_TypeChecker_Env.get_range env1  in
                             (uu____3155, uu____3156)  in
                           FStar_Errors.Error uu____3152  in
                         raise uu____3151  in
                       let uu____3159 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____3159 with
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____3178 =
                             let uu____3179 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____3179  in
                           if uu____3178
                           then no_reify eff_name
                           else
                             (let uu____3184 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____3185 =
                                let uu____3188 =
                                  let uu____3189 =
                                    let uu____3199 =
                                      let uu____3201 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____3202 =
                                        let uu____3204 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____3204]  in
                                      uu____3201 :: uu____3202  in
                                    (repr, uu____3199)  in
                                  FStar_Syntax_Syntax.Tm_app uu____3189  in
                                FStar_Syntax_Syntax.mk uu____3188  in
                              uu____3185 None uu____3184)
                        in
                     let uu____3214 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3229,lift_wp)) ->
                           let uu____3242 =
                             check_and_gen env1 lift_wp expected_k  in
                           (lift, uu____3242)
                       | (Some (what,lift),None ) ->
                           ((let uu____3257 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____3257
                             then
                               let uu____3258 =
                                 FStar_Syntax_Print.term_to_string lift  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3258
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange)
                                in
                             let uu____3261 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift  in
                             match uu____3261 with
                             | (lift1,comp,uu____3270) ->
                                 let uu____3271 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1
                                    in
                                 (match uu____3271 with
                                  | (uu____3278,lift_wp,lift_elab) ->
                                      let uu____3281 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____3282 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((Some ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____3214 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___108_3305 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___108_3305.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___108_3305.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___108_3305.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___108_3305.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___108_3305.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___108_3305.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___108_3305.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___108_3305.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___108_3305.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___108_3305.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___108_3305.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___108_3305.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___108_3305.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___108_3305.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___108_3305.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___108_3305.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___108_3305.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___108_3305.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___108_3305.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___108_3305.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___108_3305.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___108_3305.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___108_3305.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___108_3305.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___108_3305.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___108_3305.FStar_TypeChecker_Env.is_native_tactic)
                            }  in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some (uu____3309,lift1) ->
                                let uu____3316 =
                                  let uu____3321 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____3321
                                   in
                                (match uu____3316 with
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src1
                                        in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a1  in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a
                                        in
                                     let repr_f =
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.source
                                         a_typ wp_a_typ
                                        in
                                     let repr_result =
                                       let lift_wp1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env2 (snd lift_wp)
                                          in
                                       let lift_wp_a =
                                         let uu____3343 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____3344 =
                                           let uu____3347 =
                                             let uu____3348 =
                                               let uu____3358 =
                                                 let uu____3360 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____3361 =
                                                   let uu____3363 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____3363]  in
                                                 uu____3360 :: uu____3361  in
                                               (lift_wp1, uu____3358)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3348
                                              in
                                           FStar_Syntax_Syntax.mk uu____3347
                                            in
                                         uu____3344 None uu____3343  in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____3376 =
                                         let uu____3380 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____3381 =
                                           let uu____3383 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____3384 =
                                             let uu____3386 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____3386]  in
                                           uu____3383 :: uu____3384  in
                                         uu____3380 :: uu____3381  in
                                       let uu____3387 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____3376
                                         uu____3387
                                        in
                                     let uu____3390 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____3390 with
                                      | (expected_k2,uu____3396,uu____3397)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2
                                             in
                                          Some lift2))
                             in
                          let sub2 =
                            let uu___109_3400 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___109_3400.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___109_3400.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___110_3402 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___110_3402.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___110_3402.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___110_3402.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___110_3402.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1  in
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3415 = FStar_Syntax_Subst.open_comp tps c  in
           (match uu____3415 with
            | (tps1,c1) ->
                let uu____3424 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1  in
                (match uu____3424 with
                 | (tps2,env3,us) ->
                     let uu____3435 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1  in
                     (match uu____3435 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2
                               in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2
                               in
                            let uu____3449 =
                              let uu____3450 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r
                                 in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3450
                               in
                            match uu____3449 with
                            | (uvs1,t) ->
                                let uu____3463 =
                                  let uu____3471 =
                                    let uu____3474 =
                                      let uu____3475 =
                                        FStar_Syntax_Subst.compress t  in
                                      uu____3475.FStar_Syntax_Syntax.n  in
                                    (tps3, uu____3474)  in
                                  match uu____3471 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3485,c4)) -> ([], c4)
                                  | (uu____3509,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3527 -> failwith "Impossible"  in
                                (match uu____3463 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____3558 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t
                                            in
                                         match uu____3558 with
                                         | (uu____3561,t1) ->
                                             let uu____3563 =
                                               let uu____3564 =
                                                 let uu____3567 =
                                                   let uu____3568 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid
                                                      in
                                                   let uu____3569 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int
                                                      in
                                                   let uu____3574 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3568 uu____3569
                                                     uu____3574
                                                    in
                                                 (uu____3567, r)  in
                                               FStar_Errors.Error uu____3564
                                                in
                                             raise uu____3563)
                                      else ();
                                      (let se1 =
                                         let uu___111_3577 = se  in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___111_3577.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___111_3577.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___111_3577.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___111_3577.FStar_Syntax_Syntax.sigattrs)
                                         }  in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3587,uu____3588,uu____3589) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3591  ->
                   match uu___85_3591 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3592 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3595,uu____3596) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3600  ->
                   match uu___85_3600 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3601 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3608 =
             if uvs = []
             then
               let uu____3609 =
                 let uu____3610 = FStar_Syntax_Util.type_u ()  in
                 fst uu____3610  in
               check_and_gen env2 t uu____3609
             else
               (let uu____3614 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                match uu____3614 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3620 =
                        let uu____3621 = FStar_Syntax_Util.type_u ()  in
                        fst uu____3621  in
                      tc_check_trivial_guard env2 t1 uu____3620  in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2
                       in
                    let uu____3625 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                    (uvs1, uu____3625))
              in
           (match uu____3608 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___112_3635 = se  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___112_3635.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___112_3635.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___112_3635.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___112_3635.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi) ->
           let se1 = tc_assume env1 lid phi se.FStar_Syntax_Syntax.sigquals r
              in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit
              in
           let uu____3647 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____3647 with
            | (e1,c,g1) ->
                let uu____3658 =
                  let uu____3662 =
                    let uu____3664 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r
                       in
                    Some uu____3664  in
                  let uu____3665 =
                    let uu____3668 = c.FStar_Syntax_Syntax.comp ()  in
                    (e1, uu____3668)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3662 uu____3665
                   in
                (match uu____3658 with
                 | (e2,uu____3678,g) ->
                     ((let uu____3681 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3681);
                      (let se1 =
                         let uu___113_3683 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___113_3683.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___113_3683.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___113_3683.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___113_3683.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3716 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____3716
                 then Some q
                 else
                   (let uu____3729 =
                      let uu____3730 =
                        let uu____3733 =
                          let uu____3734 = FStar_Syntax_Print.lid_to_string l
                             in
                          let uu____3735 =
                            FStar_Syntax_Print.quals_to_string q  in
                          let uu____3736 =
                            FStar_Syntax_Print.quals_to_string q'  in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3734 uu____3735 uu____3736
                           in
                        (uu____3733, r)  in
                      FStar_Errors.Error uu____3730  in
                    raise uu____3729)
              in
           let uu____3739 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3760  ->
                     fun lb  ->
                       match uu____3760 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____3784 =
                             let uu____3790 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____3790 with
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | Some ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals
                                    in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____3842 ->
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
                                  (let uu____3854 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef))
                                      in
                                   (false, uu____3854, quals_opt1)))
                              in
                           (match uu____3784 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____3739 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3907 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___86_3909  ->
                                match uu___86_3909 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____3910 -> false))
                         in
                      if uu____3907
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____3918 =
                    let uu____3921 =
                      let uu____3922 =
                        let uu____3930 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r
                           in
                        (((fst lbs), lbs'1), uu____3930)  in
                      FStar_Syntax_Syntax.Tm_let uu____3922  in
                    FStar_Syntax_Syntax.mk uu____3921  in
                  uu____3918 None r  in
                let uu____3952 =
                  let uu____3958 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___114_3962 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___114_3962.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___114_3962.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___114_3962.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___114_3962.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___114_3962.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___114_3962.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___114_3962.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___114_3962.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___114_3962.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___114_3962.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___114_3962.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___114_3962.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___114_3962.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___114_3962.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___114_3962.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___114_3962.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___114_3962.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___114_3962.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___114_3962.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___114_3962.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___114_3962.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___114_3962.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___114_3962.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___114_3962.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___114_3962.FStar_TypeChecker_Env.is_native_tactic)
                       }) e
                     in
                  match uu____3958 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3970;
                       FStar_Syntax_Syntax.pos = uu____3971;
                       FStar_Syntax_Syntax.vars = uu____3972;_},uu____3973,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3992,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____3997 -> quals  in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___87_4000  ->
                             match uu___87_4000 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4002 =
                                   let uu____4003 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp
                                             in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____4007 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____4007)
                                          else ();
                                          ok) (snd lbs1)
                                      in
                                   Prims.op_Negation uu____4003  in
                                 if uu____4002
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1
                         in
                      ((let uu___115_4016 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___115_4016.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___115_4016.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___115_4016.FStar_Syntax_Syntax.sigattrs)
                        }), lbs1)
                  | uu____4021 -> failwith "impossible"  in
                (match uu____3952 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____4048 = log env2  in
                       if uu____4048
                       then
                         let uu____4049 =
                           let uu____4050 =
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4057 =
                                         let uu____4062 =
                                           let uu____4063 =
                                             let uu____4068 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____4068.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____4063.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4062
                                          in
                                       match uu____4057 with
                                       | None  -> true
                                       | uu____4075 -> false  in
                                     if should_log
                                     then
                                       let uu____4080 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____4081 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4080 uu____4081
                                     else ""))
                              in
                           FStar_All.pipe_right uu____4050
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____4049
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t  in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4105 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____4105 with
                              | (bs1,c1) ->
                                  let uu____4110 =
                                    FStar_Syntax_Util.is_total_comp c1  in
                                  if uu____4110
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4120 =
                                            let uu____4121 =
                                              FStar_Syntax_Subst.compress t'
                                               in
                                            uu____4121.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____4120 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4140 =
                                                 let uu____4141 =
                                                   FStar_Syntax_Subst.compress
                                                     h
                                                    in
                                                 uu____4141.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____4140 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4151 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4151
                                                       in
                                                    let uu____4152 =
                                                      let uu____4153 =
                                                        let uu____4154 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u'
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4154 args
                                                         in
                                                      uu____4153 None
                                                        t'.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4152 u
                                                | uu____4159 -> c1)
                                           | uu____4160 -> c1)
                                      | uu____4161 -> c1  in
                                    let uu___116_4162 = t1  in
                                    let uu____4163 =
                                      let uu____4164 =
                                        let uu____4172 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c'
                                           in
                                        (bs1, uu____4172)  in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4164
                                       in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4163;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___116_4162.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___116_4162.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___116_4162.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4194 =
                               let uu____4195 = FStar_Syntax_Subst.compress h
                                  in
                               uu____4195.FStar_Syntax_Syntax.n  in
                             (match uu____4194 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4205 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None
                                       in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4205
                                     in
                                  let uu____4206 =
                                    let uu____4207 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u'
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4207
                                      args
                                     in
                                  uu____4206 None t1.FStar_Syntax_Syntax.pos
                              | uu____4212 -> t1)
                         | uu____4213 -> t1  in
                       let reified_tactic_decl assm_lid lb =
                         let t =
                           reified_tactic_type assm_lid
                             lb.FStar_Syntax_Syntax.lbtyp
                            in
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
                         }  in
                       let reflected_tactic_decl b lb bs assm_lid comp =
                         let reified_tac =
                           let uu____4240 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4240
                            in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4249 =
                                  FStar_Syntax_Syntax.bv_to_name (fst x)  in
                                (uu____4249, (snd x))) bs
                            in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Syntax_Const.tac_effect_lid)) None
                             FStar_Range.dummyRange
                            in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             None FStar_Range.dummyRange
                            in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, None)] None FStar_Range.dummyRange
                            in
                         let unit_binder =
                           let uu____4281 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4281
                            in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp))
                            in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp))
                            in
                         let uu___117_4286 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___118_4292 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___118_4292.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___118_4292.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___118_4292.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___118_4292.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_4286.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_4286.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_4286.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___117_4286.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       let tactic_decls =
                         match snd lbs1 with
                         | hd1::[] ->
                             let uu____4302 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp
                                in
                             (match uu____4302 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp
                                     in
                                  let uu____4322 =
                                    let uu____4323 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____4323.FStar_Syntax_Syntax.n  in
                                  (match uu____4322 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h
                                          in
                                       let tac_lid =
                                         let uu____4347 =
                                           let uu____4352 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname
                                              in
                                           uu____4352.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____4347.FStar_Syntax_Syntax.v  in
                                       let assm_lid =
                                         let uu____4357 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                            in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4357
                                          in
                                       let uu____4358 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____4359 =
                                              let uu____4360 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4360
                                               in
                                            Prims.op_Negation uu____4359)
                                          in
                                       if uu____4358
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1
                                            in
                                         let se_refl =
                                           reflected_tactic_decl (fst lbs1)
                                             hd1 bs assm_lid comp
                                            in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4383 -> None))
                         | uu____4386 -> None  in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4399 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics")
                                in
                             if uu____4399
                             then
                               let uu____4400 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm
                                  in
                               let uu____4401 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl
                                  in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4400 uu____4401
                             else ());
                            ([se_assm; se_refl], []))
                       | None  -> ([se1], []))))))

let for_export :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___88_4434  ->
                match uu___88_4434 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4435 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4441) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4445 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4450 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4453 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4466 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4479) ->
          let uu____4484 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____4484
          then
            let for_export_bundle se1 uu____4503 =
              match uu____4503 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4526,uu____4527) ->
                       let dec =
                         let uu___119_4533 = se1  in
                         let uu____4534 =
                           let uu____4535 =
                             let uu____4539 =
                               let uu____4542 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____4542  in
                             (l, us, uu____4539)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4535  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4534;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___119_4533.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___119_4533.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___119_4533.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4552,uu____4553,uu____4554) ->
                       let dec =
                         let uu___120_4558 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___120_4558.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___120_4558.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___120_4558.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____4561 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4573,uu____4574) ->
          let uu____4575 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____4575 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4588 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____4588
          then
            ([(let uu___121_4596 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___121_4596.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___121_4596.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___121_4596.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____4598 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___89_4600  ->
                       match uu___89_4600 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4601 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4604 -> true
                       | uu____4605 -> false))
                in
             if uu____4598 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4615 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4618 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4621 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4624 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4627 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4637) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____4651 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____4651
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
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____4674 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____4674
          then
            let uu____4679 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___122_4685 = se  in
                      let uu____4686 =
                        let uu____4687 =
                          let uu____4691 =
                            let uu____4692 =
                              let uu____4697 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____4697.FStar_Syntax_Syntax.fv_name  in
                            uu____4692.FStar_Syntax_Syntax.v  in
                          (uu____4691, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4687  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4686;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___122_4685.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___122_4685.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___122_4685.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____4679, hidden)
          else ([se], hidden)
  
let add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4717 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4726 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4735 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4738 = FStar_Options.using_facts_from ()  in
                 match uu____4738 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4750 =
                         let uu____4755 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns
                            in
                         FStar_List.append uu____4755 [([], false)]  in
                       [uu____4750]  in
                     let uu___123_4783 = env  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___123_4783.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___123_4783.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___123_4783.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___123_4783.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___123_4783.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___123_4783.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___123_4783.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___123_4783.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___123_4783.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___123_4783.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___123_4783.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___123_4783.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___123_4783.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___123_4783.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___123_4783.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___123_4783.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___123_4783.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___123_4783.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___123_4783.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___123_4783.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___123_4783.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___123_4783.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___123_4783.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___123_4783.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___123_4783.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___123_4783.FStar_TypeChecker_Env.is_native_tactic)
                     }
                 | None  -> env))
           | uu____4785 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4786 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____4792 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4792) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4793,uu____4794,uu____4795) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4797  ->
                  match uu___90_4797 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4798 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4799,uu____4800) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4804  ->
                  match uu___90_4804 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4805 -> false))
          -> env
      | uu____4806 -> FStar_TypeChecker_Env.push_sigelt env se
  
let tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4844 se =
        match uu____4844 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4874 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____4874
              then
                let uu____4875 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4875
              else ());
             (let uu____4877 = tc_decl env1 se  in
              match uu____4877 with
              | (ses',ses_elaborated) ->
                  let env2 =
                    FStar_All.pipe_right ses'
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1)
                     in
                  ((let uu____4903 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes"))
                       in
                    if uu____4903
                    then
                      let uu____4904 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4907 =
                                 let uu____4908 =
                                   FStar_Syntax_Print.sigelt_to_string se1
                                    in
                                 Prims.strcat uu____4908 "\n"  in
                               Prims.strcat s uu____4907) "" ses'
                         in
                      FStar_Util.print1 "Checked: %s\n" uu____4904
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4912 =
                      let accum_exports_hidden uu____4930 se1 =
                        match uu____4930 with
                        | (exports1,hidden1) ->
                            let uu____4946 = for_export hidden1 se1  in
                            (match uu____4946 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2))
                         in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'
                       in
                    match uu____4912 with
                    | (exports1,hidden1) ->
                        let ses'1 =
                          FStar_List.map
                            (fun s  ->
                               let uu___124_4988 = s  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (uu___124_4988.FStar_Syntax_Syntax.sigel);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___124_4988.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___124_4988.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___124_4988.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (se.FStar_Syntax_Syntax.sigattrs)
                               }) ses'
                           in
                        (((FStar_List.rev_append ses'1 ses1), exports1, env2,
                           hidden1), ses_elaborated)))))
         in
      let uu____5000 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses  in
      match uu____5000 with
      | (ses1,exports,env1,uu____5026) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let action = if verify then "Verifying" else "Lax-checking"  in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation"  in
      (let uu____5053 = FStar_Options.debug_any ()  in
       if uu____5053
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
          in
       let msg = Prims.strcat "Internals for " name  in
       let env1 =
         let uu___125_5059 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___125_5059.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___125_5059.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___125_5059.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___125_5059.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___125_5059.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___125_5059.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___125_5059.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___125_5059.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___125_5059.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___125_5059.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___125_5059.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___125_5059.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___125_5059.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___125_5059.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___125_5059.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___125_5059.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___125_5059.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___125_5059.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___125_5059.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___125_5059.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___125_5059.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___125_5059.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___125_5059.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___125_5059.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___125_5059.FStar_TypeChecker_Env.is_native_tactic)
         }  in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name
           in
        let uu____5062 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
           in
        match uu____5062 with
        | (ses,exports,env3) ->
            ((let uu___126_5080 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___126_5080.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___126_5080.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___126_5080.FStar_Syntax_Syntax.is_interface)
              }), exports, env3)))
  
let tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____5099 = tc_decls env decls  in
        match uu____5099 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___127_5117 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___127_5117.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___127_5117.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___127_5117.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___128_5134 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___128_5134.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___128_5134.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___128_5134.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___128_5134.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___128_5134.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___128_5134.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___128_5134.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___128_5134.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___128_5134.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___128_5134.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___128_5134.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___128_5134.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___128_5134.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___128_5134.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___128_5134.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___128_5134.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___128_5134.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___128_5134.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___128_5134.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___128_5134.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___128_5134.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___128_5134.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___128_5134.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___128_5134.FStar_TypeChecker_Env.is_native_tactic)
          }  in
        let check_term lid univs1 t =
          let uu____5145 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____5145 with
          | (univs2,t1) ->
              ((let uu____5151 =
                  let uu____5152 =
                    let uu____5155 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____5155  in
                  FStar_All.pipe_left uu____5152
                    (FStar_Options.Other "Exports")
                   in
                if uu____5151
                then
                  let uu____5156 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____5157 =
                    let uu____5158 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____5158
                      (FStar_String.concat ", ")
                     in
                  let uu____5163 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5156 uu____5157 uu____5163
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____5166 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____5166 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____5184 =
             let uu____5185 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____5186 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5185 uu____5186
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5184);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5193) ->
              let uu____5198 =
                let uu____5199 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____5199  in
              if uu____5198
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5207,uu____5208) ->
              let t =
                let uu____5216 =
                  let uu____5219 =
                    let uu____5220 =
                      let uu____5228 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____5228)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____5220  in
                  FStar_Syntax_Syntax.mk uu____5219  in
                uu____5216 None se.FStar_Syntax_Syntax.sigrng  in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5240,uu____5241,uu____5242) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5248 =
                let uu____5249 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____5249  in
              if uu____5248 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____5252,lbs),uu____5254) ->
              let uu____5262 =
                let uu____5263 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____5263  in
              if uu____5262
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags) ->
              let uu____5280 =
                let uu____5281 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____5281  in
              if uu____5280
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____5295 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5296 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5299 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5300 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5301 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5302 -> ()  in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
  
let finish_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul1 =
          let uu___129_5319 = modul  in
          {
            FStar_Syntax_Syntax.name =
              (uu___129_5319.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___129_5319.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          }  in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1  in
        (let uu____5322 =
           let uu____5323 = FStar_Options.lax ()  in
           Prims.op_Negation uu____5323  in
         if uu____5322 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5329 =
           let uu____5330 = FStar_Options.interactive ()  in
           Prims.op_Negation uu____5330  in
         if uu____5329
         then
           let uu____5331 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_right uu____5331 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
  
let tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5343 = tc_partial_modul env modul  in
      match uu____5343 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
  
let check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5366 = FStar_Options.debug_any ()  in
       if uu____5366
       then
         let uu____5367 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5367
       else ());
      (let env1 =
         let uu___130_5371 = env  in
         let uu____5372 =
           let uu____5373 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____5373  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___130_5371.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___130_5371.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___130_5371.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___130_5371.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___130_5371.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___130_5371.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___130_5371.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___130_5371.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___130_5371.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___130_5371.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___130_5371.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___130_5371.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___130_5371.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___130_5371.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___130_5371.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___130_5371.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___130_5371.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___130_5371.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5372;
           FStar_TypeChecker_Env.lax_universes =
             (uu___130_5371.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___130_5371.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___130_5371.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___130_5371.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___130_5371.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___130_5371.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___130_5371.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___130_5371.FStar_TypeChecker_Env.is_native_tactic)
         }  in
       let uu____5374 = tc_modul env1 m  in
       match uu____5374 with
       | (m1,env2) ->
           ((let uu____5382 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____5382
             then
               let uu____5383 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "%s\n" uu____5383
             else ());
            (let uu____5386 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____5386
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
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                        in
                     let update lb =
                       let uu____5410 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____5410 with
                       | (univnames1,e) ->
                           let uu___131_5415 = lb  in
                           let uu____5416 =
                             let uu____5419 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____5419 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___131_5415.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___131_5415.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___131_5415.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___131_5415.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5416
                           }
                        in
                     let uu___132_5420 = se  in
                     let uu____5421 =
                       let uu____5422 =
                         let uu____5426 =
                           let uu____5430 = FStar_List.map update lbs  in
                           (b, uu____5430)  in
                         (uu____5426, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____5422  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5421;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___132_5420.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___132_5420.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___132_5420.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___132_5420.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____5437 -> se  in
               let normalized_module =
                 let uu___133_5439 = m1  in
                 let uu____5440 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___133_5439.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5440;
                   FStar_Syntax_Syntax.exports =
                     (uu___133_5439.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___133_5439.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____5441 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____5441
             else ());
            (m1, env2)))
  