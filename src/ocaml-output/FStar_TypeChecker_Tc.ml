open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for ()  in
      match uu____7 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____12 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____12 l  in
          let uu___61_13 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___61_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___61_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___61_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___61_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___61_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___61_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___61_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___61_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___61_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___61_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___61_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___61_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___61_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___61_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___61_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___61_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___61_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___61_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___61_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___61_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___61_13.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___61_13.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___61_13.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___61_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___61_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___61_13.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___61_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___61_13.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___61_13.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___61_13.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___61_13.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___61_13.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___61_13.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___61_13.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____22 = FStar_TypeChecker_Env.current_module env  in
                let uu____23 =
                  let uu____24 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____24 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____22 uu____23
            | l::uu____26 -> l  in
          let uu___62_29 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___62_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___62_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___62_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___62_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___62_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___62_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___62_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___62_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___62_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___62_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___62_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___62_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___62_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___62_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___62_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___62_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___62_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___62_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___62_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___62_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___62_29.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___62_29.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___62_29.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___62_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___62_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___62_29.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___62_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___62_29.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___62_29.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___62_29.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___62_29.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___62_29.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___62_29.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___62_29.FStar_TypeChecker_Env.dep_graph)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____38 =
         let uu____39 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____39  in
       Prims.op_Negation uu____38)
  
let get_tactic_fv :
  'Auu____44 .
    'Auu____44 ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____60) ->
            let uu____65 =
              let uu____66 = FStar_Syntax_Subst.compress h'  in
              uu____66.FStar_Syntax_Syntax.n  in
            (match uu____65 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> FStar_Pervasives_Native.Some fv
             | uu____72 -> FStar_Pervasives_Native.None)
        | uu____73 -> FStar_Pervasives_Native.None
  
let (user_tactics_modules : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____115 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____115 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____136 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____136
         then
           let uu____137 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____137
         else ());
        (let uu____139 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____139 with
         | (t',uu____147,uu____148) ->
             ((let uu____150 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____150
               then
                 let uu____151 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____151
               else ());
              t))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____162 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____162
  
let check_nogen :
  'Auu____167 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____167 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____187 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1
           in
        ([], uu____187)
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____214 =
          let uu____215 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          FStar_Errors.raise_error uu____215 (FStar_Ident.range_of_lid m)  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____259)::(wp,uu____261)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____276 -> fail ())
        | uu____277 -> fail ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____284 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____284 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____310 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____310 t  in
          let open_univs_binders n_binders bs =
            let uu____320 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____320 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____328 =
            let uu____335 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____336 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____335 uu____336  in
          (match uu____328 with
           | (effect_params_un,signature_un,opening) ->
               let uu____346 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
                  in
               (match uu____346 with
                | (effect_params,env,uu____355) ->
                    let uu____356 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                       in
                    (match uu____356 with
                     | (signature,uu____362) ->
                         let ed1 =
                           let uu___63_364 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___63_364.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___63_364.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___63_364.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___63_364.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___63_364.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___63_364.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___63_364.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___63_364.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___63_364.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___63_364.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___63_364.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___63_364.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___63_364.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___63_364.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___63_364.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___63_364.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___63_364.FStar_Syntax_Syntax.actions)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____380 ->
                               let op uu____402 =
                                 match uu____402 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____422 =
                                       let uu____423 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____432 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____423
                                         uu____432
                                        in
                                     (us, uu____422)
                                  in
                               let uu___64_441 = ed1  in
                               let uu____442 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____443 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____444 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____445 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____446 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____447 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____448 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____449 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____450 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____451 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____452 =
                                 let uu____453 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____453  in
                               let uu____464 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____465 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____466 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___65_474 = a  in
                                      let uu____475 =
                                        let uu____476 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____476
                                         in
                                      let uu____487 =
                                        let uu____488 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____488
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___65_474.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___65_474.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___65_474.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___65_474.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____475;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____487
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___64_441.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___64_441.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___64_441.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___64_441.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____442;
                                 FStar_Syntax_Syntax.bind_wp = uu____443;
                                 FStar_Syntax_Syntax.if_then_else = uu____444;
                                 FStar_Syntax_Syntax.ite_wp = uu____445;
                                 FStar_Syntax_Syntax.stronger = uu____446;
                                 FStar_Syntax_Syntax.close_wp = uu____447;
                                 FStar_Syntax_Syntax.assert_p = uu____448;
                                 FStar_Syntax_Syntax.assume_p = uu____449;
                                 FStar_Syntax_Syntax.null_wp = uu____450;
                                 FStar_Syntax_Syntax.trivial = uu____451;
                                 FStar_Syntax_Syntax.repr = uu____452;
                                 FStar_Syntax_Syntax.return_repr = uu____464;
                                 FStar_Syntax_Syntax.bind_repr = uu____465;
                                 FStar_Syntax_Syntax.actions = uu____466
                               }
                            in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____525 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t
                                in
                             FStar_Errors.raise_error uu____525
                               (FStar_Ident.range_of_lid mname)
                              in
                           let uu____536 =
                             let uu____537 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____537.FStar_Syntax_Syntax.n  in
                           match uu____536 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____572)::(wp,uu____574)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____589 -> fail signature1)
                           | uu____590 -> fail signature1  in
                         let uu____591 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____591 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____613 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____620 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un
                                       in
                                    (match uu____620 with
                                     | (signature1,uu____632) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____633 ->
                                    let uu____636 =
                                      let uu____641 =
                                        let uu____642 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____642)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____641
                                       in
                                    (match uu____636 with
                                     | (uu____651,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env1 =
                                let uu____654 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env uu____654
                                 in
                              ((let uu____656 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____656
                                then
                                  let uu____657 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____658 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____659 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____660 =
                                    let uu____661 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____661
                                     in
                                  let uu____662 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____657 uu____658 uu____659 uu____660
                                    uu____662
                                else ());
                               (let check_and_gen' env2 uu____678 k =
                                  match uu____678 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____692::uu____693 ->
                                           let uu____696 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____696 with
                                            | (us1,t1) ->
                                                let uu____705 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____705 with
                                                 | (us2,t2) ->
                                                     let uu____712 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k
                                                        in
                                                     let uu____713 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____713))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____718 =
                                      let uu____725 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____726 =
                                        let uu____729 =
                                          let uu____730 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____730
                                           in
                                        [uu____729]  in
                                      uu____725 :: uu____726  in
                                    let uu____731 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____718
                                      uu____731
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____735 = fresh_effect_signature ()
                                     in
                                  match uu____735 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____751 =
                                          let uu____758 =
                                            let uu____759 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____759
                                             in
                                          [uu____758]  in
                                        let uu____760 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____751
                                          uu____760
                                         in
                                      let expected_k =
                                        let uu____766 =
                                          let uu____773 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____774 =
                                            let uu____777 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____778 =
                                              let uu____781 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____782 =
                                                let uu____785 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____786 =
                                                  let uu____789 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____789]  in
                                                uu____785 :: uu____786  in
                                              uu____781 :: uu____782  in
                                            uu____777 :: uu____778  in
                                          uu____773 :: uu____774  in
                                        let uu____790 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____766
                                          uu____790
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____795 =
                                      let uu____796 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____796
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____795
                                     in
                                  let expected_k =
                                    let uu____808 =
                                      let uu____815 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____816 =
                                        let uu____819 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____820 =
                                          let uu____823 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____824 =
                                            let uu____827 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____827]  in
                                          uu____823 :: uu____824  in
                                        uu____819 :: uu____820  in
                                      uu____815 :: uu____816  in
                                    let uu____828 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____808
                                      uu____828
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____835 =
                                      let uu____842 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____843 =
                                        let uu____846 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____846]  in
                                      uu____842 :: uu____843  in
                                    let uu____847 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____835
                                      uu____847
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____851 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____851 with
                                  | (t,uu____857) ->
                                      let expected_k =
                                        let uu____861 =
                                          let uu____868 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____869 =
                                            let uu____872 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____873 =
                                              let uu____876 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____876]  in
                                            uu____872 :: uu____873  in
                                          uu____868 :: uu____869  in
                                        let uu____877 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____861
                                          uu____877
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____882 =
                                      let uu____883 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____883
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____882
                                     in
                                  let b_wp_a =
                                    let uu____895 =
                                      let uu____902 =
                                        let uu____903 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____903
                                         in
                                      [uu____902]  in
                                    let uu____904 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____895
                                      uu____904
                                     in
                                  let expected_k =
                                    let uu____910 =
                                      let uu____917 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____918 =
                                        let uu____921 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____922 =
                                          let uu____925 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____925]  in
                                        uu____921 :: uu____922  in
                                      uu____917 :: uu____918  in
                                    let uu____926 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____910
                                      uu____926
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____933 =
                                      let uu____940 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____941 =
                                        let uu____944 =
                                          let uu____945 =
                                            let uu____946 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____946
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____945
                                           in
                                        let uu____955 =
                                          let uu____958 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____958]  in
                                        uu____944 :: uu____955  in
                                      uu____940 :: uu____941  in
                                    let uu____959 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____933
                                      uu____959
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____966 =
                                      let uu____973 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____974 =
                                        let uu____977 =
                                          let uu____978 =
                                            let uu____979 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____979
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____978
                                           in
                                        let uu____988 =
                                          let uu____991 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____991]  in
                                        uu____977 :: uu____988  in
                                      uu____973 :: uu____974  in
                                    let uu____992 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____966
                                      uu____992
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____999 =
                                      let uu____1006 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1006]  in
                                    let uu____1007 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____999
                                      uu____1007
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1011 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1011 with
                                  | (t,uu____1017) ->
                                      let expected_k =
                                        let uu____1021 =
                                          let uu____1028 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1029 =
                                            let uu____1032 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1032]  in
                                          uu____1028 :: uu____1029  in
                                        let uu____1033 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1021
                                          uu____1033
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1036 =
                                  let uu____1047 =
                                    let uu____1048 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1048.FStar_Syntax_Syntax.n  in
                                  match uu____1047 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1063 ->
                                      let repr =
                                        let uu____1065 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1065 with
                                        | (t,uu____1071) ->
                                            let expected_k =
                                              let uu____1075 =
                                                let uu____1082 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1083 =
                                                  let uu____1086 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1086]  in
                                                uu____1082 :: uu____1083  in
                                              let uu____1087 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1075 uu____1087
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
                                        let uu____1100 =
                                          let uu____1103 =
                                            let uu____1104 =
                                              let uu____1119 =
                                                let uu____1122 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1123 =
                                                  let uu____1126 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1126]  in
                                                uu____1122 :: uu____1123  in
                                              (repr1, uu____1119)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1104
                                             in
                                          FStar_Syntax_Syntax.mk uu____1103
                                           in
                                        uu____1100
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1141 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1141 wp  in
                                      let destruct_repr t =
                                        let uu____1154 =
                                          let uu____1155 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1155.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1154 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1166,(t1,uu____1168)::
                                             (wp,uu____1170)::[])
                                            -> (t1, wp)
                                        | uu____1213 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1224 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1224
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1225 =
                                          fresh_effect_signature ()  in
                                        match uu____1225 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1241 =
                                                let uu____1248 =
                                                  let uu____1249 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1249
                                                   in
                                                [uu____1248]  in
                                              let uu____1250 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1241 uu____1250
                                               in
                                            let wp_f =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_f"
                                                FStar_Pervasives_Native.None
                                                wp_a
                                               in
                                            let wp_g =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_g"
                                                FStar_Pervasives_Native.None
                                                a_wp_b
                                               in
                                            let x_a =
                                              let uu____1256 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1256
                                               in
                                            let wp_g_x =
                                              let uu____1260 =
                                                let uu____1261 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1262 =
                                                  let uu____1263 =
                                                    let uu____1264 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1264
                                                     in
                                                  [uu____1263]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1261 uu____1262
                                                 in
                                              uu____1260
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1273 =
                                                  let uu____1274 =
                                                    let uu____1275 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1275
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1284 =
                                                    let uu____1285 =
                                                      let uu____1288 =
                                                        let uu____1291 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1292 =
                                                          let uu____1295 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1296 =
                                                            let uu____1299 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1300 =
                                                              let uu____1303
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1303]
                                                               in
                                                            uu____1299 ::
                                                              uu____1300
                                                             in
                                                          uu____1295 ::
                                                            uu____1296
                                                           in
                                                        uu____1291 ::
                                                          uu____1292
                                                         in
                                                      r :: uu____1288  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1285
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1274 uu____1284
                                                   in
                                                uu____1273
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let expected_k =
                                              let uu____1309 =
                                                let uu____1316 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1317 =
                                                  let uu____1320 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____1321 =
                                                    let uu____1324 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1325 =
                                                      let uu____1328 =
                                                        let uu____1329 =
                                                          let uu____1330 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1330
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1329
                                                         in
                                                      let uu____1331 =
                                                        let uu____1334 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1335 =
                                                          let uu____1338 =
                                                            let uu____1339 =
                                                              let uu____1340
                                                                =
                                                                let uu____1347
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1347]
                                                                 in
                                                              let uu____1348
                                                                =
                                                                let uu____1351
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1351
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1340
                                                                uu____1348
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1339
                                                             in
                                                          [uu____1338]  in
                                                        uu____1334 ::
                                                          uu____1335
                                                         in
                                                      uu____1328 ::
                                                        uu____1331
                                                       in
                                                    uu____1324 :: uu____1325
                                                     in
                                                  uu____1320 :: uu____1321
                                                   in
                                                uu____1316 :: uu____1317  in
                                              let uu____1352 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1309 uu____1352
                                               in
                                            let uu____1355 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k
                                               in
                                            (match uu____1355 with
                                             | (expected_k1,uu____1363,uu____1364)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env3 =
                                                   let uu___66_1369 = env2
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qname_and_index
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.qname_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___66_1369.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1379 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1379
                                           in
                                        let res =
                                          let wp =
                                            let uu____1386 =
                                              let uu____1387 =
                                                let uu____1388 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1388
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1397 =
                                                let uu____1398 =
                                                  let uu____1401 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1402 =
                                                    let uu____1405 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1405]  in
                                                  uu____1401 :: uu____1402
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1398
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1387 uu____1397
                                               in
                                            uu____1386
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1411 =
                                            let uu____1418 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1419 =
                                              let uu____1422 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1422]  in
                                            uu____1418 :: uu____1419  in
                                          let uu____1423 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1411
                                            uu____1423
                                           in
                                        let uu____1426 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k
                                           in
                                        match uu____1426 with
                                        | (expected_k1,uu____1440,uu____1441)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1445 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1445 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1466 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let act_typ =
                                            let uu____1494 =
                                              let uu____1495 =
                                                FStar_Syntax_Subst.compress
                                                  act.FStar_Syntax_Syntax.action_typ
                                                 in
                                              uu____1495.FStar_Syntax_Syntax.n
                                               in
                                            match uu____1494 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) ->
                                                let c1 =
                                                  FStar_Syntax_Util.comp_to_comp_typ
                                                    c
                                                   in
                                                if
                                                  FStar_Ident.lid_equals
                                                    c1.FStar_Syntax_Syntax.effect_name
                                                    ed2.FStar_Syntax_Syntax.mname
                                                then
                                                  let uu____1521 =
                                                    let uu____1524 =
                                                      let uu____1525 =
                                                        let uu____1526 =
                                                          FStar_List.hd
                                                            c1.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        FStar_Pervasives_Native.fst
                                                          uu____1526
                                                         in
                                                      mk_repr'
                                                        c1.FStar_Syntax_Syntax.result_typ
                                                        uu____1525
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total
                                                      uu____1524
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____1521
                                                else
                                                  act.FStar_Syntax_Syntax.action_typ
                                            | uu____1542 ->
                                                act.FStar_Syntax_Syntax.action_typ
                                             in
                                          let uu____1543 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1 act_typ
                                             in
                                          match uu____1543 with
                                          | (act_typ1,uu____1551,g_t) ->
                                              let env' =
                                                let uu___67_1554 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ1
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___67_1554.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___67_1554.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1556 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1556
                                                then
                                                  let uu____1557 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn
                                                     in
                                                  let uu____1558 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ1
                                                     in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1557 uu____1558
                                                else ());
                                               (let uu____1560 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn
                                                   in
                                                match uu____1560 with
                                                | (act_defn,uu____1568,g_a)
                                                    ->
                                                    let act_defn1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant]
                                                        env1 act_defn
                                                       in
                                                    let act_typ2 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant;
                                                        FStar_TypeChecker_Normalize.Eager_unfolding;
                                                        FStar_TypeChecker_Normalize.Beta]
                                                        env1 act_typ1
                                                       in
                                                    let uu____1572 =
                                                      let act_typ3 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ2
                                                         in
                                                      match act_typ3.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1600 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c
                                                             in
                                                          (match uu____1600
                                                           with
                                                           | (bs1,uu____1610)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let k =
                                                                 let uu____1617
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1617
                                                                  in
                                                               let uu____1620
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k
                                                                  in
                                                               (match uu____1620
                                                                with
                                                                | (k1,uu____1632,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1634 ->
                                                          let uu____1635 =
                                                            let uu____1640 =
                                                              let uu____1641
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ3
                                                                 in
                                                              let uu____1642
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ3
                                                                 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1641
                                                                uu____1642
                                                               in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1640)
                                                             in
                                                          FStar_Errors.raise_error
                                                            uu____1635
                                                            act_defn1.FStar_Syntax_Syntax.pos
                                                       in
                                                    (match uu____1572 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ2
                                                             expected_k
                                                            in
                                                         ((let uu____1651 =
                                                             let uu____1652 =
                                                               let uu____1653
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1653
                                                                in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1652
                                                              in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1651);
                                                          (let act_typ3 =
                                                             let uu____1657 =
                                                               let uu____1658
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1658.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1657
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1681
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1681
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1690
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1690
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1712
                                                                    =
                                                                    let uu____1713
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1713]
                                                                     in
                                                                    let uu____1714
                                                                    =
                                                                    let uu____1723
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1723]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1712;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1714;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1724
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1724))
                                                             | uu____1727 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1730 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1
                                                              in
                                                           match uu____1730
                                                           with
                                                           | (univs1,act_defn2)
                                                               ->
                                                               let act_typ4 =
                                                                 FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Normalize.Beta]
                                                                   env1
                                                                   act_typ3
                                                                  in
                                                               let act_typ5 =
                                                                 FStar_Syntax_Subst.close_univ_vars
                                                                   univs1
                                                                   act_typ4
                                                                  in
                                                               let uu___68_1739
                                                                 = act  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___68_1739.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___68_1739.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___68_1739.FStar_Syntax_Syntax.action_params);
                                                                 FStar_Syntax_Syntax.action_defn
                                                                   =
                                                                   act_defn2;
                                                                 FStar_Syntax_Syntax.action_typ
                                                                   = act_typ5
                                                               })))))
                                           in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action)
                                         in
                                      (repr, bind_repr, return_repr, actions)
                                   in
                                match uu____1036 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1763 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1763
                                       in
                                    let uu____1766 =
                                      let uu____1773 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1773 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1794 ->
                                               let uu____1797 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           (FStar_Syntax_Syntax.order_univ_name
                                                              u1 u2)
                                                             =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____1797
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1811 =
                                                    let uu____1816 =
                                                      let uu____1817 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1818 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1817 uu____1818
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1816)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1811
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1766 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1832 =
                                             let uu____1837 =
                                               let uu____1838 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1838.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1837)  in
                                           match uu____1832 with
                                           | ([],uu____1841) -> t
                                           | (uu____1852,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1853,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1871 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1884 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1884
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1889 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1891 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1891))
                                                && (m <> n1)
                                               in
                                            if uu____1889
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____1907 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____1914 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____1915 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1907 uu____1914
                                                  uu____1915
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____1923 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____1923 with
                                           | (univs2,defn) ->
                                               let uu____1930 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____1930 with
                                                | (univs',typ) ->
                                                    let uu___69_1940 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___69_1940.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___69_1940.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___69_1940.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___70_1945 = ed2  in
                                           let uu____1946 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____1947 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____1948 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____1949 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____1950 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____1951 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____1952 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____1953 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____1954 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____1955 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____1956 =
                                             let uu____1957 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____1957
                                              in
                                           let uu____1968 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____1969 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____1970 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___70_1945.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___70_1945.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____1946;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____1947;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____1948;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____1949;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____1950;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____1951;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____1952;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____1953;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____1954;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____1955;
                                             FStar_Syntax_Syntax.repr =
                                               uu____1956;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____1968;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____1969;
                                             FStar_Syntax_Syntax.actions =
                                               uu____1970
                                           }  in
                                         ((let uu____1974 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____1974
                                           then
                                             let uu____1975 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____1975
                                           else ());
                                          ed3))))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ed  ->
      let uu____1993 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____1993 with
      | (effect_binders_un,signature_un) ->
          let uu____2010 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2010 with
           | (effect_binders,env1,uu____2029) ->
               let uu____2030 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2030 with
                | (signature,uu____2046) ->
                    let raise_error1 a uu____2057 =
                      match uu____2057 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2083  ->
                           match uu____2083 with
                           | (bv,qual) ->
                               let uu____2094 =
                                 let uu___71_2095 = bv  in
                                 let uu____2096 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___71_2095.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___71_2095.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2096
                                 }  in
                               (uu____2094, qual)) effect_binders
                       in
                    let uu____2099 =
                      let uu____2106 =
                        let uu____2107 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2107.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2106 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2117)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2139 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2099 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2157 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2157
                           then
                             let uu____2158 =
                               let uu____2161 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2161  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2158
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2195 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2195 with
                           | (t2,comp,uu____2208) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2215 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2215 with
                          | (repr,_comp) ->
                              ((let uu____2237 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2237
                                then
                                  let uu____2238 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2238
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange)
                                   in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr
                                   in
                                let wp_type1 = recheck_debug "*" env1 wp_type
                                   in
                                let wp_a =
                                  let uu____2244 =
                                    let uu____2245 =
                                      let uu____2246 =
                                        let uu____2261 =
                                          let uu____2268 =
                                            let uu____2273 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2274 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2273, uu____2274)  in
                                          [uu____2268]  in
                                        (wp_type1, uu____2261)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2246
                                       in
                                    mk1 uu____2245  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2244
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2299 =
                                      let uu____2304 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2304)  in
                                    let uu____2305 =
                                      let uu____2312 =
                                        let uu____2313 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2313
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2312]  in
                                    uu____2299 :: uu____2305  in
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
                                  let uu____2376 = item  in
                                  match uu____2376 with
                                  | (u_item,item1) ->
                                      let uu____2397 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2397 with
                                       | (item2,item_comp) ->
                                           ((let uu____2413 =
                                               let uu____2414 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2414
                                                in
                                             if uu____2413
                                             then
                                               let uu____2415 =
                                                 let uu____2420 =
                                                   let uu____2421 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2422 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2421 uu____2422
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2420)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2415
                                             else ());
                                            (let uu____2424 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2424 with
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
                                let uu____2444 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2444 with
                                | (dmff_env1,uu____2468,bind_wp,bind_elab) ->
                                    let uu____2471 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2471 with
                                     | (dmff_env2,uu____2495,return_wp,return_elab)
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
                                           }  in
                                         let lift_from_pure_wp =
                                           let uu____2502 =
                                             let uu____2503 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2503.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2502 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2547 =
                                                       let uu____2562 =
                                                         let uu____2567 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2567
                                                          in
                                                       match uu____2562 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2631 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2547 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2670 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2670
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2687 =
                                                               let uu____2688
                                                                 =
                                                                 let uu____2703
                                                                   =
                                                                   let uu____2710
                                                                    =
                                                                    let uu____2715
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2716
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2715,
                                                                    uu____2716)
                                                                     in
                                                                   [uu____2710]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2703)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2688
                                                                in
                                                             mk1 uu____2687
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2731 =
                                                           let uu____2740 =
                                                             let uu____2741 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2741
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2740
                                                            in
                                                         (match uu____2731
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a415 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2760
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2762
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2762
                                                                    (match what'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                                    error_msg)))
                                                                  a415
                                                                 in
                                                              ((match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ()
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    (
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                    then
                                                                    fail ()
                                                                    else ();
                                                                    (
                                                                    let uu____2768
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
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ())
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2768
                                                                    FStar_Pervasives.ignore)));
                                                               (let wp =
                                                                  let t2 =
                                                                    (FStar_Pervasives_Native.fst
                                                                    b21).FStar_Syntax_Syntax.sort
                                                                     in
                                                                  let pure_wp_type
                                                                    =
                                                                    FStar_TypeChecker_DMFF.double_star
                                                                    t2  in
                                                                  FStar_Syntax_Syntax.gen_bv
                                                                    "wp"
                                                                    FStar_Pervasives_Native.None
                                                                    pure_wp_type
                                                                   in
                                                                let body3 =
                                                                  let uu____2795
                                                                    =
                                                                    let uu____2796
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2797
                                                                    =
                                                                    let uu____2798
                                                                    =
                                                                    let uu____2805
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2805,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2798]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2796
                                                                    uu____2797
                                                                     in
                                                                  uu____2795
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2830
                                                                  =
                                                                  let uu____2831
                                                                    =
                                                                    let uu____2838
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2838]
                                                                     in
                                                                  b11 ::
                                                                    uu____2831
                                                                   in
                                                                let uu____2843
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2830
                                                                  uu____2843
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2844 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let return_wp1 =
                                           let uu____2846 =
                                             let uu____2847 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2847.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2846 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2891 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2891
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____2904 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let bind_wp1 =
                                           let uu____2906 =
                                             let uu____2907 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____2907.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2906 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (binders,body,what) ->
                                                  Obj.repr
                                                    (let r =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         FStar_Parser_Const.range_lid
                                                         (FStar_Syntax_Syntax.Delta_defined_at_level
                                                            (Prims.parse_int "1"))
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     let uu____2934 =
                                                       let uu____2935 =
                                                         let uu____2938 =
                                                           let uu____2939 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____2939
                                                            in
                                                         [uu____2938]  in
                                                       FStar_List.append
                                                         uu____2935 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____2934 body what)
                                              | uu____2940 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedBindShape,
                                                         "unexpected shape for bind")))
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2958 =
                                                let uu____2959 =
                                                  let uu____2960 =
                                                    let uu____2975 =
                                                      let uu____2976 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2976
                                                       in
                                                    (t, uu____2975)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2960
                                                   in
                                                mk1 uu____2959  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2958)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3006 = f a2  in
                                               [uu____3006]
                                           | x::xs ->
                                               let uu____3011 =
                                                 apply_last1 f xs  in
                                               x :: uu____3011
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
                                           let uu____3031 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3031 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3061 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3061
                                                 then
                                                   let uu____3062 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3062
                                                 else ());
                                                (let uu____3064 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3064))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3073 =
                                                 let uu____3078 = mk_lid name
                                                    in
                                                 let uu____3079 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3078 uu____3079
                                                  in
                                               (match uu____3073 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3083 =
                                                        let uu____3086 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3086
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3083);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         (FStar_Options.push ();
                                          (let uu____3183 =
                                             let uu____3186 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3187 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3186 :: uu____3187  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3183);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3285 =
                                               let uu____3288 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3289 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3288 :: uu____3289  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3285);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3384 =
                                                FStar_List.fold_left
                                                  (fun uu____3424  ->
                                                     fun action  ->
                                                       match uu____3424 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3445 =
                                                             let uu____3452 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3452
                                                               params_un
                                                              in
                                                           (match uu____3445
                                                            with
                                                            | (action_params,env',uu____3461)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3481
                                                                     ->
                                                                    match uu____3481
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3492
                                                                    =
                                                                    let uu___72_3493
                                                                    = bv  in
                                                                    let uu____3494
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___72_3493.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___72_3493.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3494
                                                                    }  in
                                                                    (uu____3492,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3498
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3498
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
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____3528
                                                                    ->
                                                                    let uu____3529
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3529
                                                                     in
                                                                    ((
                                                                    let uu____3533
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3533
                                                                    then
                                                                    let uu____3534
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3535
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3536
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3537
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3534
                                                                    uu____3535
                                                                    uu____3536
                                                                    uu____3537
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
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3544
                                                                    =
                                                                    let uu___73_3545
                                                                    = action
                                                                     in
                                                                    let uu____3546
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3547
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___73_3545.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___73_3545.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___73_3545.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3546;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3547
                                                                    }  in
                                                                    uu____3544
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3541))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3384 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a
                                                       in
                                                    let binders =
                                                      let uu____3580 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3581 =
                                                        let uu____3584 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3584]  in
                                                      uu____3580 ::
                                                        uu____3581
                                                       in
                                                    let uu____3585 =
                                                      let uu____3586 =
                                                        let uu____3587 =
                                                          let uu____3588 =
                                                            let uu____3603 =
                                                              let uu____3610
                                                                =
                                                                let uu____3615
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3616
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3615,
                                                                  uu____3616)
                                                                 in
                                                              [uu____3610]
                                                               in
                                                            (repr,
                                                              uu____3603)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3588
                                                           in
                                                        mk1 uu____3587  in
                                                      let uu____3631 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3586
                                                        uu____3631
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3585
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3634 =
                                                    let uu____3641 =
                                                      let uu____3642 =
                                                        let uu____3645 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3645
                                                         in
                                                      uu____3642.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3641 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3655)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3684
                                                                =
                                                                let uu____3701
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3701
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3759
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3684
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3809
                                                                    =
                                                                    let uu____3810
                                                                    =
                                                                    let uu____3813
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3813
                                                                     in
                                                                    uu____3810.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3809
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3838
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3838
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3851
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3876
                                                                     ->
                                                                    match uu____3876
                                                                    with
                                                                    | 
                                                                    (bv,uu____3882)
                                                                    ->
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3884
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3884
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3883
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3851
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
                                                                    let uu____3948
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3948
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3953
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3961
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____3966
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____3969
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____3966,
                                                                    uu____3969)))
                                                                    | 
                                                                    uu____3976
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3977
                                                                    =
                                                                    let uu____3982
                                                                    =
                                                                    let uu____3983
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3983
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3982)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____3977)))
                                                       | uu____3984 ->
                                                           Obj.repr
                                                             (let uu____3985
                                                                =
                                                                let uu____3990
                                                                  =
                                                                  let uu____3991
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____3991
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____3990)
                                                                 in
                                                              raise_error1 ()
                                                                uu____3985))
                                                     in
                                                  (match uu____3634 with
                                                   | (pre,post) ->
                                                       ((let uu____4009 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4011 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4013 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___74_4015 =
                                                             ed  in
                                                           let uu____4016 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4017 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____4018 =
                                                             let uu____4019 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4019)
                                                              in
                                                           let uu____4026 =
                                                             let uu____4027 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4027)
                                                              in
                                                           let uu____4034 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____4035 =
                                                             let uu____4036 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4036)
                                                              in
                                                           let uu____4043 =
                                                             let uu____4044 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4044)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4016;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4017;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4018;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4026;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___74_4015.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4034;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4035;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4043;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____4051 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4051
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4069
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4069
                                                               then
                                                                 let uu____4070
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4070
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
                                                                    let uu____4082
                                                                    =
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4094
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4094)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4085
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____4082;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4109
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4109
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4111
                                                                 =
                                                                 let uu____4114
                                                                   =
                                                                   let uu____4117
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4117
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4114
                                                                   sigelts'
                                                                  in
                                                               (uu____4111,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4174 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4174 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4207 = FStar_List.hd ses  in
            uu____4207.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4212 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4216,[],t,uu____4218,uu____4219);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4221;
               FStar_Syntax_Syntax.sigattrs = uu____4222;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4224,_t_top,_lex_t_top,_0_40,uu____4227);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4229;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4230;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4232,_t_cons,_lex_t_cons,_0_41,uu____4235);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4237;
                 FStar_Syntax_Syntax.sigattrs = uu____4238;_}::[]
               when
               ((_0_40 = (Prims.parse_int "0")) &&
                  (_0_41 = (Prims.parse_int "0")))
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
                   (FStar_Pervasives_Native.Some r)
                  in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
                   FStar_Pervasives_Native.None r
                  in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1  in
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
                 }  in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1)
                  in
               let lex_top_t =
                 let uu____4297 =
                   let uu____4300 =
                     let uu____4301 =
                       let uu____4308 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4308, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4301  in
                   FStar_Syntax_Syntax.mk uu____4300  in
                 uu____4297 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
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
                 }  in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let lex_cons_t =
                 let a =
                   let uu____4326 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4326
                    in
                 let hd1 =
                   let uu____4328 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4328
                    in
                 let tl1 =
                   let uu____4330 =
                     let uu____4331 =
                       let uu____4334 =
                         let uu____4335 =
                           let uu____4342 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4342, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4335  in
                       FStar_Syntax_Syntax.mk uu____4334  in
                     uu____4331 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4330
                    in
                 let res =
                   let uu____4351 =
                     let uu____4354 =
                       let uu____4355 =
                         let uu____4362 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4362,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4355  in
                     FStar_Syntax_Syntax.mk uu____4354  in
                   uu____4351 FStar_Pervasives_Native.None r2  in
                 let uu____4368 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4368
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
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let uu____4407 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4407;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4412 ->
               let err_msg =
                 let uu____4416 =
                   let uu____4417 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4417  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4416
                  in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.formula ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun lid  ->
      fun phi  ->
        fun quals  ->
          fun r  ->
            let env1 = FStar_TypeChecker_Env.set_range env r  in
            let uu____4442 = FStar_Syntax_Util.type_u ()  in
            match uu____4442 with
            | (k,uu____4448) ->
                let phi1 =
                  let uu____4450 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____4450
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4452 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1  in
                  match uu____4452 with
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
  
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive"  in
          let uu____4494 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4494 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4527 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas
                   in
                FStar_All.pipe_right uu____4527 FStar_List.flatten  in
              ((let uu____4541 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____4541
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle  in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env2
                           in
                        if Prims.op_Negation b
                        then
                          let uu____4552 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4562,uu____4563,uu____4564,uu____4565,uu____4566)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4575 -> failwith "Impossible!"  in
                          match uu____4552 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4586 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4590,uu____4591,uu____4592,uu____4593,uu____4594)
                        -> lid
                    | uu____4603 -> failwith "Impossible"  in
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
                let res =
                  let uu____4621 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4621
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
                           sig_bndle tcs datas env1 tc_assume
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume
                        in
                     let uu____4644 =
                       let uu____4647 =
                         let uu____4648 =
                           FStar_TypeChecker_Env.get_range env1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4648;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       uu____4647 :: ses1  in
                     (uu____4644, data_ops_ses))
                   in
                (let uu____4658 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4692 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4717 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids
              in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____4769 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4769 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4807 = cps_and_elaborate env1 ne  in
           (match uu____4807 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___75_4844 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___75_4844.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___75_4844.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___75_4844.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___75_4844.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___76_4846 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___76_4846.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___76_4846.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___76_4846.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___76_4846.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___77_4854 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___77_4854.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___77_4854.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___77_4854.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___77_4854.FStar_Syntax_Syntax.sigattrs)
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
           let uu____4862 =
             let uu____4869 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4869
              in
           (match uu____4862 with
            | (a,wp_a_src) ->
                let uu____4884 =
                  let uu____4891 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4891
                   in
                (match uu____4884 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4907 =
                         let uu____4910 =
                           let uu____4911 =
                             let uu____4918 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____4918)  in
                           FStar_Syntax_Syntax.NT uu____4911  in
                         [uu____4910]  in
                       FStar_Syntax_Subst.subst uu____4907 wp_b_tgt  in
                     let expected_k =
                       let uu____4922 =
                         let uu____4929 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____4930 =
                           let uu____4933 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____4933]  in
                         uu____4929 :: uu____4930  in
                       let uu____4934 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____4922 uu____4934  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4955 =
                           let uu____4960 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____4960)
                            in
                         let uu____4961 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____4955 uu____4961  in
                       let uu____4964 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____4964 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____4996 =
                             let uu____4997 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____4997  in
                           if uu____4996
                           then no_reify eff_name
                           else
                             (let uu____5003 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____5004 =
                                let uu____5007 =
                                  let uu____5008 =
                                    let uu____5023 =
                                      let uu____5026 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____5027 =
                                        let uu____5030 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____5030]  in
                                      uu____5026 :: uu____5027  in
                                    (repr, uu____5023)  in
                                  FStar_Syntax_Syntax.Tm_app uu____5008  in
                                FStar_Syntax_Syntax.mk uu____5007  in
                              uu____5004 FStar_Pervasives_Native.None
                                uu____5003)
                        in
                     let uu____5036 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let lift_wp1 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5089 =
                                 let uu____5092 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 FStar_Pervasives_Native.fst uu____5092  in
                               FStar_Syntax_Subst.subst uu____5089 lift_wp
                             else lift_wp  in
                           let uu____5106 =
                             check_and_gen env1 lift_wp1 expected_k  in
                           (lift, uu____5106)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let lift1 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5132 =
                                 let uu____5135 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 FStar_Pervasives_Native.fst uu____5135  in
                               FStar_Syntax_Subst.subst uu____5132 lift
                             else lift  in
                           ((let uu____5150 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5150
                             then
                               let uu____5151 =
                                 FStar_Syntax_Print.term_to_string lift1  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5151
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5154 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift1
                                in
                             match uu____5154 with
                             | (lift2,comp,uu____5169) ->
                                 let uu____5170 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift2
                                    in
                                 (match uu____5170 with
                                  | (uu____5183,lift_wp,lift_elab) ->
                                      let uu____5186 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5187 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____5036 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___78_5228 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___78_5228.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___78_5228.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___78_5228.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___78_5228.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___78_5228.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___78_5228.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___78_5228.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___78_5228.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___78_5228.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___78_5228.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___78_5228.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___78_5228.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___78_5228.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___78_5228.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___78_5228.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___78_5228.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___78_5228.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___78_5228.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___78_5228.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___78_5228.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___78_5228.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___78_5228.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___78_5228.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___78_5228.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___78_5228.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___78_5228.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___78_5228.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___78_5228.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___78_5228.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___78_5228.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___78_5228.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___78_5228.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___78_5228.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___78_5228.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5234,lift1)
                                ->
                                let uu____5246 =
                                  let uu____5253 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5253
                                   in
                                (match uu____5246 with
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv
                                         FStar_Pervasives_Native.None
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
                                           env2
                                           (FStar_Pervasives_Native.snd
                                              lift_wp)
                                          in
                                       let lift_wp_a =
                                         let uu____5277 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5278 =
                                           let uu____5281 =
                                             let uu____5282 =
                                               let uu____5297 =
                                                 let uu____5300 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5301 =
                                                   let uu____5304 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5304]  in
                                                 uu____5300 :: uu____5301  in
                                               (lift_wp1, uu____5297)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5282
                                              in
                                           FStar_Syntax_Syntax.mk uu____5281
                                            in
                                         uu____5278
                                           FStar_Pervasives_Native.None
                                           uu____5277
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5313 =
                                         let uu____5320 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5321 =
                                           let uu____5324 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5325 =
                                             let uu____5328 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5328]  in
                                           uu____5324 :: uu____5325  in
                                         uu____5320 :: uu____5321  in
                                       let uu____5329 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5313
                                         uu____5329
                                        in
                                     let uu____5332 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5332 with
                                      | (expected_k2,uu____5342,uu____5343)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift2))
                             in
                          let sub2 =
                            let uu___79_5346 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___79_5346.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___79_5346.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___80_5348 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___80_5348.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___80_5348.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___80_5348.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___80_5348.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let uu____5363 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (uvs, tps, c)
             else
               (let uu____5377 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____5377 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____5404 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____5404 c  in
                    (uvs1, tps1, c1))
              in
           (match uu____5363 with
            | (uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____5425 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____5425 with
                 | (tps2,c2) ->
                     let uu____5440 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____5440 with
                      | (tps3,env3,us) ->
                          let uu____5458 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____5458 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____5479 =
                                   let uu____5480 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____5480
                                    in
                                 match uu____5479 with
                                 | (uvs2,t) ->
                                     let uu____5495 =
                                       let uu____5508 =
                                         let uu____5513 =
                                           let uu____5514 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____5514.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____5513)  in
                                       match uu____5508 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____5529,c5)) -> ([], c5)
                                       | (uu____5569,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____5596 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____5495 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____5640 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____5640 with
                                              | (uu____5645,t1) ->
                                                  let uu____5647 =
                                                    let uu____5652 =
                                                      let uu____5653 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____5654 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____5655 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____5653 uu____5654
                                                        uu____5655
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____5652)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5647 r)
                                           else ();
                                           (let se1 =
                                              let uu___81_5658 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___81_5658.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___81_5658.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___81_5658.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___81_5658.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5675,uu____5676,uu____5677) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5681  ->
                   match uu___56_5681 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5682 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5687,uu____5688) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5696  ->
                   match uu___56_5696 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5697 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5707 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5707
             then
               let uu____5708 =
                 let uu____5713 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid)
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5713)
                  in
               FStar_Errors.raise_error uu____5708 r
             else ());
            (let uu____5715 =
               if uvs = []
               then
                 let uu____5716 =
                   let uu____5717 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____5717  in
                 check_and_gen env2 t uu____5716
               else
                 (let uu____5723 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____5723 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5731 =
                          let uu____5732 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____5732  in
                        tc_check_trivial_guard env2 t1 uu____5731  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____5738 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____5738))
                in
             match uu____5715 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___82_5754 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___82_5754.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___82_5754.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___82_5754.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___82_5754.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5764 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____5764 with
            | (uu____5777,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r
                   in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit
              in
           let uu____5787 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____5787 with
            | (e1,c,g1) ->
                let uu____5805 =
                  let uu____5812 =
                    let uu____5815 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____5815  in
                  let uu____5816 =
                    let uu____5821 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____5821)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5812 uu____5816
                   in
                (match uu____5805 with
                 | (e2,uu____5831,g) ->
                     ((let uu____5834 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5834);
                      (let se1 =
                         let uu___83_5836 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___83_5836.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___83_5836.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___83_5836.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___83_5836.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5887 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____5887
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5895 =
                      let uu____5900 =
                        let uu____5901 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____5902 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____5903 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____5901 uu____5902 uu____5903
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____5900)
                       in
                    FStar_Errors.raise_error uu____5895 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____5929 =
                   let uu____5930 = FStar_Syntax_Subst.compress def  in
                   uu____5930.FStar_Syntax_Syntax.n  in
                 match uu____5929 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5940,uu____5941)
                     -> binders
                 | uu____5962 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5972;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6050) -> val_bs1
                     | (uu____6073,[]) -> val_bs1
                     | ((body_bv,uu____6097)::bt,(val_bv,aqual)::vt) ->
                         let uu____6134 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6150) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___84_6152 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___85_6155 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___85_6155.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___84_6152.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___84_6152.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6134
                      in
                   let uu____6156 =
                     let uu____6159 =
                       let uu____6160 =
                         let uu____6173 = rename_binders1 def_bs val_bs  in
                         (uu____6173, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6160  in
                     FStar_Syntax_Syntax.mk uu____6159  in
                   uu____6156 FStar_Pervasives_Native.None r1
               | uu____6191 -> typ1  in
             let uu___86_6192 = lb  in
             let uu____6193 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___86_6192.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___86_6192.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6193;
               FStar_Syntax_Syntax.lbeff =
                 (uu___86_6192.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___86_6192.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___86_6192.FStar_Syntax_Syntax.lbattrs)
             }  in
           let uu____6196 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6247  ->
                     fun lb  ->
                       match uu____6247 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6289 =
                             let uu____6300 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6300 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals
                                    in
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____6385 ->
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_ascribed
                                            ((lb.FStar_Syntax_Syntax.lbdef),
                                              ((FStar_Util.Inl
                                                  (lb.FStar_Syntax_Syntax.lbtyp)),
                                                FStar_Pervasives_Native.None),
                                              FStar_Pervasives_Native.None))
                                         FStar_Pervasives_Native.None
                                         (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos
                                    in
                                 (if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ();
                                  (let uu____6428 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def)
                                      in
                                   (false, uu____6428, quals_opt1)))
                              in
                           (match uu____6289 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6196 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6522 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___57_6526  ->
                                match uu___57_6526 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6527 -> false))
                         in
                      if uu____6522
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6537 =
                    let uu____6540 =
                      let uu____6541 =
                        let uu____6554 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6554)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6541  in
                    FStar_Syntax_Syntax.mk uu____6540  in
                  uu____6537 FStar_Pervasives_Native.None r  in
                let uu____6572 =
                  let uu____6583 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___87_6592 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___87_6592.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___87_6592.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___87_6592.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___87_6592.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___87_6592.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___87_6592.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___87_6592.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___87_6592.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___87_6592.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___87_6592.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___87_6592.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___87_6592.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___87_6592.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___87_6592.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___87_6592.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___87_6592.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___87_6592.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___87_6592.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___87_6592.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___87_6592.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___87_6592.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___87_6592.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___87_6592.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___87_6592.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___87_6592.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___87_6592.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___87_6592.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___87_6592.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___87_6592.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___87_6592.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___87_6592.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___87_6592.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___87_6592.FStar_TypeChecker_Env.dep_graph)
                       }) e
                     in
                  match uu____6583 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6605;
                       FStar_Syntax_Syntax.vars = uu____6606;_},uu____6607,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6636 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6636)  in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6654,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6659 -> quals  in
                      ((let uu___88_6667 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___88_6667.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___88_6667.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___88_6667.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6676 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6572 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6725 = log env2  in
                       if uu____6725
                       then
                         let uu____6726 =
                           let uu____6727 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6742 =
                                         let uu____6751 =
                                           let uu____6752 =
                                             let uu____6755 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____6755.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____6752.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6751
                                          in
                                       match uu____6742 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6762 -> false  in
                                     if should_log
                                     then
                                       let uu____6771 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____6772 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6771 uu____6772
                                     else ""))
                              in
                           FStar_All.pipe_right uu____6727
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____6726
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t  in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6803 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____6803 with
                              | (bs1,c1) ->
                                  let uu____6810 =
                                    FStar_Syntax_Util.is_total_comp c1  in
                                  if uu____6810
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6822 =
                                            let uu____6823 =
                                              FStar_Syntax_Subst.compress t'
                                               in
                                            uu____6823.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6822 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6848 =
                                                 let uu____6849 =
                                                   FStar_Syntax_Subst.compress
                                                     h
                                                    in
                                                 uu____6849.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6848 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6859 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6859
                                                       in
                                                    let uu____6860 =
                                                      let uu____6861 =
                                                        let uu____6862 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u'
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6862 args
                                                         in
                                                      uu____6861
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6860 u
                                                | uu____6865 -> c1)
                                           | uu____6866 -> c1)
                                      | uu____6867 -> c1  in
                                    let uu___89_6868 = t1  in
                                    let uu____6869 =
                                      let uu____6870 =
                                        let uu____6883 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c'
                                           in
                                        (bs1, uu____6883)  in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6870
                                       in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6869;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___89_6868.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___89_6868.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6907 =
                               let uu____6908 = FStar_Syntax_Subst.compress h
                                  in
                               uu____6908.FStar_Syntax_Syntax.n  in
                             (match uu____6907 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6918 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6918
                                     in
                                  let uu____6919 =
                                    let uu____6920 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u'
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6920
                                      args
                                     in
                                  uu____6919 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6923 -> t1)
                         | uu____6924 -> t1  in
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
                           let uu____6952 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6952
                            in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6969 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x)
                                   in
                                (uu____6969, (FStar_Pervasives_Native.snd x)))
                             bs
                            in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Parser_Const.tac_effect_lid))
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, FStar_Pervasives_Native.None)]
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let unit_binder =
                           let uu____7000 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____7000
                            in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp))
                            in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp))
                            in
                         let uu___90_7007 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___91_7019 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___91_7019.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___91_7019.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___91_7019.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___91_7019.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___91_7019.FStar_Syntax_Syntax.lbattrs)
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___90_7007.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___90_7007.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___90_7007.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___90_7007.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____7036 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp
                                in
                             (match uu____7036 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp
                                     in
                                  let uu____7070 =
                                    let uu____7071 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____7071.FStar_Syntax_Syntax.n  in
                                  (match uu____7070 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h
                                          in
                                       let tac_lid =
                                         let uu____7104 =
                                           let uu____7107 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname
                                              in
                                           uu____7107.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____7104.FStar_Syntax_Syntax.v  in
                                       let assm_lid =
                                         let uu____7109 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                            in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____7109
                                          in
                                       let uu____7110 =
                                         get_tactic_fv env2 assm_lid h1  in
                                       (match uu____7110 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7120 =
                                              let uu____7121 =
                                                let uu____7122 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7122
                                                 in
                                              Prims.op_Negation uu____7121
                                               in
                                            if uu____7120
                                            then
                                              ((let uu____7152 =
                                                  let uu____7153 =
                                                    FStar_Syntax_Util.is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule
                                                     in
                                                  Prims.op_Negation
                                                    uu____7153
                                                   in
                                                if uu____7152
                                                then
                                                  let added_modules =
                                                    FStar_ST.op_Bang
                                                      user_tactics_modules
                                                     in
                                                  let module_name =
                                                    FStar_Ident.ml_path_of_lid
                                                      env2.FStar_TypeChecker_Env.curmodule
                                                     in
                                                  (if
                                                     Prims.op_Negation
                                                       (FStar_List.contains
                                                          module_name
                                                          added_modules)
                                                   then
                                                     FStar_ST.op_Colon_Equals
                                                       user_tactics_modules
                                                       (FStar_List.append
                                                          added_modules
                                                          [module_name])
                                                   else ())
                                                else ());
                                               (let uu____7206 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid
                                                   in
                                                if uu____7206
                                                then
                                                  let se_assm =
                                                    reified_tactic_decl
                                                      assm_lid hd1
                                                     in
                                                  let se_refl =
                                                    reflected_tactic_decl
                                                      (FStar_Pervasives_Native.fst
                                                         lbs1) hd1 bs
                                                      assm_lid comp
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    (se_assm, se_refl)
                                                else
                                                  FStar_Pervasives_Native.None))
                                            else FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7235 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7240 -> FStar_Pervasives_Native.None  in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7262 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics")
                                in
                             if uu____7262
                             then
                               let uu____7263 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm
                                  in
                               let uu____7264 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl
                                  in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7263 uu____7264
                             else ());
                            ([se_assm; se_refl], []))
                       | FStar_Pervasives_Native.None  -> ([se1], []))))))
  
let (for_export :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___58_7315  ->
                match uu___58_7315 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7316 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7322) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7328 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7337 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7342 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7367 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7391) ->
          let uu____7400 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7400
          then
            let for_export_bundle se1 uu____7431 =
              match uu____7431 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7470,uu____7471) ->
                       let dec =
                         let uu___92_7481 = se1  in
                         let uu____7482 =
                           let uu____7483 =
                             let uu____7490 =
                               let uu____7493 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7493  in
                             (l, us, uu____7490)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7483  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7482;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_7481.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_7481.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_7481.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7505,uu____7506,uu____7507) ->
                       let dec =
                         let uu___93_7513 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___93_7513.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___93_7513.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___93_7513.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7518 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7540,uu____7541,uu____7542) ->
          let uu____7543 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7543 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7564 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7564
          then
            ([(let uu___94_7580 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___94_7580.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___94_7580.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___94_7580.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7582 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___59_7586  ->
                       match uu___59_7586 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7587 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7592 -> true
                       | uu____7593 -> false))
                in
             if uu____7582 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7611 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7616 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7621 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7626 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7631 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7649) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7666 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7666
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
          let uu____7697 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7697
          then
            let uu____7706 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___95_7719 = se  in
                      let uu____7720 =
                        let uu____7721 =
                          let uu____7728 =
                            let uu____7729 =
                              let uu____7732 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7732.FStar_Syntax_Syntax.fv_name  in
                            uu____7729.FStar_Syntax_Syntax.v  in
                          (uu____7728, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7721  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7720;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___95_7719.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___95_7719.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___95_7719.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7706, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7752 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7769 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7784) ->
          let env1 =
            let uu____7788 = FStar_Options.using_facts_from ()  in
            FStar_TypeChecker_Env.set_proof_ns uu____7788 env  in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7790 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7791 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7801 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7801) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7802,uu____7803,uu____7804) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7808  ->
                  match uu___60_7808 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7809 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7810,uu____7811) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7819  ->
                  match uu___60_7819 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7820 -> false))
          -> env
      | uu____7821 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (dont_use_exports : Prims.bool) =
  (FStar_Options.use_extracted_interfaces ()) ||
    (FStar_Options.check_interface ())
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7881 se =
        match uu____7881 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7934 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7934
              then
                let uu____7935 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7935
              else ());
             (let uu____7937 = tc_decl env1 se  in
              match uu____7937 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7987 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____7987
                             then
                               let uu____7988 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7988
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1))
                     in
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
                              fun se1  -> add_sigelt_to_env env2 se1) env1)
                       in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____8011 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____8011
                     then
                       let uu____8012 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____8018 =
                                  let uu____8019 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____8019 "\n"  in
                                Prims.strcat s uu____8018) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____8012
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____8024 =
                       if dont_use_exports
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____8067 se1 =
                            match uu____8067 with
                            | (exports1,hidden1) ->
                                let uu____8095 = for_export hidden1 se1  in
                                (match uu____8095 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____8024 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___96_8174 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___96_8174.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___96_8174.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___96_8174.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___96_8174.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____8252 = acc  in
        match uu____8252 with
        | (uu____8287,uu____8288,env1,uu____8290) ->
            let uu____8303 =
              FStar_Util.record_time
                (fun uu____8349  -> process_one_decl acc se)
               in
            (match uu____8303 with
             | (r,ms_elapsed) ->
                 ((let uu____8413 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8413
                   then
                     let uu____8414 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8415 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8414 uu____8415
                   else ());
                  r))
         in
      let uu____8417 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8417 with
      | (ses1,exports,env1,uu____8465) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun modul  ->
      fun push_before_typechecking  ->
        let verify =
          FStar_Options.should_verify
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        let action = if verify then "Verifying" else "Lax-checking"  in
        let label1 =
          if modul.FStar_Syntax_Syntax.is_interface
          then "interface"
          else "implementation"  in
        (let uu____8505 = FStar_Options.debug_any ()  in
         if uu____8505
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
           let uu___97_8511 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___97_8511.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___97_8511.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___97_8511.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___97_8511.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___97_8511.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___97_8511.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___97_8511.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___97_8511.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___97_8511.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___97_8511.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___97_8511.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___97_8511.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___97_8511.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___97_8511.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___97_8511.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___97_8511.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___97_8511.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___97_8511.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___97_8511.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___97_8511.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___97_8511.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___97_8511.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___97_8511.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___97_8511.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___97_8511.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___97_8511.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___97_8511.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___97_8511.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___97_8511.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___97_8511.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___97_8511.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___97_8511.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___97_8511.FStar_TypeChecker_Env.dep_graph)
           }  in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name
             in
          let uu____8515 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations  in
          match uu____8515 with
          | (ses,exports,env3) ->
              ((let uu___98_8548 = modul  in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___98_8548.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___98_8548.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___98_8548.FStar_Syntax_Syntax.is_interface)
                }), exports, env3)))
  
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____8570 = tc_decls env decls  in
        match uu____8570 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___99_8601 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___99_8601.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___99_8601.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___99_8601.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___100_8618 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___100_8618.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___100_8618.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___100_8618.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___100_8618.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___100_8618.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___100_8618.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___100_8618.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___100_8618.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___100_8618.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___100_8618.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___100_8618.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___100_8618.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___100_8618.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___100_8618.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___100_8618.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___100_8618.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___100_8618.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___100_8618.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___100_8618.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___100_8618.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___100_8618.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___100_8618.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___100_8618.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___100_8618.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___100_8618.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___100_8618.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___100_8618.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___100_8618.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___100_8618.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___100_8618.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___100_8618.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___100_8618.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8629 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8629 with
          | (univs2,t1) ->
              ((let uu____8637 =
                  let uu____8638 =
                    let uu____8641 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8641  in
                  FStar_All.pipe_left uu____8638
                    (FStar_Options.Other "Exports")
                   in
                if uu____8637
                then
                  let uu____8642 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8643 =
                    let uu____8644 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8644
                      (FStar_String.concat ", ")
                     in
                  let uu____8653 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8642 uu____8643 uu____8653
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____8656 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____8656 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____8680 =
             let uu____8681 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8682 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8681 uu____8682
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8680);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8689) ->
              let uu____8698 =
                let uu____8699 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8699  in
              if uu____8698
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8709,uu____8710) ->
              let t =
                let uu____8722 =
                  let uu____8725 =
                    let uu____8726 =
                      let uu____8739 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8739)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8726  in
                  FStar_Syntax_Syntax.mk uu____8725  in
                uu____8722 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8746,uu____8747,uu____8748) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8756 =
                let uu____8757 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8757  in
              if uu____8756 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8761,lbs),uu____8763) ->
              let uu____8778 =
                let uu____8779 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8779  in
              if uu____8778
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
              (l,univs1,binders,comp,flags1) ->
              let uu____8798 =
                let uu____8799 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8799  in
              if uu____8798
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8806 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8807 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8814 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8815 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8816 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8817 -> ()  in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
  
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract  in
      let is_irreducible1 =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible  in
      let is_assume = FStar_List.contains FStar_Syntax_Syntax.Assumption  in
      let is_noeq_or_unopteq =
        FStar_List.existsb
          (fun q  ->
             (q = FStar_Syntax_Syntax.Noeq) ||
               (q = FStar_Syntax_Syntax.Unopteq))
         in
      let filter_out_abstract =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((q = FStar_Syntax_Syntax.Abstract) ||
                   (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Noeq))
                    || (q = FStar_Syntax_Syntax.Unopteq))
                   || (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Irreducible))
                    || (q = FStar_Syntax_Syntax.Visible_default))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
         in
      let add_assume_if_needed quals =
        if is_assume quals
        then quals
        else FStar_Syntax_Syntax.Assumption :: quals  in
      let val_typs = FStar_Util.mk_ref []  in
      let abstract_inductive_tycons = FStar_Util.mk_ref []  in
      let abstract_inductive_datacons = FStar_Util.mk_ref []  in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q  ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l,uu____8939) -> true
             | uu____8940 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8959 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____8990 ->
                   let uu____8991 =
                     let uu____8994 =
                       let uu____8995 =
                         let uu____9008 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____9008)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____8995  in
                     FStar_Syntax_Syntax.mk uu____8994  in
                   uu____8991 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____9016,uu____9017) ->
            let s1 =
              let uu___101_9027 = s  in
              let uu____9028 =
                let uu____9029 =
                  let uu____9036 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____9036)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____9029  in
              let uu____9037 =
                let uu____9040 =
                  filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals
                   in
                FStar_Syntax_Syntax.Assumption :: uu____9040  in
              {
                FStar_Syntax_Syntax.sigel = uu____9028;
                FStar_Syntax_Syntax.sigrng =
                  (uu___101_9027.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____9037;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___101_9027.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___101_9027.FStar_Syntax_Syntax.sigattrs)
              }  in
            if false
            then
              let uu____9043 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9043 with
               | (usubst,uvs1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let uu____9063 =
                     FStar_TypeChecker_Util.get_optimized_haseq_axiom env1 s
                       usubst uvs1
                      in
                   (match uu____9063 with
                    | (axiom_lid,fml,uu____9076,uu____9077,uu____9078) ->
                        let uu____9079 =
                          FStar_TypeChecker_Util.generalize_universes env1
                            fml
                           in
                        (match uu____9079 with
                         | (uvs2,fml1) ->
                             let s2 =
                               let uu___102_9087 = s  in
                               let uu____9088 =
                                 let uu____9091 =
                                   filter_out_abstract
                                     s.FStar_Syntax_Syntax.sigquals
                                    in
                                 FStar_Syntax_Syntax.Assumption :: uu____9091
                                  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_assume
                                      (axiom_lid, uvs2, fml1));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___102_9087.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = uu____9088;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___102_9087.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___102_9087.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             [s1; s2])))
            else [s1]
        | uu____9097 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____9115 =
        match uu____9115 with
        | (uvs,c_or_t) ->
            let t =
              let uu____9137 = FStar_All.pipe_right c_or_t FStar_Util.is_left
                 in
              if uu____9137
              then
                let uu____9144 = FStar_All.pipe_right c_or_t FStar_Util.left
                   in
                FStar_All.pipe_right uu____9144 FStar_Syntax_Util.comp_result
              else FStar_All.pipe_right c_or_t FStar_Util.right  in
            let uu___103_9156 = s  in
            let uu____9157 =
              let uu____9160 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____9160  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___103_9156.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____9157;
              FStar_Syntax_Syntax.sigmeta =
                (uu___103_9156.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___103_9156.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let extract_lb_annotation lb lid r =
        (lb,
          (FStar_Pervasives_Native.Some
             ((lb.FStar_Syntax_Syntax.lbunivs),
               (FStar_Util.Inr (lb.FStar_Syntax_Syntax.lbtyp)))))
         in
      let should_keep_lbdef c_or_t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____9256 -> failwith "Impossible!"  in
        let c_opt =
          let uu____9260 = FStar_Util.is_left c_or_t  in
          if uu____9260
          then
            let uu____9263 = FStar_All.pipe_right c_or_t FStar_Util.left  in
            FStar_Pervasives_Native.Some uu____9263
          else
            (let t = FStar_All.pipe_right c_or_t FStar_Util.right  in
             let uu____9274 = FStar_Syntax_Util.is_unit t  in
             if uu____9274
             then
               let uu____9277 = FStar_Syntax_Syntax.mk_Total t  in
               FStar_Pervasives_Native.Some uu____9277
             else
               (let uu____9279 =
                  let uu____9280 = FStar_Syntax_Subst.compress t  in
                  uu____9280.FStar_Syntax_Syntax.n  in
                match uu____9279 with
                | FStar_Syntax_Syntax.Tm_arrow (uu____9285,c) ->
                    FStar_Pervasives_Native.Some c
                | uu____9305 -> FStar_Pervasives_Native.None))
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           ((FStar_Syntax_Util.is_pure_or_ghost_comp c) ||
              (let uu____9313 = comp_effect_name1 c  in
               FStar_TypeChecker_Util.is_reifiable env uu____9313))
             &&
             (let uu____9315 =
                let uu____9316 =
                  FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
                FStar_All.pipe_right uu____9316 FStar_Syntax_Util.is_unit  in
              Prims.op_Negation uu____9315))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____9331 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____9350 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9398,uu____9399,uu____9400,uu____9401,uu____9402)
                         ->
                         ((let uu____9412 =
                             let uu____9415 =
                               FStar_ST.op_Bang abstract_inductive_tycons  in
                             lid :: uu____9415  in
                           FStar_ST.op_Colon_Equals abstract_inductive_tycons
                             uu____9412);
                          (let uu____9508 = vals_of_abstract_inductive s1  in
                           FStar_List.append uu____9508 sigelts1))
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____9512,uu____9513,uu____9514,uu____9515,uu____9516)
                         ->
                         ((let uu____9522 =
                             let uu____9525 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____9525  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____9522);
                          sigelts1)
                     | uu____9618 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9625 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9625
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____9631 =
                   let uu___104_9632 = s  in
                   let uu____9633 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___104_9632.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___104_9632.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9633;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___104_9632.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___104_9632.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9631])
              else
                ((let uu____9638 =
                    let uu____9647 = FStar_ST.op_Bang val_typs  in
                    (lid, uvs, t) :: uu____9647  in
                  FStar_ST.op_Colon_Equals val_typs uu____9638);
                 [])
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____9782 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9782
            then []
            else
              (let uu____9786 = lbs  in
               match uu____9786 with
               | (flbs,slbs) ->
                   let uu____9795 =
                     FStar_List.fold_left2
                       (fun uu____9845  ->
                          fun lb  ->
                            fun lid  ->
                              match uu____9845 with
                              | (b,lbs1,typs) ->
                                  let uu____9919 =
                                    extract_lb_annotation lb lid
                                      s.FStar_Syntax_Syntax.sigrng
                                     in
                                  (match uu____9919 with
                                   | (lb1,t) ->
                                       (((FStar_Util.is_some t) && b), (lb1
                                         :: lbs1), (t :: typs))))
                       (true, [], []) slbs lids
                      in
                   (match uu____9795 with
                    | (b,lbs1,typs) ->
                        let uu____10065 =
                          ((FStar_List.rev_append lbs1 []),
                            (FStar_List.rev_append typs []))
                           in
                        (match uu____10065 with
                         | (lbs2,typs1) ->
                             let s1 =
                               let uu___105_10151 = s  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_let
                                      ((flbs, lbs2), lids));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___105_10151.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___105_10151.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___105_10151.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___105_10151.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             if Prims.op_Negation b
                             then
                               (if
                                  (is_abstract
                                     s1.FStar_Syntax_Syntax.sigquals)
                                    ||
                                    (is_irreducible1
                                       s1.FStar_Syntax_Syntax.sigquals)
                                then
                                  let uu____10166 =
                                    let uu____10171 =
                                      let uu____10172 =
                                        let uu____10173 = FStar_List.hd lids
                                           in
                                        uu____10173.FStar_Ident.str  in
                                      Prims.strcat
                                        "For extracting interfaces, abstract and irreducible defns must be annotated at the top-level: "
                                        uu____10172
                                       in
                                    (FStar_Errors.Fatal_IllTyped,
                                      uu____10171)
                                     in
                                  FStar_Errors.raise_error uu____10166
                                    s1.FStar_Syntax_Syntax.sigrng
                                else [s1])
                             else
                               (let is_lemma1 =
                                  FStar_List.existsML
                                    (fun opt  ->
                                       let uu____10204 =
                                         FStar_All.pipe_right opt
                                           FStar_Util.must
                                          in
                                       match uu____10204 with
                                       | (uu____10239,c_or_t) ->
                                           (FStar_Util.is_right c_or_t) &&
                                             (let uu____10250 =
                                                FStar_All.pipe_right c_or_t
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____10250
                                                FStar_Syntax_Util.is_lemma))
                                    typs1
                                   in
                                let vals =
                                  FStar_List.map2
                                    (fun lid  ->
                                       fun opt  ->
                                         let uu____10283 =
                                           FStar_All.pipe_right opt
                                             FStar_Util.must
                                            in
                                         val_of_lb s1 lid uu____10283) lids
                                    typs1
                                   in
                                if
                                  ((is_abstract
                                      s1.FStar_Syntax_Syntax.sigquals)
                                     ||
                                     (is_irreducible1
                                        s1.FStar_Syntax_Syntax.sigquals))
                                    || is_lemma1
                                then vals
                                else
                                  (let should_keep_defs =
                                     FStar_List.existsML
                                       (fun opt  ->
                                          let uu____10345 =
                                            let uu____10350 =
                                              FStar_All.pipe_right opt
                                                FStar_Util.must
                                               in
                                            FStar_All.pipe_right uu____10350
                                              FStar_Pervasives_Native.snd
                                             in
                                          should_keep_lbdef uu____10345)
                                       typs1
                                      in
                                   if should_keep_defs then [s1] else vals)))))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____10408,uu____10409) ->
            let is_haseq =
              let str = lid.FStar_Ident.str  in
              let len = FStar_String.length str  in
              (len > (Prims.parse_int "6")) &&
                (let uu____10420 =
                   let uu____10421 =
                     FStar_String.substring str (len - (Prims.parse_int "6"))
                       (Prims.parse_int "6")
                      in
                   FStar_String.compare uu____10421 "_haseq"  in
                 uu____10420 = (Prims.parse_int "0"))
               in
            let is_haseq_of_abstract_inductive =
              let uu____10429 = FStar_ST.op_Bang abstract_inductive_tycons
                 in
              FStar_List.existsML
                (fun l  ->
                   let uu____10480 =
                     FStar_Ident.lid_of_ids
                       (FStar_List.append l.FStar_Ident.ns
                          [FStar_Ident.id_of_text
                             (Prims.strcat
                                (l.FStar_Ident.ident).FStar_Ident.idText
                                "_haseq")])
                      in
                   FStar_Ident.lid_equals lid uu____10480) uu____10429
               in
            if is_haseq
            then
              (if is_haseq_of_abstract_inductive
               then
                 let uu____10485 =
                   let uu___106_10486 = s  in
                   let uu____10487 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___106_10486.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___106_10486.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____10487;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___106_10486.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___106_10486.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____10485]
               else [])
            else
              (let uu____10492 =
                 let uu___107_10493 = s  in
                 let uu____10494 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___107_10493.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___107_10493.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____10494;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___107_10493.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___107_10493.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____10492])
        | FStar_Syntax_Syntax.Sig_new_effect uu____10497 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10498 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____10499 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10500 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____10513 -> [s]  in
      let uu___108_10514 = m  in
      let uu____10515 =
        let uu____10516 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____10516  in
      {
        FStar_Syntax_Syntax.name = (uu___108_10514.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10515;
        FStar_Syntax_Syntax.exports =
          (uu___108_10514.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env0  ->
    fun m  ->
      let lax_mode = env0.FStar_TypeChecker_Env.lax  in
      let env01 =
        if
          FStar_Ident.lid_equals env0.FStar_TypeChecker_Env.curmodule
            FStar_Parser_Const.prims_lid
        then
          let uu___109_10567 = env0  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___109_10567.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___109_10567.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___109_10567.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___109_10567.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___109_10567.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___109_10567.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___109_10567.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___109_10567.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___109_10567.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___109_10567.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___109_10567.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___109_10567.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___109_10567.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___109_10567.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___109_10567.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___109_10567.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___109_10567.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___109_10567.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes =
              (uu___109_10567.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___109_10567.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___109_10567.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___109_10567.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___109_10567.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___109_10567.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___109_10567.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___109_10567.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___109_10567.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___109_10567.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___109_10567.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___109_10567.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___109_10567.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___109_10567.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___109_10567.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___109_10567.FStar_TypeChecker_Env.dep_graph)
          }
        else env0  in
      let env = FStar_TypeChecker_Env.mk_copy env01  in
      let uu____10570 = tc_partial_modul env m true  in
      match uu____10570 with
      | (modul,non_private_decls,env1) ->
          let uu____10594 =
            finish_partial_modul false env01 env1 modul non_private_decls  in
          (match uu____10594 with
           | (m1,m_opt,env2) ->
               (m1, m_opt,
                 (let uu___110_10621 = env2  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___110_10621.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___110_10621.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___110_10621.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___110_10621.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___110_10621.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___110_10621.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___110_10621.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___110_10621.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___110_10621.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___110_10621.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___110_10621.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___110_10621.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___110_10621.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___110_10621.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___110_10621.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___110_10621.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___110_10621.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___110_10621.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = lax_mode;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___110_10621.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___110_10621.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___110_10621.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___110_10621.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___110_10621.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___110_10621.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___110_10621.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___110_10621.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qname_and_index =
                      (uu___110_10621.FStar_TypeChecker_Env.qname_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___110_10621.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth =
                      (uu___110_10621.FStar_TypeChecker_Env.synth);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___110_10621.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___110_10621.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___110_10621.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___110_10621.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___110_10621.FStar_TypeChecker_Env.dep_graph)
                  })))

and (finish_partial_modul :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.modul ->
          FStar_Syntax_Syntax.sigelt Prims.list ->
            (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                         FStar_Pervasives_Native.option,
              FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun loading_from_cache  ->
    fun env0  ->
      fun en  ->
        fun m  ->
          fun exports  ->
            let uu____10637 =
              ((Prims.op_Negation loading_from_cache) &&
                 (FStar_Options.use_extracted_interfaces ()))
                && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
               in
            if uu____10637
            then
              ((en.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                 (Prims.strcat "Ending modul "
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str);
               (en.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____10649 =
                  let uu____10650 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____10650  in
                if uu____10649
                then
                  let uu____10651 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____10651 FStar_Pervasives.ignore
                else ());
               (let modul_iface = extract_interface env0 m  in
                (let uu____10655 =
                   let uu____10656 =
                     FStar_Options.dump_module
                       (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____10656
                   then
                     let uu____10657 = FStar_Syntax_Print.modul_to_string m
                        in
                     Prims.strcat "from: " uu____10657
                   else ""  in
                 let uu____10659 =
                   let uu____10660 =
                     FStar_Options.dump_module
                       (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____10660
                   then
                     let uu____10661 =
                       FStar_Syntax_Print.modul_to_string modul_iface  in
                     Prims.strcat "to: " uu____10661
                   else ""  in
                 FStar_Util.print3
                   "Extracting and type checking module %s interface\n%s\n%s\n"
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____10655
                   uu____10659);
                (let env01 =
                   let uu___111_10664 = env0  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___111_10664.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___111_10664.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___111_10664.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___111_10664.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___111_10664.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___111_10664.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___111_10664.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___111_10664.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___111_10664.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___111_10664.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___111_10664.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___111_10664.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___111_10664.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___111_10664.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___111_10664.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___111_10664.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface = true;
                     FStar_TypeChecker_Env.admit =
                       (uu___111_10664.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (uu___111_10664.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___111_10664.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.failhard =
                       (uu___111_10664.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___111_10664.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___111_10664.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___111_10664.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___111_10664.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___111_10664.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___111_10664.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qname_and_index =
                       (uu___111_10664.FStar_TypeChecker_Env.qname_and_index);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___111_10664.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth =
                       (uu___111_10664.FStar_TypeChecker_Env.synth);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___111_10664.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___111_10664.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___111_10664.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___111_10664.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.dep_graph =
                       (uu___111_10664.FStar_TypeChecker_Env.dep_graph)
                   }  in
                 let uu____10665 = tc_modul env01 modul_iface  in
                 match uu____10665 with
                 | (modul_iface1,must_be_none,env) ->
                     if must_be_none <> FStar_Pervasives_Native.None
                     then
                       failwith
                         "Impossible! Expected the second component to be None"
                     else
                       (m, (FStar_Pervasives_Native.Some modul_iface1), env))))
            else
              (let modul =
                 if dont_use_exports
                 then
                   let uu___112_10712 = m  in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___112_10712.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations =
                       (uu___112_10712.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.exports =
                       (m.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___112_10712.FStar_Syntax_Syntax.is_interface)
                   }
                 else
                   (let uu___113_10714 = m  in
                    {
                      FStar_Syntax_Syntax.name =
                        (uu___113_10714.FStar_Syntax_Syntax.name);
                      FStar_Syntax_Syntax.declarations =
                        (uu___113_10714.FStar_Syntax_Syntax.declarations);
                      FStar_Syntax_Syntax.exports = exports;
                      FStar_Syntax_Syntax.is_interface =
                        (uu___113_10714.FStar_Syntax_Syntax.is_interface)
                    })
                  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____10717 =
                  ((let uu____10720 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____10720) &&
                     (Prims.op_Negation dont_use_exports))
                    && (Prims.op_Negation loading_from_cache)
                   in
                if uu____10717 then check_exports env modul exports else ());
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                 (Prims.strcat "Ending modul "
                    (modul.FStar_Syntax_Syntax.name).FStar_Ident.str);
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____10726 =
                  let uu____10727 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____10727  in
                if uu____10726
                then
                  let uu____10728 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____10728 FStar_Pervasives.ignore
                else ());
               (modul, FStar_Pervasives_Native.None, env))

let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun en  ->
    fun m  ->
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m.FStar_Syntax_Syntax.name
         in
      (let uu____10740 =
         let uu____10741 =
           FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
         Prims.strcat "Internals for " uu____10741  in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
         uu____10740);
      (let env1 =
         FStar_List.fold_left
           (fun env1  ->
              fun se  ->
                let env2 = FStar_TypeChecker_Env.push_sigelt env1 se  in
                let lids = FStar_Syntax_Util.lids_of_sigelt se  in
                FStar_All.pipe_right lids
                  (FStar_List.iter
                     (fun lid  ->
                        let uu____10760 =
                          FStar_TypeChecker_Env.try_lookup_lid env2 lid  in
                        ()));
                env2) env m.FStar_Syntax_Syntax.declarations
          in
       let uu____10781 =
         finish_partial_modul true env1 env1 m m.FStar_Syntax_Syntax.exports
          in
       match uu____10781 with | (uu____10790,uu____10791,env2) -> env2)
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      (let uu____10812 = FStar_Options.debug_any ()  in
       if uu____10812
       then
         let uu____10813 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____10813
       else ());
      (let env1 =
         let uu___114_10817 = env  in
         let uu____10818 =
           let uu____10819 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____10819  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___114_10817.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___114_10817.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___114_10817.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___114_10817.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___114_10817.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___114_10817.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___114_10817.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___114_10817.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___114_10817.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___114_10817.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___114_10817.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___114_10817.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___114_10817.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___114_10817.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___114_10817.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___114_10817.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___114_10817.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___114_10817.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____10818;
           FStar_TypeChecker_Env.lax_universes =
             (uu___114_10817.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___114_10817.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___114_10817.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___114_10817.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___114_10817.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___114_10817.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___114_10817.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___114_10817.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___114_10817.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___114_10817.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___114_10817.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___114_10817.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___114_10817.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___114_10817.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___114_10817.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___114_10817.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____10820 = tc_modul env1 m  in
       match uu____10820 with
       | (m1,m_iface_opt,env2) ->
           ((let uu____10845 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____10845
             then
               let uu____10846 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____10846
             else ());
            (let uu____10849 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____10849
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
                       let uu____10880 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____10880 with
                       | (univnames1,e) ->
                           let uu___115_10887 = lb  in
                           let uu____10888 =
                             let uu____10891 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____10891 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___115_10887.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___115_10887.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___115_10887.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___115_10887.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____10888;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___115_10887.FStar_Syntax_Syntax.lbattrs)
                           }
                        in
                     let uu___116_10892 = se  in
                     let uu____10893 =
                       let uu____10894 =
                         let uu____10901 =
                           let uu____10908 = FStar_List.map update lbs  in
                           (b, uu____10908)  in
                         (uu____10901, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____10894  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____10893;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___116_10892.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___116_10892.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___116_10892.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___116_10892.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____10921 -> se  in
               let normalized_module =
                 let uu___117_10923 = m1  in
                 let uu____10924 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___117_10923.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____10924;
                   FStar_Syntax_Syntax.exports =
                     (uu___117_10923.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___117_10923.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____10925 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____10925
             else ());
            (m1, m_iface_opt, env2)))
  