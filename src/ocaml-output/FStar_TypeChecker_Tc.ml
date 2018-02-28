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
                                          let uu____1491 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1
                                              act.FStar_Syntax_Syntax.action_typ
                                             in
                                          match uu____1491 with
                                          | (act_typ,uu____1499,g_t) ->
                                              let env' =
                                                let uu___67_1502 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___67_1502.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___67_1502.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1504 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1504
                                                then
                                                  let uu____1505 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn
                                                     in
                                                  let uu____1506 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ
                                                     in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1505 uu____1506
                                                else ());
                                               (let uu____1508 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn
                                                   in
                                                match uu____1508 with
                                                | (act_defn,uu____1516,g_a)
                                                    ->
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
                                                    let uu____1520 =
                                                      let act_typ2 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ1
                                                         in
                                                      match act_typ2.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1548 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c
                                                             in
                                                          (match uu____1548
                                                           with
                                                           | (bs1,uu____1558)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let k =
                                                                 let uu____1565
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1565
                                                                  in
                                                               let uu____1568
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k
                                                                  in
                                                               (match uu____1568
                                                                with
                                                                | (k1,uu____1580,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1582 ->
                                                          let uu____1583 =
                                                            let uu____1588 =
                                                              let uu____1589
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ2
                                                                 in
                                                              let uu____1590
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ2
                                                                 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1589
                                                                uu____1590
                                                               in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1588)
                                                             in
                                                          FStar_Errors.raise_error
                                                            uu____1583
                                                            act_defn1.FStar_Syntax_Syntax.pos
                                                       in
                                                    (match uu____1520 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ1
                                                             expected_k
                                                            in
                                                         ((let uu____1599 =
                                                             let uu____1600 =
                                                               let uu____1601
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1601
                                                                in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1600
                                                              in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1599);
                                                          (let act_typ2 =
                                                             let uu____1605 =
                                                               let uu____1606
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1606.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1605
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1629
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1629
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1638
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1638
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1660
                                                                    =
                                                                    let uu____1661
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1661]
                                                                     in
                                                                    let uu____1662
                                                                    =
                                                                    let uu____1671
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1671]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1660;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1662;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1672
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1672))
                                                             | uu____1675 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1678 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1
                                                              in
                                                           match uu____1678
                                                           with
                                                           | (univs1,act_defn2)
                                                               ->
                                                               let act_typ3 =
                                                                 FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Normalize.Beta]
                                                                   env1
                                                                   act_typ2
                                                                  in
                                                               let act_typ4 =
                                                                 FStar_Syntax_Subst.close_univ_vars
                                                                   univs1
                                                                   act_typ3
                                                                  in
                                                               let uu___68_1687
                                                                 = act  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___68_1687.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___68_1687.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___68_1687.FStar_Syntax_Syntax.action_params);
                                                                 FStar_Syntax_Syntax.action_defn
                                                                   =
                                                                   act_defn2;
                                                                 FStar_Syntax_Syntax.action_typ
                                                                   = act_typ4
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
                                      let uu____1711 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1711
                                       in
                                    let uu____1714 =
                                      let uu____1721 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1721 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1742 ->
                                               let uu____1745 =
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
                                               if uu____1745
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1759 =
                                                    let uu____1764 =
                                                      let uu____1765 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1766 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1765 uu____1766
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1764)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1759
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1714 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1780 =
                                             let uu____1785 =
                                               let uu____1786 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1786.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1785)  in
                                           match uu____1780 with
                                           | ([],uu____1789) -> t
                                           | (uu____1800,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1801,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1819 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1832 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1832
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1837 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1839 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1839))
                                                && (m <> n1)
                                               in
                                            if uu____1837
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____1855 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____1862 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____1863 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1855 uu____1862
                                                  uu____1863
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____1871 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____1871 with
                                           | (univs2,defn) ->
                                               let uu____1878 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____1878 with
                                                | (univs',typ) ->
                                                    let uu___69_1888 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___69_1888.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___69_1888.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___69_1888.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___70_1893 = ed2  in
                                           let uu____1894 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____1895 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____1896 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____1897 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____1898 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____1899 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____1900 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____1901 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____1902 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____1903 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____1904 =
                                             let uu____1905 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____1905
                                              in
                                           let uu____1916 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____1917 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____1918 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___70_1893.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___70_1893.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____1894;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____1895;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____1896;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____1897;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____1898;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____1899;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____1900;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____1901;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____1902;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____1903;
                                             FStar_Syntax_Syntax.repr =
                                               uu____1904;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____1916;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____1917;
                                             FStar_Syntax_Syntax.actions =
                                               uu____1918
                                           }  in
                                         ((let uu____1922 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____1922
                                           then
                                             let uu____1923 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____1923
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
      let uu____1941 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____1941 with
      | (effect_binders_un,signature_un) ->
          let uu____1958 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____1958 with
           | (effect_binders,env1,uu____1977) ->
               let uu____1978 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____1978 with
                | (signature,uu____1994) ->
                    let raise_error1 a uu____2005 =
                      match uu____2005 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2031  ->
                           match uu____2031 with
                           | (bv,qual) ->
                               let uu____2042 =
                                 let uu___71_2043 = bv  in
                                 let uu____2044 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___71_2043.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___71_2043.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2044
                                 }  in
                               (uu____2042, qual)) effect_binders
                       in
                    let uu____2047 =
                      let uu____2054 =
                        let uu____2055 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2055.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2054 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2065)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2087 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2047 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2105 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2105
                           then
                             let uu____2106 =
                               let uu____2109 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2109  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2106
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2143 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2143 with
                           | (t2,comp,uu____2156) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2163 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2163 with
                          | (repr,_comp) ->
                              ((let uu____2185 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2185
                                then
                                  let uu____2186 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2186
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
                                  let uu____2192 =
                                    let uu____2193 =
                                      let uu____2194 =
                                        let uu____2209 =
                                          let uu____2216 =
                                            let uu____2221 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2222 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2221, uu____2222)  in
                                          [uu____2216]  in
                                        (wp_type1, uu____2209)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2194
                                       in
                                    mk1 uu____2193  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2192
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2247 =
                                      let uu____2252 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2252)  in
                                    let uu____2253 =
                                      let uu____2260 =
                                        let uu____2261 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2261
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2260]  in
                                    uu____2247 :: uu____2253  in
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
                                  let uu____2324 = item  in
                                  match uu____2324 with
                                  | (u_item,item1) ->
                                      let uu____2345 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2345 with
                                       | (item2,item_comp) ->
                                           ((let uu____2361 =
                                               let uu____2362 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2362
                                                in
                                             if uu____2361
                                             then
                                               let uu____2363 =
                                                 let uu____2368 =
                                                   let uu____2369 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2370 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2369 uu____2370
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2368)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2363
                                             else ());
                                            (let uu____2372 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2372 with
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
                                let uu____2392 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2392 with
                                | (dmff_env1,uu____2416,bind_wp,bind_elab) ->
                                    let uu____2419 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2419 with
                                     | (dmff_env2,uu____2443,return_wp,return_elab)
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
                                           let uu____2450 =
                                             let uu____2451 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2451.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2450 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2495 =
                                                       let uu____2510 =
                                                         let uu____2515 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2515
                                                          in
                                                       match uu____2510 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2579 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2495 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2618 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2618
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2635 =
                                                               let uu____2636
                                                                 =
                                                                 let uu____2651
                                                                   =
                                                                   let uu____2658
                                                                    =
                                                                    let uu____2663
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2664
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2663,
                                                                    uu____2664)
                                                                     in
                                                                   [uu____2658]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2651)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2636
                                                                in
                                                             mk1 uu____2635
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2679 =
                                                           let uu____2688 =
                                                             let uu____2689 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2689
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2688
                                                            in
                                                         (match uu____2679
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a415 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2708
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2710
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2710
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
                                                                    let uu____2716
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
                                                                    uu____2716
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
                                                                  let uu____2743
                                                                    =
                                                                    let uu____2744
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2745
                                                                    =
                                                                    let uu____2746
                                                                    =
                                                                    let uu____2753
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2753,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2746]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2744
                                                                    uu____2745
                                                                     in
                                                                  uu____2743
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2778
                                                                  =
                                                                  let uu____2779
                                                                    =
                                                                    let uu____2786
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2786]
                                                                     in
                                                                  b11 ::
                                                                    uu____2779
                                                                   in
                                                                let uu____2791
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2778
                                                                  uu____2791
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2792 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let return_wp1 =
                                           let uu____2794 =
                                             let uu____2795 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2795.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2794 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2839 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2839
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____2852 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let bind_wp1 =
                                           let uu____2854 =
                                             let uu____2855 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____2855.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2854 with
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
                                                     let uu____2882 =
                                                       let uu____2883 =
                                                         let uu____2886 =
                                                           let uu____2887 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____2887
                                                            in
                                                         [uu____2886]  in
                                                       FStar_List.append
                                                         uu____2883 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____2882 body what)
                                              | uu____2888 ->
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
                                             (let uu____2906 =
                                                let uu____2907 =
                                                  let uu____2908 =
                                                    let uu____2923 =
                                                      let uu____2924 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2924
                                                       in
                                                    (t, uu____2923)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2908
                                                   in
                                                mk1 uu____2907  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2906)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2954 = f a2  in
                                               [uu____2954]
                                           | x::xs ->
                                               let uu____2959 =
                                                 apply_last1 f xs  in
                                               x :: uu____2959
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
                                           let uu____2979 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____2979 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3009 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3009
                                                 then
                                                   let uu____3010 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3010
                                                 else ());
                                                (let uu____3012 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3012))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3021 =
                                                 let uu____3026 = mk_lid name
                                                    in
                                                 let uu____3027 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3026 uu____3027
                                                  in
                                               (match uu____3021 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3031 =
                                                        let uu____3034 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3034
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3031);
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
                                          (let uu____3131 =
                                             let uu____3134 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3135 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3134 :: uu____3135  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3131);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3233 =
                                               let uu____3236 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3237 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3236 :: uu____3237  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3233);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3332 =
                                                FStar_List.fold_left
                                                  (fun uu____3372  ->
                                                     fun action  ->
                                                       match uu____3372 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3393 =
                                                             let uu____3400 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3400
                                                               params_un
                                                              in
                                                           (match uu____3393
                                                            with
                                                            | (action_params,env',uu____3409)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3429
                                                                     ->
                                                                    match uu____3429
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3440
                                                                    =
                                                                    let uu___72_3441
                                                                    = bv  in
                                                                    let uu____3442
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___72_3441.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___72_3441.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3442
                                                                    }  in
                                                                    (uu____3440,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3446
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3446
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
                                                                    uu____3476
                                                                    ->
                                                                    let uu____3477
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3477
                                                                     in
                                                                    ((
                                                                    let uu____3481
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3481
                                                                    then
                                                                    let uu____3482
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3483
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3484
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3485
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3482
                                                                    uu____3483
                                                                    uu____3484
                                                                    uu____3485
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
                                                                    let uu____3489
                                                                    =
                                                                    let uu____3492
                                                                    =
                                                                    let uu___73_3493
                                                                    = action
                                                                     in
                                                                    let uu____3494
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3495
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___73_3493.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___73_3493.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___73_3493.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3494;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3495
                                                                    }  in
                                                                    uu____3492
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3489))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3332 with
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
                                                      let uu____3528 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3529 =
                                                        let uu____3532 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3532]  in
                                                      uu____3528 ::
                                                        uu____3529
                                                       in
                                                    let uu____3533 =
                                                      let uu____3534 =
                                                        let uu____3535 =
                                                          let uu____3536 =
                                                            let uu____3551 =
                                                              let uu____3558
                                                                =
                                                                let uu____3563
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3564
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3563,
                                                                  uu____3564)
                                                                 in
                                                              [uu____3558]
                                                               in
                                                            (repr,
                                                              uu____3551)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3536
                                                           in
                                                        mk1 uu____3535  in
                                                      let uu____3579 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3534
                                                        uu____3579
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3533
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3582 =
                                                    let uu____3589 =
                                                      let uu____3590 =
                                                        let uu____3593 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3593
                                                         in
                                                      uu____3590.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3589 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3603)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3632
                                                                =
                                                                let uu____3649
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3649
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3707
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3632
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3757
                                                                    =
                                                                    let uu____3758
                                                                    =
                                                                    let uu____3761
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3761
                                                                     in
                                                                    uu____3758.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3757
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3786
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3786
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3799
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3824
                                                                     ->
                                                                    match uu____3824
                                                                    with
                                                                    | 
                                                                    (bv,uu____3830)
                                                                    ->
                                                                    let uu____3831
                                                                    =
                                                                    let uu____3832
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3832
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3831
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3799
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
                                                                    let uu____3896
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3896
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3901
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3909
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3909
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____3914
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____3917
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____3914,
                                                                    uu____3917)))
                                                                    | 
                                                                    uu____3924
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3925
                                                                    =
                                                                    let uu____3930
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3931
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3930)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____3925)))
                                                       | uu____3932 ->
                                                           Obj.repr
                                                             (let uu____3933
                                                                =
                                                                let uu____3938
                                                                  =
                                                                  let uu____3939
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____3939
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____3938)
                                                                 in
                                                              raise_error1 ()
                                                                uu____3933))
                                                     in
                                                  (match uu____3582 with
                                                   | (pre,post) ->
                                                       ((let uu____3957 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____3959 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____3961 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___74_3963 =
                                                             ed  in
                                                           let uu____3964 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____3965 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____3966 =
                                                             let uu____3967 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____3967)
                                                              in
                                                           let uu____3974 =
                                                             let uu____3975 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____3975)
                                                              in
                                                           let uu____3982 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____3983 =
                                                             let uu____3984 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____3984)
                                                              in
                                                           let uu____3991 =
                                                             let uu____3992 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____3992)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3964;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3965;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3966;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3974;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___74_3963.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3982;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3983;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3991;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____3999 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____3999
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4017
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4017
                                                               then
                                                                 let uu____4018
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4018
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
                                                                    let uu____4030
                                                                    =
                                                                    let uu____4033
                                                                    =
                                                                    let uu____4042
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4042)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4033
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
                                                                    uu____4030;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4057
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4057
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4059
                                                                 =
                                                                 let uu____4062
                                                                   =
                                                                   let uu____4065
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4065
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4062
                                                                   sigelts'
                                                                  in
                                                               (uu____4059,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4122 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4122 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4155 = FStar_List.hd ses  in
            uu____4155.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4160 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4164,[],t,uu____4166,uu____4167);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4169;
               FStar_Syntax_Syntax.sigattrs = uu____4170;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4172,_t_top,_lex_t_top,_0_40,uu____4175);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4177;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4178;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4180,_t_cons,_lex_t_cons,_0_41,uu____4183);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4185;
                 FStar_Syntax_Syntax.sigattrs = uu____4186;_}::[]
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
                 let uu____4245 =
                   let uu____4248 =
                     let uu____4249 =
                       let uu____4256 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4256, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4249  in
                   FStar_Syntax_Syntax.mk uu____4248  in
                 uu____4245 FStar_Pervasives_Native.None r1  in
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
                   let uu____4274 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4274
                    in
                 let hd1 =
                   let uu____4276 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4276
                    in
                 let tl1 =
                   let uu____4278 =
                     let uu____4279 =
                       let uu____4282 =
                         let uu____4283 =
                           let uu____4290 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4290, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4283  in
                       FStar_Syntax_Syntax.mk uu____4282  in
                     uu____4279 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4278
                    in
                 let res =
                   let uu____4299 =
                     let uu____4302 =
                       let uu____4303 =
                         let uu____4310 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4310,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4303  in
                     FStar_Syntax_Syntax.mk uu____4302  in
                   uu____4299 FStar_Pervasives_Native.None r2  in
                 let uu____4316 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4316
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
               let uu____4355 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4355;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4360 ->
               let err_msg =
                 let uu____4364 =
                   let uu____4365 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4365  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4364
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
            let uu____4390 = FStar_Syntax_Util.type_u ()  in
            match uu____4390 with
            | (k,uu____4396) ->
                let phi1 =
                  let uu____4398 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____4398
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4400 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1  in
                  match uu____4400 with
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
          let uu____4442 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4442 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4475 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas
                   in
                FStar_All.pipe_right uu____4475 FStar_List.flatten  in
              ((let uu____4489 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____4489
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
                          let uu____4500 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4510,uu____4511,uu____4512,uu____4513,uu____4514)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4523 -> failwith "Impossible!"  in
                          match uu____4500 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4534 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4538,uu____4539,uu____4540,uu____4541,uu____4542)
                        -> lid
                    | uu____4551 -> failwith "Impossible"  in
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
                  let uu____4569 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4569
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
                     let uu____4592 =
                       let uu____4595 =
                         let uu____4596 =
                           FStar_TypeChecker_Env.get_range env1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4596;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       uu____4595 :: ses1  in
                     (uu____4592, data_ops_ses))
                   in
                (let uu____4606 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4640 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4665 ->
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
           let uu____4717 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4717 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4755 = cps_and_elaborate env1 ne  in
           (match uu____4755 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___75_4792 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___75_4792.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___75_4792.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___75_4792.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___75_4792.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___76_4794 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___76_4794.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___76_4794.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___76_4794.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___76_4794.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___77_4802 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___77_4802.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___77_4802.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___77_4802.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___77_4802.FStar_Syntax_Syntax.sigattrs)
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
           let uu____4810 =
             let uu____4817 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4817
              in
           (match uu____4810 with
            | (a,wp_a_src) ->
                let uu____4832 =
                  let uu____4839 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4839
                   in
                (match uu____4832 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4855 =
                         let uu____4858 =
                           let uu____4859 =
                             let uu____4866 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____4866)  in
                           FStar_Syntax_Syntax.NT uu____4859  in
                         [uu____4858]  in
                       FStar_Syntax_Subst.subst uu____4855 wp_b_tgt  in
                     let expected_k =
                       let uu____4870 =
                         let uu____4877 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____4878 =
                           let uu____4881 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____4881]  in
                         uu____4877 :: uu____4878  in
                       let uu____4882 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____4870 uu____4882  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4903 =
                           let uu____4908 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____4908)
                            in
                         let uu____4909 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____4903 uu____4909  in
                       let uu____4912 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____4912 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____4944 =
                             let uu____4945 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____4945  in
                           if uu____4944
                           then no_reify eff_name
                           else
                             (let uu____4951 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____4952 =
                                let uu____4955 =
                                  let uu____4956 =
                                    let uu____4971 =
                                      let uu____4974 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____4975 =
                                        let uu____4978 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____4978]  in
                                      uu____4974 :: uu____4975  in
                                    (repr, uu____4971)  in
                                  FStar_Syntax_Syntax.Tm_app uu____4956  in
                                FStar_Syntax_Syntax.mk uu____4955  in
                              uu____4952 FStar_Pervasives_Native.None
                                uu____4951)
                        in
                     let uu____4984 =
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
                               let uu____5037 =
                                 let uu____5040 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 FStar_Pervasives_Native.fst uu____5040  in
                               FStar_Syntax_Subst.subst uu____5037 lift_wp
                             else lift_wp  in
                           let uu____5054 =
                             check_and_gen env1 lift_wp1 expected_k  in
                           (lift, uu____5054)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let lift1 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5080 =
                                 let uu____5083 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 FStar_Pervasives_Native.fst uu____5083  in
                               FStar_Syntax_Subst.subst uu____5080 lift
                             else lift  in
                           ((let uu____5098 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5098
                             then
                               let uu____5099 =
                                 FStar_Syntax_Print.term_to_string lift1  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5099
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5102 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift1
                                in
                             match uu____5102 with
                             | (lift2,comp,uu____5117) ->
                                 let uu____5118 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift2
                                    in
                                 (match uu____5118 with
                                  | (uu____5131,lift_wp,lift_elab) ->
                                      let uu____5134 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5135 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____4984 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___78_5176 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___78_5176.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___78_5176.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___78_5176.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___78_5176.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___78_5176.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___78_5176.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___78_5176.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___78_5176.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___78_5176.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___78_5176.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___78_5176.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___78_5176.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___78_5176.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___78_5176.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___78_5176.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___78_5176.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___78_5176.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___78_5176.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___78_5176.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___78_5176.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___78_5176.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___78_5176.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___78_5176.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___78_5176.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___78_5176.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___78_5176.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___78_5176.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___78_5176.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___78_5176.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___78_5176.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___78_5176.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___78_5176.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___78_5176.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___78_5176.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5182,lift1)
                                ->
                                let uu____5194 =
                                  let uu____5201 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5201
                                   in
                                (match uu____5194 with
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
                                         let uu____5225 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5226 =
                                           let uu____5229 =
                                             let uu____5230 =
                                               let uu____5245 =
                                                 let uu____5248 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5249 =
                                                   let uu____5252 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5252]  in
                                                 uu____5248 :: uu____5249  in
                                               (lift_wp1, uu____5245)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5230
                                              in
                                           FStar_Syntax_Syntax.mk uu____5229
                                            in
                                         uu____5226
                                           FStar_Pervasives_Native.None
                                           uu____5225
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5261 =
                                         let uu____5268 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5269 =
                                           let uu____5272 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5273 =
                                             let uu____5276 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5276]  in
                                           uu____5272 :: uu____5273  in
                                         uu____5268 :: uu____5269  in
                                       let uu____5277 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5261
                                         uu____5277
                                        in
                                     let uu____5280 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5280 with
                                      | (expected_k2,uu____5290,uu____5291)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift2))
                             in
                          let sub2 =
                            let uu___79_5294 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___79_5294.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___79_5294.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___80_5296 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___80_5296.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___80_5296.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___80_5296.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___80_5296.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let uu____5311 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (uvs, tps, c)
             else
               (let uu____5325 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____5325 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____5352 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____5352 c  in
                    (uvs1, tps1, c1))
              in
           (match uu____5311 with
            | (uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____5373 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____5373 with
                 | (tps2,c2) ->
                     let uu____5388 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____5388 with
                      | (tps3,env3,us) ->
                          let uu____5406 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____5406 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____5427 =
                                   let uu____5428 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____5428
                                    in
                                 match uu____5427 with
                                 | (uvs2,t) ->
                                     let uu____5443 =
                                       let uu____5456 =
                                         let uu____5461 =
                                           let uu____5462 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____5462.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____5461)  in
                                       match uu____5456 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____5477,c5)) -> ([], c5)
                                       | (uu____5517,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____5544 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____5443 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____5588 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____5588 with
                                              | (uu____5593,t1) ->
                                                  let uu____5595 =
                                                    let uu____5600 =
                                                      let uu____5601 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____5602 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____5603 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____5601 uu____5602
                                                        uu____5603
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____5600)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5595 r)
                                           else ();
                                           (let se1 =
                                              let uu___81_5606 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___81_5606.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___81_5606.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___81_5606.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___81_5606.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5623,uu____5624,uu____5625) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5629  ->
                   match uu___56_5629 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5630 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5635,uu____5636) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5644  ->
                   match uu___56_5644 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5645 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5655 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5655
             then
               let uu____5656 =
                 let uu____5661 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid)
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5661)
                  in
               FStar_Errors.raise_error uu____5656 r
             else ());
            (let uu____5663 =
               if uvs = []
               then
                 let uu____5664 =
                   let uu____5665 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____5665  in
                 check_and_gen env2 t uu____5664
               else
                 (let uu____5671 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____5671 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5679 =
                          let uu____5680 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____5680  in
                        tc_check_trivial_guard env2 t1 uu____5679  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____5686 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____5686))
                in
             match uu____5663 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___82_5702 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___82_5702.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___82_5702.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___82_5702.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___82_5702.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5712 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____5712 with
            | (uu____5725,phi1) ->
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
           let uu____5735 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____5735 with
            | (e1,c,g1) ->
                let uu____5753 =
                  let uu____5760 =
                    let uu____5763 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____5763  in
                  let uu____5764 =
                    let uu____5769 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____5769)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5760 uu____5764
                   in
                (match uu____5753 with
                 | (e2,uu____5779,g) ->
                     ((let uu____5782 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5782);
                      (let se1 =
                         let uu___83_5784 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___83_5784.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___83_5784.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___83_5784.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___83_5784.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5835 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____5835
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5843 =
                      let uu____5848 =
                        let uu____5849 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____5850 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____5851 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____5849 uu____5850 uu____5851
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____5848)
                       in
                    FStar_Errors.raise_error uu____5843 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____5877 =
                   let uu____5878 = FStar_Syntax_Subst.compress def  in
                   uu____5878.FStar_Syntax_Syntax.n  in
                 match uu____5877 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5888,uu____5889)
                     -> binders
                 | uu____5910 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5920;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5998) -> val_bs1
                     | (uu____6021,[]) -> val_bs1
                     | ((body_bv,uu____6045)::bt,(val_bv,aqual)::vt) ->
                         let uu____6082 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6098) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___84_6100 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___85_6103 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___85_6103.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___84_6100.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___84_6100.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6082
                      in
                   let uu____6104 =
                     let uu____6107 =
                       let uu____6108 =
                         let uu____6121 = rename_binders1 def_bs val_bs  in
                         (uu____6121, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6108  in
                     FStar_Syntax_Syntax.mk uu____6107  in
                   uu____6104 FStar_Pervasives_Native.None r1
               | uu____6139 -> typ1  in
             let uu___86_6140 = lb  in
             let uu____6141 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___86_6140.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___86_6140.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6141;
               FStar_Syntax_Syntax.lbeff =
                 (uu___86_6140.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___86_6140.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___86_6140.FStar_Syntax_Syntax.lbattrs)
             }  in
           let uu____6144 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6195  ->
                     fun lb  ->
                       match uu____6195 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6237 =
                             let uu____6248 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6248 with
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
                                   | uu____6333 ->
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
                                  (let uu____6376 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def)
                                      in
                                   (false, uu____6376, quals_opt1)))
                              in
                           (match uu____6237 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6144 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6470 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___57_6474  ->
                                match uu___57_6474 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6475 -> false))
                         in
                      if uu____6470
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6485 =
                    let uu____6488 =
                      let uu____6489 =
                        let uu____6502 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6502)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6489  in
                    FStar_Syntax_Syntax.mk uu____6488  in
                  uu____6485 FStar_Pervasives_Native.None r  in
                let uu____6520 =
                  let uu____6531 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___87_6540 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___87_6540.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___87_6540.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___87_6540.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___87_6540.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___87_6540.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___87_6540.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___87_6540.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___87_6540.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___87_6540.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___87_6540.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___87_6540.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___87_6540.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___87_6540.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___87_6540.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___87_6540.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___87_6540.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___87_6540.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___87_6540.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___87_6540.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___87_6540.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___87_6540.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___87_6540.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___87_6540.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___87_6540.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___87_6540.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___87_6540.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___87_6540.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___87_6540.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___87_6540.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___87_6540.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___87_6540.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___87_6540.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___87_6540.FStar_TypeChecker_Env.dep_graph)
                       }) e
                     in
                  match uu____6531 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6553;
                       FStar_Syntax_Syntax.vars = uu____6554;_},uu____6555,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6584 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6584)  in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6602,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6607 -> quals  in
                      ((let uu___88_6615 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___88_6615.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___88_6615.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___88_6615.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6624 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6520 with
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
                      (let uu____6673 = log env2  in
                       if uu____6673
                       then
                         let uu____6674 =
                           let uu____6675 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6690 =
                                         let uu____6699 =
                                           let uu____6700 =
                                             let uu____6703 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____6703.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____6700.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6699
                                          in
                                       match uu____6690 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6710 -> false  in
                                     if should_log
                                     then
                                       let uu____6719 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____6720 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6719 uu____6720
                                     else ""))
                              in
                           FStar_All.pipe_right uu____6675
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____6674
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t  in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6751 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____6751 with
                              | (bs1,c1) ->
                                  let uu____6758 =
                                    FStar_Syntax_Util.is_total_comp c1  in
                                  if uu____6758
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6770 =
                                            let uu____6771 =
                                              FStar_Syntax_Subst.compress t'
                                               in
                                            uu____6771.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6770 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6796 =
                                                 let uu____6797 =
                                                   FStar_Syntax_Subst.compress
                                                     h
                                                    in
                                                 uu____6797.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6796 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6807 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6807
                                                       in
                                                    let uu____6808 =
                                                      let uu____6809 =
                                                        let uu____6810 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u'
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6810 args
                                                         in
                                                      uu____6809
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6808 u
                                                | uu____6813 -> c1)
                                           | uu____6814 -> c1)
                                      | uu____6815 -> c1  in
                                    let uu___89_6816 = t1  in
                                    let uu____6817 =
                                      let uu____6818 =
                                        let uu____6831 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c'
                                           in
                                        (bs1, uu____6831)  in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6818
                                       in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6817;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___89_6816.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___89_6816.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6855 =
                               let uu____6856 = FStar_Syntax_Subst.compress h
                                  in
                               uu____6856.FStar_Syntax_Syntax.n  in
                             (match uu____6855 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6866 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6866
                                     in
                                  let uu____6867 =
                                    let uu____6868 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u'
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6868
                                      args
                                     in
                                  uu____6867 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6871 -> t1)
                         | uu____6872 -> t1  in
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
                           let uu____6900 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6900
                            in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6917 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x)
                                   in
                                (uu____6917, (FStar_Pervasives_Native.snd x)))
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
                           let uu____6948 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6948
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
                         let uu___90_6955 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___91_6967 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___91_6967.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___91_6967.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___91_6967.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___91_6967.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___91_6967.FStar_Syntax_Syntax.lbattrs)
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___90_6955.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___90_6955.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___90_6955.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___90_6955.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6984 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp
                                in
                             (match uu____6984 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp
                                     in
                                  let uu____7018 =
                                    let uu____7019 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____7019.FStar_Syntax_Syntax.n  in
                                  (match uu____7018 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h
                                          in
                                       let tac_lid =
                                         let uu____7052 =
                                           let uu____7055 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname
                                              in
                                           uu____7055.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____7052.FStar_Syntax_Syntax.v  in
                                       let assm_lid =
                                         let uu____7057 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                            in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____7057
                                          in
                                       let uu____7058 =
                                         get_tactic_fv env2 assm_lid h1  in
                                       (match uu____7058 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7068 =
                                              let uu____7069 =
                                                let uu____7070 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7070
                                                 in
                                              Prims.op_Negation uu____7069
                                               in
                                            if uu____7068
                                            then
                                              ((let uu____7100 =
                                                  let uu____7101 =
                                                    FStar_Syntax_Util.is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule
                                                     in
                                                  Prims.op_Negation
                                                    uu____7101
                                                   in
                                                if uu____7100
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
                                               (let uu____7154 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid
                                                   in
                                                if uu____7154
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
                                   | uu____7183 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7188 -> FStar_Pervasives_Native.None  in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7210 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics")
                                in
                             if uu____7210
                             then
                               let uu____7211 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm
                                  in
                               let uu____7212 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl
                                  in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7211 uu____7212
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
             (fun uu___58_7263  ->
                match uu___58_7263 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7264 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7270) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7276 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7285 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7290 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7315 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7339) ->
          let uu____7348 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7348
          then
            let for_export_bundle se1 uu____7379 =
              match uu____7379 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7418,uu____7419) ->
                       let dec =
                         let uu___92_7429 = se1  in
                         let uu____7430 =
                           let uu____7431 =
                             let uu____7438 =
                               let uu____7441 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7441  in
                             (l, us, uu____7438)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7431  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7430;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_7429.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_7429.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_7429.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7453,uu____7454,uu____7455) ->
                       let dec =
                         let uu___93_7461 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___93_7461.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___93_7461.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___93_7461.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7466 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7488,uu____7489,uu____7490) ->
          let uu____7491 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7491 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7512 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7512
          then
            ([(let uu___94_7528 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___94_7528.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___94_7528.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___94_7528.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7530 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___59_7534  ->
                       match uu___59_7534 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7535 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7540 -> true
                       | uu____7541 -> false))
                in
             if uu____7530 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7559 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7564 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7569 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7574 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7579 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7597) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7614 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7614
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
          let uu____7645 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7645
          then
            let uu____7654 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___95_7667 = se  in
                      let uu____7668 =
                        let uu____7669 =
                          let uu____7676 =
                            let uu____7677 =
                              let uu____7680 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7680.FStar_Syntax_Syntax.fv_name  in
                            uu____7677.FStar_Syntax_Syntax.v  in
                          (uu____7676, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7669  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7668;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___95_7667.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___95_7667.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___95_7667.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7654, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7700 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7717 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7732) ->
          let env1 =
            let uu____7736 = FStar_Options.using_facts_from ()  in
            FStar_TypeChecker_Env.set_proof_ns uu____7736 env  in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7738 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7739 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7749 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7749) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7750,uu____7751,uu____7752) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7756  ->
                  match uu___60_7756 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7757 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7758,uu____7759) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7767  ->
                  match uu___60_7767 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7768 -> false))
          -> env
      | uu____7769 -> FStar_TypeChecker_Env.push_sigelt env se
  
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
      let rec process_one_decl uu____7829 se =
        match uu____7829 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7882 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7882
              then
                let uu____7883 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7883
              else ());
             (let uu____7885 = tc_decl env1 se  in
              match uu____7885 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7935 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____7935
                             then
                               let uu____7936 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7936
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
                    (let uu____7959 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____7959
                     then
                       let uu____7960 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7966 =
                                  let uu____7967 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____7967 "\n"  in
                                Prims.strcat s uu____7966) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____7960
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7972 =
                       if dont_use_exports
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____8015 se1 =
                            match uu____8015 with
                            | (exports1,hidden1) ->
                                let uu____8043 = for_export hidden1 se1  in
                                (match uu____8043 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____7972 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___96_8122 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___96_8122.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___96_8122.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___96_8122.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___96_8122.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____8200 = acc  in
        match uu____8200 with
        | (uu____8235,uu____8236,env1,uu____8238) ->
            let uu____8251 =
              FStar_Util.record_time
                (fun uu____8297  -> process_one_decl acc se)
               in
            (match uu____8251 with
             | (r,ms_elapsed) ->
                 ((let uu____8361 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8361
                   then
                     let uu____8362 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8363 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8362 uu____8363
                   else ());
                  r))
         in
      let uu____8365 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8365 with
      | (ses1,exports,env1,uu____8413) ->
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
        (let uu____8453 = FStar_Options.debug_any ()  in
         if uu____8453
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
           let uu___97_8459 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___97_8459.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___97_8459.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___97_8459.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___97_8459.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___97_8459.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___97_8459.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___97_8459.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___97_8459.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___97_8459.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___97_8459.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___97_8459.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___97_8459.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___97_8459.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___97_8459.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___97_8459.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___97_8459.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___97_8459.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___97_8459.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___97_8459.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___97_8459.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___97_8459.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___97_8459.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___97_8459.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___97_8459.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___97_8459.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___97_8459.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___97_8459.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___97_8459.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___97_8459.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___97_8459.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___97_8459.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___97_8459.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___97_8459.FStar_TypeChecker_Env.dep_graph)
           }  in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name
             in
          let uu____8463 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations  in
          match uu____8463 with
          | (ses,exports,env3) ->
              ((let uu___98_8496 = modul  in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___98_8496.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___98_8496.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___98_8496.FStar_Syntax_Syntax.is_interface)
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
        let uu____8518 = tc_decls env decls  in
        match uu____8518 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___99_8549 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___99_8549.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___99_8549.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___99_8549.FStar_Syntax_Syntax.is_interface)
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
          let uu___100_8566 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___100_8566.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___100_8566.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___100_8566.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___100_8566.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___100_8566.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___100_8566.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___100_8566.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___100_8566.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___100_8566.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___100_8566.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___100_8566.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___100_8566.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___100_8566.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___100_8566.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___100_8566.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___100_8566.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___100_8566.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___100_8566.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___100_8566.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___100_8566.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___100_8566.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___100_8566.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___100_8566.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___100_8566.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___100_8566.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___100_8566.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___100_8566.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___100_8566.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___100_8566.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___100_8566.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___100_8566.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___100_8566.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8577 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8577 with
          | (univs2,t1) ->
              ((let uu____8585 =
                  let uu____8586 =
                    let uu____8589 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8589  in
                  FStar_All.pipe_left uu____8586
                    (FStar_Options.Other "Exports")
                   in
                if uu____8585
                then
                  let uu____8590 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8591 =
                    let uu____8592 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8592
                      (FStar_String.concat ", ")
                     in
                  let uu____8601 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8590 uu____8591 uu____8601
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____8604 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____8604 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____8628 =
             let uu____8629 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8630 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8629 uu____8630
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8628);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8637) ->
              let uu____8646 =
                let uu____8647 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8647  in
              if uu____8646
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8657,uu____8658) ->
              let t =
                let uu____8670 =
                  let uu____8673 =
                    let uu____8674 =
                      let uu____8687 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8687)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8674  in
                  FStar_Syntax_Syntax.mk uu____8673  in
                uu____8670 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8694,uu____8695,uu____8696) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8704 =
                let uu____8705 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8705  in
              if uu____8704 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8709,lbs),uu____8711) ->
              let uu____8726 =
                let uu____8727 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8727  in
              if uu____8726
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
              let uu____8746 =
                let uu____8747 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8747  in
              if uu____8746
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8754 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8755 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8762 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8763 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8764 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8765 -> ()  in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
  
let (finish_partial_modul :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.sigelts ->
          (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2)
  =
  fun must_check_exports  ->
    fun env  ->
      fun modul  ->
        fun exports  ->
          let modul1 =
            if dont_use_exports
            then
              let uu___101_8784 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___101_8784.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (uu___101_8784.FStar_Syntax_Syntax.declarations);
                FStar_Syntax_Syntax.exports =
                  (modul.FStar_Syntax_Syntax.declarations);
                FStar_Syntax_Syntax.is_interface =
                  (uu___101_8784.FStar_Syntax_Syntax.is_interface)
              }
            else
              (let uu___102_8786 = modul  in
               {
                 FStar_Syntax_Syntax.name =
                   (uu___102_8786.FStar_Syntax_Syntax.name);
                 FStar_Syntax_Syntax.declarations =
                   (uu___102_8786.FStar_Syntax_Syntax.declarations);
                 FStar_Syntax_Syntax.exports = exports;
                 FStar_Syntax_Syntax.is_interface =
                   (uu___102_8786.FStar_Syntax_Syntax.is_interface)
               })
             in
          let env1 = FStar_TypeChecker_Env.finish_module env modul1  in
          (let uu____8789 =
             ((let uu____8792 = FStar_Options.lax ()  in
               Prims.op_Negation uu____8792) &&
                (Prims.op_Negation dont_use_exports))
               && must_check_exports
              in
           if uu____8789 then check_exports env1 modul1 exports else ());
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
            (Prims.strcat "Ending modul "
               (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
            env1 modul1;
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
            ();
          (let uu____8798 =
             let uu____8799 = FStar_Options.interactive ()  in
             Prims.op_Negation uu____8799  in
           if uu____8798
           then
             let uu____8800 = FStar_Options.restore_cmd_line_options true  in
             FStar_All.pipe_right uu____8800 FStar_Pervasives.ignore
           else ());
          (modul1, env1)
  
let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let env1 =
        FStar_TypeChecker_Env.set_current_module env
          modul.FStar_Syntax_Syntax.name
         in
      (let uu____8810 =
         let uu____8811 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
         Prims.strcat "Internals for " uu____8811  in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
         uu____8810);
      (let env2 =
         FStar_List.fold_left
           (fun env2  ->
              fun se  ->
                let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
                let lids = FStar_Syntax_Util.lids_of_sigelt se  in
                FStar_All.pipe_right lids
                  (FStar_List.iter
                     (fun lid  ->
                        let uu____8830 =
                          FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                        ()));
                env3) env1 modul.FStar_Syntax_Syntax.declarations
          in
       let uu____8851 =
         finish_partial_modul false env2 modul
           modul.FStar_Syntax_Syntax.exports
          in
       FStar_Pervasives_Native.snd uu____8851)
  
let (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun modul  ->
      let uu____8866 = tc_partial_modul env modul true  in
      match uu____8866 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul true env1 modul1 non_private_decls
  
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
               ((q = FStar_Syntax_Syntax.Abstract) ||
                  (q = FStar_Syntax_Syntax.Irreducible)))
         in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               ((((q = FStar_Syntax_Syntax.Abstract) ||
                    (q = FStar_Syntax_Syntax.Noeq))
                   || (q = FStar_Syntax_Syntax.Unopteq))
                  || (q = FStar_Syntax_Syntax.Irreducible)))
         in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               ((((q = FStar_Syntax_Syntax.Abstract) ||
                    (q = FStar_Syntax_Syntax.Irreducible))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
         in
      let add_assume_if_needed quals =
        if is_assume quals
        then quals
        else FStar_Syntax_Syntax.Assumption :: quals  in
      let val_typs = FStar_Util.mk_ref []  in
      let abstract_inductive_datacons = FStar_Util.mk_ref []  in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q  ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l ->
                 let uu____9011 =
                   FStar_ST.op_Bang abstract_inductive_datacons  in
                 FStar_List.existsb (fun l'  -> FStar_Ident.lid_equals l l')
                   uu____9011
             | FStar_Syntax_Syntax.Projector (l,uu____9062) ->
                 let uu____9063 =
                   FStar_ST.op_Bang abstract_inductive_datacons  in
                 FStar_List.existsb (fun l'  -> FStar_Ident.lid_equals l l')
                   uu____9063
             | uu____9113 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____9132 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____9163 ->
                   let uu____9164 =
                     let uu____9167 =
                       let uu____9168 =
                         let uu____9181 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____9181)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____9168  in
                     FStar_Syntax_Syntax.mk uu____9167  in
                   uu____9164 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____9189,uu____9190) ->
            let s1 =
              let uu___103_9200 = s  in
              let uu____9201 =
                let uu____9202 =
                  let uu____9209 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____9209)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____9202  in
              let uu____9210 =
                let uu____9213 =
                  filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals
                   in
                FStar_Syntax_Syntax.Assumption :: uu____9213  in
              {
                FStar_Syntax_Syntax.sigel = uu____9201;
                FStar_Syntax_Syntax.sigrng =
                  (uu___103_9200.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____9210;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___103_9200.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___103_9200.FStar_Syntax_Syntax.sigattrs)
              }  in
            if
              Prims.op_Negation
                (is_noeq_or_unopteq s.FStar_Syntax_Syntax.sigquals)
            then
              let uu____9216 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9216 with
               | (usubst,uvs1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let uu____9236 =
                     FStar_TypeChecker_Util.get_optimized_haseq_axiom env1 s
                       usubst uvs1
                      in
                   (match uu____9236 with
                    | (axiom_lid,fml,uu____9249,uu____9250,uu____9251) ->
                        let uu____9252 =
                          FStar_TypeChecker_Util.generalize_universes env1
                            fml
                           in
                        (match uu____9252 with
                         | (uvs2,fml1) ->
                             let s2 =
                               let uu___104_9260 = s  in
                               let uu____9261 =
                                 let uu____9264 =
                                   filter_out_abstract
                                     s.FStar_Syntax_Syntax.sigquals
                                    in
                                 FStar_Syntax_Syntax.Assumption :: uu____9264
                                  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_assume
                                      (axiom_lid, uvs2, fml1));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___104_9260.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = uu____9261;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___104_9260.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___104_9260.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             [s1; s2])))
            else [s1]
        | uu____9270 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____9288 =
        match uu____9288 with
        | (uvs,c_or_t) ->
            let t =
              let uu____9310 = FStar_All.pipe_right c_or_t FStar_Util.is_left
                 in
              if uu____9310
              then
                let uu____9317 = FStar_All.pipe_right c_or_t FStar_Util.left
                   in
                FStar_All.pipe_right uu____9317 FStar_Syntax_Util.comp_result
              else FStar_All.pipe_right c_or_t FStar_Util.right  in
            let uu___105_9329 = s  in
            let uu____9330 =
              let uu____9333 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____9333  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___105_9329.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____9330;
              FStar_Syntax_Syntax.sigmeta =
                (uu___105_9329.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___105_9329.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let extract_lb_annotation lb lid r =
        let opt =
          let uu____9389 = FStar_ST.op_Bang val_typs  in
          FStar_List.tryFind
            (fun uu____9481  ->
               match uu____9481 with
               | (l,uu____9493,uu____9494) -> FStar_Ident.lid_equals lid l)
            uu____9389
           in
        if FStar_Util.is_some opt
        then
          let uu____9527 = FStar_All.pipe_right opt FStar_Util.must  in
          match uu____9527 with
          | (uu____9584,uvs,t) ->
              let uu____9595 =
                let uu___106_9596 = lb  in
                let uu____9597 =
                  FStar_Syntax_Util.ascribe lb.FStar_Syntax_Syntax.lbdef
                    ((FStar_Util.Inl t), FStar_Pervasives_Native.None)
                   in
                {
                  FStar_Syntax_Syntax.lbname =
                    (uu___106_9596.FStar_Syntax_Syntax.lbname);
                  FStar_Syntax_Syntax.lbunivs = uvs;
                  FStar_Syntax_Syntax.lbtyp =
                    (uu___106_9596.FStar_Syntax_Syntax.lbtyp);
                  FStar_Syntax_Syntax.lbeff =
                    (uu___106_9596.FStar_Syntax_Syntax.lbeff);
                  FStar_Syntax_Syntax.lbdef = uu____9597;
                  FStar_Syntax_Syntax.lbattrs =
                    (uu___106_9596.FStar_Syntax_Syntax.lbattrs)
                }  in
              (uu____9595,
                (FStar_Pervasives_Native.Some (uvs, (FStar_Util.Inr t))))
        else
          (let uu____9655 =
             let uu____9656 =
               FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
             uu____9656.FStar_Syntax_Syntax.n  in
           match uu____9655 with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____9673 =
                 let uu____9674 =
                   FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef
                    in
                 uu____9674.FStar_Syntax_Syntax.n  in
               (match uu____9673 with
                | FStar_Syntax_Syntax.Tm_ascribed
                    (uu____9691,(FStar_Util.Inr c,uu____9693),uu____9694) ->
                    (lb,
                      (FStar_Pervasives_Native.Some
                         ((lb.FStar_Syntax_Syntax.lbunivs),
                           (FStar_Util.Inl c))))
                | FStar_Syntax_Syntax.Tm_ascribed
                    (uu____9777,(FStar_Util.Inl t,uu____9779),uu____9780) ->
                    (lb,
                      (FStar_Pervasives_Native.Some
                         ((lb.FStar_Syntax_Syntax.lbunivs),
                           (FStar_Util.Inr t))))
                | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____9865) ->
                    let uu____9886 =
                      let uu____9887 = FStar_Syntax_Subst.compress e  in
                      uu____9887.FStar_Syntax_Syntax.n  in
                    (match uu____9886 with
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (uu____9904,(FStar_Util.Inr c,uu____9906),uu____9907)
                         ->
                         let uu____9954 =
                           let uu____9969 =
                             let uu____9982 =
                               let uu____9989 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                                   FStar_Pervasives_Native.None r
                                  in
                               FStar_Util.Inr uu____9989  in
                             ((lb.FStar_Syntax_Syntax.lbunivs), uu____9982)
                              in
                           FStar_Pervasives_Native.Some uu____9969  in
                         (lb, uu____9954)
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (uu____10036,(FStar_Util.Inl t,uu____10038),uu____10039)
                         ->
                         let c =
                           let uu____10087 = FStar_Options.ml_ish ()  in
                           if uu____10087
                           then FStar_Syntax_Util.ml_comp t r
                           else FStar_Syntax_Syntax.mk_Total t  in
                         let uu____10089 =
                           let uu____10104 =
                             let uu____10117 =
                               let uu____10124 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                                   FStar_Pervasives_Native.None r
                                  in
                               FStar_Util.Inr uu____10124  in
                             ((lb.FStar_Syntax_Syntax.lbunivs), uu____10117)
                              in
                           FStar_Pervasives_Native.Some uu____10104  in
                         (lb, uu____10089)
                     | uu____10169 -> (lb, FStar_Pervasives_Native.None))
                | uu____10188 -> (lb, FStar_Pervasives_Native.None))
           | uu____10207 ->
               (lb,
                 (FStar_Pervasives_Native.Some
                    ((lb.FStar_Syntax_Syntax.lbunivs),
                      (FStar_Util.Inr (lb.FStar_Syntax_Syntax.lbtyp))))))
         in
      let should_keep_lbdef c_or_t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____10261 -> failwith "Impossible!"  in
        let c_opt =
          let uu____10265 = FStar_Util.is_left c_or_t  in
          if uu____10265
          then
            let uu____10268 = FStar_All.pipe_right c_or_t FStar_Util.left  in
            FStar_Pervasives_Native.Some uu____10268
          else
            (let t = FStar_All.pipe_right c_or_t FStar_Util.right  in
             let uu____10279 = FStar_Syntax_Util.is_unit t  in
             if uu____10279
             then
               let uu____10282 = FStar_Syntax_Syntax.mk_Total t  in
               FStar_Pervasives_Native.Some uu____10282
             else
               (let uu____10284 =
                  let uu____10285 = FStar_Syntax_Subst.compress t  in
                  uu____10285.FStar_Syntax_Syntax.n  in
                match uu____10284 with
                | FStar_Syntax_Syntax.Tm_arrow (uu____10290,c) ->
                    FStar_Pervasives_Native.Some c
                | uu____10310 -> FStar_Pervasives_Native.None))
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           ((FStar_Syntax_Util.is_pure_or_ghost_comp c) ||
              (let uu____10318 = comp_effect_name1 c  in
               FStar_TypeChecker_Util.is_reifiable env uu____10318))
             &&
             (let uu____10320 =
                let uu____10321 =
                  FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
                FStar_All.pipe_right uu____10321 FStar_Syntax_Util.is_unit
                 in
              Prims.op_Negation uu____10320))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____10336 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____10355 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____10401,uu____10402,uu____10403,uu____10404,uu____10405,uu____10406)
                         ->
                         let uu____10415 = vals_of_abstract_inductive s1  in
                         FStar_List.append uu____10415 sigelts1
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____10419,uu____10420,uu____10421,uu____10422,uu____10423)
                         ->
                         ((let uu____10429 =
                             let uu____10432 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____10432  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____10429);
                          sigelts1)
                     | uu____10525 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____10532 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____10532
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____10538 =
                   let uu___107_10539 = s  in
                   let uu____10540 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___107_10539.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___107_10539.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____10540;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___107_10539.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___107_10539.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____10538])
              else
                ((let uu____10545 =
                    let uu____10558 = FStar_ST.op_Bang val_typs  in
                    (lid, uvs, t) :: uu____10558  in
                  FStar_ST.op_Colon_Equals val_typs uu____10545);
                 [])
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____10709 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____10709
            then []
            else
              (let uu____10713 = lbs  in
               match uu____10713 with
               | (flbs,slbs) ->
                   let uu____10722 =
                     FStar_List.fold_left2
                       (fun uu____10772  ->
                          fun lb  ->
                            fun lid  ->
                              match uu____10772 with
                              | (b,lbs1,typs) ->
                                  let uu____10846 =
                                    extract_lb_annotation lb lid
                                      s.FStar_Syntax_Syntax.sigrng
                                     in
                                  (match uu____10846 with
                                   | (lb1,t) ->
                                       (((FStar_Util.is_some t) && b), (lb1
                                         :: lbs1), (t :: typs))))
                       (true, [], []) slbs lids
                      in
                   (match uu____10722 with
                    | (b,lbs1,typs) ->
                        let uu____10992 =
                          ((FStar_List.rev_append lbs1 []),
                            (FStar_List.rev_append typs []))
                           in
                        (match uu____10992 with
                         | (lbs2,typs1) ->
                             let s1 =
                               let uu___108_11078 = s  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_let
                                      ((flbs, lbs2), lids));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___108_11078.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___108_11078.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___108_11078.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___108_11078.FStar_Syntax_Syntax.sigattrs)
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
                                  let uu____11093 =
                                    let uu____11098 =
                                      let uu____11099 =
                                        let uu____11100 = FStar_List.hd lids
                                           in
                                        uu____11100.FStar_Ident.str  in
                                      Prims.strcat
                                        "For extracting interfaces, abstract and irreducible defns must be annotated at the top-level: "
                                        uu____11099
                                       in
                                    (FStar_Errors.Fatal_IllTyped,
                                      uu____11098)
                                     in
                                  FStar_Errors.raise_error uu____11093
                                    s1.FStar_Syntax_Syntax.sigrng
                                else [s1])
                             else
                               (let is_lemma1 =
                                  FStar_List.existsML
                                    (fun opt  ->
                                       let uu____11131 =
                                         FStar_All.pipe_right opt
                                           FStar_Util.must
                                          in
                                       match uu____11131 with
                                       | (uu____11166,c_or_t) ->
                                           (FStar_Util.is_right c_or_t) &&
                                             (let uu____11177 =
                                                FStar_All.pipe_right c_or_t
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____11177
                                                FStar_Syntax_Util.is_lemma))
                                    typs1
                                   in
                                let vals =
                                  FStar_List.map2
                                    (fun lid  ->
                                       fun opt  ->
                                         let uu____11210 =
                                           FStar_All.pipe_right opt
                                             FStar_Util.must
                                            in
                                         val_of_lb s1 lid uu____11210) lids
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
                                          let uu____11272 =
                                            let uu____11277 =
                                              FStar_All.pipe_right opt
                                                FStar_Util.must
                                               in
                                            FStar_All.pipe_right uu____11277
                                              FStar_Pervasives_Native.snd
                                             in
                                          should_keep_lbdef uu____11272)
                                       typs1
                                      in
                                   if should_keep_defs then [s1] else vals)))))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lids,uvs,t) ->
            let uu____11337 =
              let uu___109_11338 = s  in
              let uu____11339 =
                filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___109_11338.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___109_11338.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____11339;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___109_11338.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___109_11338.FStar_Syntax_Syntax.sigattrs)
              }  in
            [uu____11337]
        | FStar_Syntax_Syntax.Sig_new_effect uu____11342 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11343 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____11344 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11345 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____11358 -> [s]  in
      let uu___110_11359 = m  in
      let uu____11360 =
        let uu____11361 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____11361  in
      {
        FStar_Syntax_Syntax.name = (uu___110_11359.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11360;
        FStar_Syntax_Syntax.exports =
          (uu___110_11359.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      (let uu____11379 = FStar_Options.debug_any ()  in
       if uu____11379
       then
         let uu____11380 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____11380
       else ());
      (let env1 =
         let uu___111_11384 = env  in
         let uu____11385 =
           let uu____11386 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____11386  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___111_11384.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___111_11384.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___111_11384.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___111_11384.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___111_11384.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___111_11384.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___111_11384.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___111_11384.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___111_11384.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___111_11384.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___111_11384.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___111_11384.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___111_11384.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___111_11384.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___111_11384.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___111_11384.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___111_11384.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___111_11384.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____11385;
           FStar_TypeChecker_Env.lax_universes =
             (uu___111_11384.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___111_11384.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___111_11384.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___111_11384.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___111_11384.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___111_11384.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___111_11384.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___111_11384.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___111_11384.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___111_11384.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___111_11384.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___111_11384.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___111_11384.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___111_11384.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___111_11384.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___111_11384.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____11387 = tc_modul env1 m  in
       match uu____11387 with
       | (m1,env2) ->
           ((let uu____11399 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____11399
             then
               let uu____11400 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____11400
             else ());
            (let uu____11403 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____11403
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
                       let uu____11434 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____11434 with
                       | (univnames1,e) ->
                           let uu___112_11441 = lb  in
                           let uu____11442 =
                             let uu____11445 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____11445 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___112_11441.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___112_11441.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___112_11441.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___112_11441.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____11442;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___112_11441.FStar_Syntax_Syntax.lbattrs)
                           }
                        in
                     let uu___113_11446 = se  in
                     let uu____11447 =
                       let uu____11448 =
                         let uu____11455 =
                           let uu____11462 = FStar_List.map update lbs  in
                           (b, uu____11462)  in
                         (uu____11455, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____11448  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____11447;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___113_11446.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___113_11446.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___113_11446.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___113_11446.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____11475 -> se  in
               let normalized_module =
                 let uu___114_11477 = m1  in
                 let uu____11478 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___114_11477.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____11478;
                   FStar_Syntax_Syntax.exports =
                     (uu___114_11477.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___114_11477.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____11479 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____11479
             else ());
            (m1, env2)))
  