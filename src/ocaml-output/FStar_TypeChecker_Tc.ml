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
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____83 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____83 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____104 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____104
         then
           let uu____105 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____105
         else ());
        (let uu____107 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____107 with
         | (t',uu____115,uu____116) ->
             ((let uu____118 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____118
               then
                 let uu____119 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____119
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
        let uu____130 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____130
  
let check_nogen :
  'Auu____135 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____135 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____155 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1
           in
        ([], uu____155)
  
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
        let fail uu____182 =
          let uu____183 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          FStar_Errors.raise_error uu____183 (FStar_Ident.range_of_lid m)  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____227)::(wp,uu____229)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____244 -> fail ())
        | uu____245 -> fail ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____252 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____252 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____278 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____278 t  in
          let open_univs_binders n_binders bs =
            let uu____288 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____288 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____296 =
            let uu____303 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____304 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____303 uu____304  in
          (match uu____296 with
           | (effect_params_un,signature_un,opening) ->
               let uu____314 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
                  in
               (match uu____314 with
                | (effect_params,env,uu____323) ->
                    let uu____324 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                       in
                    (match uu____324 with
                     | (signature,uu____330) ->
                         let ed1 =
                           let uu___63_332 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___63_332.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___63_332.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___63_332.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___63_332.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___63_332.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___63_332.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___63_332.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___63_332.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___63_332.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___63_332.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___63_332.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___63_332.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___63_332.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___63_332.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___63_332.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___63_332.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___63_332.FStar_Syntax_Syntax.actions)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____348 ->
                               let op uu____370 =
                                 match uu____370 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____390 =
                                       let uu____391 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____400 =
                                         open_univs (n_effect_params + n_us)
                                           t
                                          in
                                       FStar_Syntax_Subst.subst uu____391
                                         uu____400
                                        in
                                     (us, uu____390)
                                  in
                               let uu___64_413 = ed1  in
                               let uu____414 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____415 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____416 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____417 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____418 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____419 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____420 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____421 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____422 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____423 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____424 =
                                 let uu____425 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____425  in
                               let uu____436 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____437 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____438 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___65_446 = a  in
                                      let uu____447 =
                                        let uu____448 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____448
                                         in
                                      let uu____459 =
                                        let uu____460 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____460
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___65_446.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___65_446.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___65_446.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___65_446.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____447;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____459
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___64_413.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___64_413.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___64_413.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___64_413.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____414;
                                 FStar_Syntax_Syntax.bind_wp = uu____415;
                                 FStar_Syntax_Syntax.if_then_else = uu____416;
                                 FStar_Syntax_Syntax.ite_wp = uu____417;
                                 FStar_Syntax_Syntax.stronger = uu____418;
                                 FStar_Syntax_Syntax.close_wp = uu____419;
                                 FStar_Syntax_Syntax.assert_p = uu____420;
                                 FStar_Syntax_Syntax.assume_p = uu____421;
                                 FStar_Syntax_Syntax.null_wp = uu____422;
                                 FStar_Syntax_Syntax.trivial = uu____423;
                                 FStar_Syntax_Syntax.repr = uu____424;
                                 FStar_Syntax_Syntax.return_repr = uu____436;
                                 FStar_Syntax_Syntax.bind_repr = uu____437;
                                 FStar_Syntax_Syntax.actions = uu____438
                               }
                            in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____497 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t
                                in
                             FStar_Errors.raise_error uu____497
                               (FStar_Ident.range_of_lid mname)
                              in
                           let uu____508 =
                             let uu____509 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____509.FStar_Syntax_Syntax.n  in
                           match uu____508 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____544)::(wp,uu____546)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____561 -> fail signature1)
                           | uu____562 -> fail signature1  in
                         let uu____563 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____563 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____585 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____592 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un
                                       in
                                    (match uu____592 with
                                     | (signature1,uu____604) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____605 ->
                                    let uu____608 =
                                      let uu____613 =
                                        let uu____614 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____614)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____613
                                       in
                                    (match uu____608 with
                                     | (uu____623,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env1 =
                                let uu____626 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env uu____626
                                 in
                              ((let uu____628 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____628
                                then
                                  let uu____629 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____630 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____631 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____632 =
                                    let uu____633 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____633
                                     in
                                  let uu____634 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____629 uu____630 uu____631 uu____632
                                    uu____634
                                else ());
                               (let check_and_gen' env2 uu____650 k =
                                  match uu____650 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____664::uu____665 ->
                                           let uu____668 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____668 with
                                            | (us1,t1) ->
                                                let uu____677 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____677 with
                                                 | (us2,t2) ->
                                                     let uu____684 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k
                                                        in
                                                     let uu____685 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____685))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____690 =
                                      let uu____697 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____698 =
                                        let uu____701 =
                                          let uu____702 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____702
                                           in
                                        [uu____701]  in
                                      uu____697 :: uu____698  in
                                    let uu____703 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____690
                                      uu____703
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____707 = fresh_effect_signature ()
                                     in
                                  match uu____707 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____723 =
                                          let uu____730 =
                                            let uu____731 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____731
                                             in
                                          [uu____730]  in
                                        let uu____732 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____723
                                          uu____732
                                         in
                                      let expected_k =
                                        let uu____738 =
                                          let uu____745 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____746 =
                                            let uu____749 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____750 =
                                              let uu____753 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____754 =
                                                let uu____757 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____758 =
                                                  let uu____761 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____761]  in
                                                uu____757 :: uu____758  in
                                              uu____753 :: uu____754  in
                                            uu____749 :: uu____750  in
                                          uu____745 :: uu____746  in
                                        let uu____762 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____738
                                          uu____762
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____767 =
                                      let uu____768 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____768
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____767
                                     in
                                  let expected_k =
                                    let uu____780 =
                                      let uu____787 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____788 =
                                        let uu____791 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____792 =
                                          let uu____795 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____796 =
                                            let uu____799 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____799]  in
                                          uu____795 :: uu____796  in
                                        uu____791 :: uu____792  in
                                      uu____787 :: uu____788  in
                                    let uu____800 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____780
                                      uu____800
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____807 =
                                      let uu____814 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____815 =
                                        let uu____818 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____818]  in
                                      uu____814 :: uu____815  in
                                    let uu____819 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____807
                                      uu____819
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____823 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____823 with
                                  | (t,uu____829) ->
                                      let expected_k =
                                        let uu____833 =
                                          let uu____840 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____841 =
                                            let uu____844 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____845 =
                                              let uu____848 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____848]  in
                                            uu____844 :: uu____845  in
                                          uu____840 :: uu____841  in
                                        let uu____849 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____833
                                          uu____849
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____854 =
                                      let uu____855 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____855
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____854
                                     in
                                  let b_wp_a =
                                    let uu____867 =
                                      let uu____874 =
                                        let uu____875 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____875
                                         in
                                      [uu____874]  in
                                    let uu____876 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____867
                                      uu____876
                                     in
                                  let expected_k =
                                    let uu____882 =
                                      let uu____889 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____890 =
                                        let uu____893 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____894 =
                                          let uu____897 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____897]  in
                                        uu____893 :: uu____894  in
                                      uu____889 :: uu____890  in
                                    let uu____898 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____882
                                      uu____898
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____905 =
                                      let uu____912 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____913 =
                                        let uu____916 =
                                          let uu____917 =
                                            let uu____918 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____918
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____917
                                           in
                                        let uu____927 =
                                          let uu____930 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____930]  in
                                        uu____916 :: uu____927  in
                                      uu____912 :: uu____913  in
                                    let uu____931 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____905
                                      uu____931
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____938 =
                                      let uu____945 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____946 =
                                        let uu____949 =
                                          let uu____950 =
                                            let uu____951 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____951
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____950
                                           in
                                        let uu____960 =
                                          let uu____963 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____963]  in
                                        uu____949 :: uu____960  in
                                      uu____945 :: uu____946  in
                                    let uu____964 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____938
                                      uu____964
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____971 =
                                      let uu____978 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____978]  in
                                    let uu____979 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____971
                                      uu____979
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____983 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____983 with
                                  | (t,uu____989) ->
                                      let expected_k =
                                        let uu____993 =
                                          let uu____1000 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1001 =
                                            let uu____1004 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1004]  in
                                          uu____1000 :: uu____1001  in
                                        let uu____1005 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____993
                                          uu____1005
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1008 =
                                  let uu____1019 =
                                    let uu____1020 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1020.FStar_Syntax_Syntax.n  in
                                  match uu____1019 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1035 ->
                                      let repr =
                                        let uu____1037 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1037 with
                                        | (t,uu____1043) ->
                                            let expected_k =
                                              let uu____1047 =
                                                let uu____1054 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1055 =
                                                  let uu____1058 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1058]  in
                                                uu____1054 :: uu____1055  in
                                              let uu____1059 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1047 uu____1059
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
                                        let uu____1072 =
                                          let uu____1075 =
                                            let uu____1076 =
                                              let uu____1091 =
                                                let uu____1094 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1095 =
                                                  let uu____1098 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1098]  in
                                                uu____1094 :: uu____1095  in
                                              (repr1, uu____1091)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1076
                                             in
                                          FStar_Syntax_Syntax.mk uu____1075
                                           in
                                        uu____1072
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1113 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1113 wp  in
                                      let destruct_repr t =
                                        let uu____1126 =
                                          let uu____1127 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1127.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1126 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1138,(t1,uu____1140)::
                                             (wp,uu____1142)::[])
                                            -> (t1, wp)
                                        | uu____1185 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1196 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1196
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1197 =
                                          fresh_effect_signature ()  in
                                        match uu____1197 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1213 =
                                                let uu____1220 =
                                                  let uu____1221 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1221
                                                   in
                                                [uu____1220]  in
                                              let uu____1222 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1213 uu____1222
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
                                              let uu____1228 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1228
                                               in
                                            let wp_g_x =
                                              let uu____1232 =
                                                let uu____1233 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1234 =
                                                  let uu____1235 =
                                                    let uu____1236 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1236
                                                     in
                                                  [uu____1235]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1233 uu____1234
                                                 in
                                              uu____1232
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1245 =
                                                  let uu____1246 =
                                                    let uu____1247 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1247
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1256 =
                                                    let uu____1257 =
                                                      let uu____1260 =
                                                        let uu____1263 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1264 =
                                                          let uu____1267 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1268 =
                                                            let uu____1271 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1272 =
                                                              let uu____1275
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1275]
                                                               in
                                                            uu____1271 ::
                                                              uu____1272
                                                             in
                                                          uu____1267 ::
                                                            uu____1268
                                                           in
                                                        uu____1263 ::
                                                          uu____1264
                                                         in
                                                      r :: uu____1260  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1257
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1246 uu____1256
                                                   in
                                                uu____1245
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let expected_k =
                                              let uu____1281 =
                                                let uu____1288 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1289 =
                                                  let uu____1292 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____1293 =
                                                    let uu____1296 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1297 =
                                                      let uu____1300 =
                                                        let uu____1301 =
                                                          let uu____1302 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1302
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1301
                                                         in
                                                      let uu____1303 =
                                                        let uu____1306 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1307 =
                                                          let uu____1310 =
                                                            let uu____1311 =
                                                              let uu____1312
                                                                =
                                                                let uu____1319
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1319]
                                                                 in
                                                              let uu____1320
                                                                =
                                                                let uu____1323
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1323
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1312
                                                                uu____1320
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1311
                                                             in
                                                          [uu____1310]  in
                                                        uu____1306 ::
                                                          uu____1307
                                                         in
                                                      uu____1300 ::
                                                        uu____1303
                                                       in
                                                    uu____1296 :: uu____1297
                                                     in
                                                  uu____1292 :: uu____1293
                                                   in
                                                uu____1288 :: uu____1289  in
                                              let uu____1324 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1281 uu____1324
                                               in
                                            let uu____1327 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k
                                               in
                                            (match uu____1327 with
                                             | (expected_k1,uu____1335,uu____1336)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env3 =
                                                   let uu___66_1341 = env2
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qname_and_index
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.qname_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___66_1341.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1351 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1351
                                           in
                                        let res =
                                          let wp =
                                            let uu____1358 =
                                              let uu____1359 =
                                                let uu____1360 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1360
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1369 =
                                                let uu____1370 =
                                                  let uu____1373 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1374 =
                                                    let uu____1377 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1377]  in
                                                  uu____1373 :: uu____1374
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1370
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1359 uu____1369
                                               in
                                            uu____1358
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1383 =
                                            let uu____1390 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1391 =
                                              let uu____1394 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1394]  in
                                            uu____1390 :: uu____1391  in
                                          let uu____1395 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1383
                                            uu____1395
                                           in
                                        let uu____1398 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k
                                           in
                                        match uu____1398 with
                                        | (expected_k1,uu____1412,uu____1413)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1417 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1417 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1438 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____1463 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1
                                              act.FStar_Syntax_Syntax.action_typ
                                             in
                                          match uu____1463 with
                                          | (act_typ,uu____1471,g_t) ->
                                              let env' =
                                                let uu___67_1474 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___67_1474.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___67_1474.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1476 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1476
                                                then
                                                  let uu____1477 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn
                                                     in
                                                  let uu____1478 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ
                                                     in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1477 uu____1478
                                                else ());
                                               (let uu____1480 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn
                                                   in
                                                match uu____1480 with
                                                | (act_defn,uu____1488,g_a)
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
                                                    let uu____1492 =
                                                      let act_typ2 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ1
                                                         in
                                                      match act_typ2.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1520 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c
                                                             in
                                                          (match uu____1520
                                                           with
                                                           | (bs1,uu____1530)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let k =
                                                                 let uu____1537
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1537
                                                                  in
                                                               let uu____1540
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k
                                                                  in
                                                               (match uu____1540
                                                                with
                                                                | (k1,uu____1552,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1554 ->
                                                          let uu____1555 =
                                                            let uu____1560 =
                                                              let uu____1561
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ2
                                                                 in
                                                              let uu____1562
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ2
                                                                 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1561
                                                                uu____1562
                                                               in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1560)
                                                             in
                                                          FStar_Errors.raise_error
                                                            uu____1555
                                                            act_defn1.FStar_Syntax_Syntax.pos
                                                       in
                                                    (match uu____1492 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ1
                                                             expected_k
                                                            in
                                                         ((let uu____1571 =
                                                             let uu____1572 =
                                                               let uu____1573
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1573
                                                                in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1572
                                                              in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1571);
                                                          (let act_typ2 =
                                                             let uu____1577 =
                                                               let uu____1578
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1578.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1577
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1601
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1601
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1610
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1610
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1632
                                                                    =
                                                                    let uu____1633
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1633]
                                                                     in
                                                                    let uu____1634
                                                                    =
                                                                    let uu____1643
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1643]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1632;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1634;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1644
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1644))
                                                             | uu____1647 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1650 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1
                                                              in
                                                           match uu____1650
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
                                                               let uu___68_1659
                                                                 = act  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___68_1659.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___68_1659.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___68_1659.FStar_Syntax_Syntax.action_params);
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
                                match uu____1008 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1683 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1683
                                       in
                                    let uu____1686 =
                                      let uu____1693 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1693 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1714 ->
                                               let uu____1717 =
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
                                               if uu____1717
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1731 =
                                                    let uu____1736 =
                                                      let uu____1737 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1738 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1737 uu____1738
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1736)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1731
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1686 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1752 =
                                             let uu____1757 =
                                               let uu____1758 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1758.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1757)  in
                                           match uu____1752 with
                                           | ([],uu____1761) -> t
                                           | (uu____1772,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1773,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1791 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1804 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1804
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1809 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1811 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1811))
                                                && (m <> n1)
                                               in
                                            if uu____1809
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____1827 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____1834 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____1835 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1827 uu____1834
                                                  uu____1835
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____1843 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____1843 with
                                           | (univs2,defn) ->
                                               let uu____1850 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____1850 with
                                                | (univs',typ) ->
                                                    let uu___69_1860 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___69_1860.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___69_1860.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___69_1860.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___70_1865 = ed2  in
                                           let uu____1866 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____1867 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____1868 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____1869 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____1870 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____1871 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____1872 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____1873 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____1874 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____1875 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____1876 =
                                             let uu____1877 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____1877
                                              in
                                           let uu____1888 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____1889 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____1890 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___70_1865.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___70_1865.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____1866;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____1867;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____1868;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____1869;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____1870;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____1871;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____1872;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____1873;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____1874;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____1875;
                                             FStar_Syntax_Syntax.repr =
                                               uu____1876;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____1888;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____1889;
                                             FStar_Syntax_Syntax.actions =
                                               uu____1890
                                           }  in
                                         ((let uu____1894 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____1894
                                           then
                                             let uu____1895 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____1895
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
      let uu____1913 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____1913 with
      | (effect_binders_un,signature_un) ->
          let uu____1930 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____1930 with
           | (effect_binders,env1,uu____1949) ->
               let uu____1950 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____1950 with
                | (signature,uu____1966) ->
                    let raise_error1 a uu____1977 =
                      match uu____1977 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2003  ->
                           match uu____2003 with
                           | (bv,qual) ->
                               let uu____2014 =
                                 let uu___71_2015 = bv  in
                                 let uu____2016 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___71_2015.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___71_2015.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2016
                                 }  in
                               (uu____2014, qual)) effect_binders
                       in
                    let uu____2019 =
                      let uu____2026 =
                        let uu____2027 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2027.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2026 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2037)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2059 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2019 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2077 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2077
                           then
                             let uu____2078 =
                               let uu____2081 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2081  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2078
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2115 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2115 with
                           | (t2,comp,uu____2128) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2135 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2135 with
                          | (repr,_comp) ->
                              ((let uu____2157 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2157
                                then
                                  let uu____2158 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2158
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
                                  let uu____2164 =
                                    let uu____2165 =
                                      let uu____2166 =
                                        let uu____2181 =
                                          let uu____2188 =
                                            let uu____2193 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2194 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2193, uu____2194)  in
                                          [uu____2188]  in
                                        (wp_type1, uu____2181)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2166
                                       in
                                    mk1 uu____2165  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2164
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2219 =
                                      let uu____2224 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2224)  in
                                    let uu____2225 =
                                      let uu____2232 =
                                        let uu____2233 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2233
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2232]  in
                                    uu____2219 :: uu____2225  in
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
                                  let uu____2296 = item  in
                                  match uu____2296 with
                                  | (u_item,item1) ->
                                      let uu____2317 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2317 with
                                       | (item2,item_comp) ->
                                           ((let uu____2333 =
                                               let uu____2334 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2334
                                                in
                                             if uu____2333
                                             then
                                               let uu____2335 =
                                                 let uu____2340 =
                                                   let uu____2341 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2342 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2341 uu____2342
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2340)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2335
                                             else ());
                                            (let uu____2344 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2344 with
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
                                let uu____2364 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2364 with
                                | (dmff_env1,uu____2388,bind_wp,bind_elab) ->
                                    let uu____2391 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2391 with
                                     | (dmff_env2,uu____2415,return_wp,return_elab)
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
                                           let uu____2422 =
                                             let uu____2423 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2423.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2422 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2467 =
                                                       let uu____2482 =
                                                         let uu____2487 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2487
                                                          in
                                                       match uu____2482 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2551 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2467 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2590 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2590
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2607 =
                                                               let uu____2608
                                                                 =
                                                                 let uu____2623
                                                                   =
                                                                   let uu____2630
                                                                    =
                                                                    let uu____2635
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2636
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2635,
                                                                    uu____2636)
                                                                     in
                                                                   [uu____2630]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2623)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2608
                                                                in
                                                             mk1 uu____2607
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2651 =
                                                           let uu____2660 =
                                                             let uu____2661 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2661
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2660
                                                            in
                                                         (match uu____2651
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a415 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2680
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2682
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2682
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
                                                                    let uu____2688
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
                                                                    uu____2688
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
                                                                  let uu____2715
                                                                    =
                                                                    let uu____2716
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2717
                                                                    =
                                                                    let uu____2718
                                                                    =
                                                                    let uu____2725
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2725,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2718]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2716
                                                                    uu____2717
                                                                     in
                                                                  uu____2715
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2750
                                                                  =
                                                                  let uu____2751
                                                                    =
                                                                    let uu____2758
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2758]
                                                                     in
                                                                  b11 ::
                                                                    uu____2751
                                                                   in
                                                                let uu____2763
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2750
                                                                  uu____2763
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2764 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let return_wp1 =
                                           let uu____2766 =
                                             let uu____2767 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2767.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2766 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2811 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2811
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____2824 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let bind_wp1 =
                                           let uu____2826 =
                                             let uu____2827 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____2827.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2826 with
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
                                                     let uu____2854 =
                                                       let uu____2855 =
                                                         let uu____2858 =
                                                           let uu____2859 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____2859
                                                            in
                                                         [uu____2858]  in
                                                       FStar_List.append
                                                         uu____2855 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____2854 body what)
                                              | uu____2860 ->
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
                                             (let uu____2878 =
                                                let uu____2879 =
                                                  let uu____2880 =
                                                    let uu____2895 =
                                                      let uu____2896 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2896
                                                       in
                                                    (t, uu____2895)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2880
                                                   in
                                                mk1 uu____2879  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2878)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2926 = f a2  in
                                               [uu____2926]
                                           | x::xs ->
                                               let uu____2931 =
                                                 apply_last1 f xs  in
                                               x :: uu____2931
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
                                           let uu____2951 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____2951 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____2981 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____2981
                                                 then
                                                   let uu____2982 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2982
                                                 else ());
                                                (let uu____2984 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2984))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____2993 =
                                                 let uu____2998 = mk_lid name
                                                    in
                                                 let uu____2999 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2998 uu____2999
                                                  in
                                               (match uu____2993 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3003 =
                                                        let uu____3006 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3006
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3003);
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
                                          (let uu____3103 =
                                             let uu____3106 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3107 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3106 :: uu____3107  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3103);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3205 =
                                               let uu____3208 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3209 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3208 :: uu____3209  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3205);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3304 =
                                                FStar_List.fold_left
                                                  (fun uu____3344  ->
                                                     fun action  ->
                                                       match uu____3344 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3365 =
                                                             let uu____3372 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3372
                                                               params_un
                                                              in
                                                           (match uu____3365
                                                            with
                                                            | (action_params,env',uu____3381)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3401
                                                                     ->
                                                                    match uu____3401
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3412
                                                                    =
                                                                    let uu___72_3413
                                                                    = bv  in
                                                                    let uu____3414
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___72_3413.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___72_3413.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3414
                                                                    }  in
                                                                    (uu____3412,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3418
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3418
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
                                                                    uu____3448
                                                                    ->
                                                                    let uu____3449
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3449
                                                                     in
                                                                    ((
                                                                    let uu____3453
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3453
                                                                    then
                                                                    let uu____3454
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3455
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3456
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3457
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3454
                                                                    uu____3455
                                                                    uu____3456
                                                                    uu____3457
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
                                                                    let uu____3461
                                                                    =
                                                                    let uu____3464
                                                                    =
                                                                    let uu___73_3465
                                                                    = action
                                                                     in
                                                                    let uu____3466
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3467
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___73_3465.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___73_3465.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___73_3465.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3466;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3467
                                                                    }  in
                                                                    uu____3464
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3461))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3304 with
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
                                                      let uu____3500 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3501 =
                                                        let uu____3504 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3504]  in
                                                      uu____3500 ::
                                                        uu____3501
                                                       in
                                                    let uu____3505 =
                                                      let uu____3506 =
                                                        let uu____3507 =
                                                          let uu____3508 =
                                                            let uu____3523 =
                                                              let uu____3530
                                                                =
                                                                let uu____3535
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3536
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3535,
                                                                  uu____3536)
                                                                 in
                                                              [uu____3530]
                                                               in
                                                            (repr,
                                                              uu____3523)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3508
                                                           in
                                                        mk1 uu____3507  in
                                                      let uu____3551 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3506
                                                        uu____3551
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3505
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3554 =
                                                    let uu____3561 =
                                                      let uu____3562 =
                                                        let uu____3565 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3565
                                                         in
                                                      uu____3562.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3561 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3575)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3604
                                                                =
                                                                let uu____3621
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3621
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3679
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3604
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3729
                                                                    =
                                                                    let uu____3730
                                                                    =
                                                                    let uu____3733
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3733
                                                                     in
                                                                    uu____3730.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3729
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3758
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3758
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3771
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3796
                                                                     ->
                                                                    match uu____3796
                                                                    with
                                                                    | 
                                                                    (bv,uu____3802)
                                                                    ->
                                                                    let uu____3803
                                                                    =
                                                                    let uu____3804
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3804
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3803
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3771
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
                                                                    let uu____3868
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3868
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3873
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3881
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3881
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____3886
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____3889
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____3886,
                                                                    uu____3889)))
                                                                    | 
                                                                    uu____3896
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3897
                                                                    =
                                                                    let uu____3902
                                                                    =
                                                                    let uu____3903
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3903
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3902)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____3897)))
                                                       | uu____3904 ->
                                                           Obj.repr
                                                             (let uu____3905
                                                                =
                                                                let uu____3910
                                                                  =
                                                                  let uu____3911
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____3911
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____3910)
                                                                 in
                                                              raise_error1 ()
                                                                uu____3905))
                                                     in
                                                  (match uu____3554 with
                                                   | (pre,post) ->
                                                       ((let uu____3929 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____3931 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____3933 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___74_3935 =
                                                             ed  in
                                                           let uu____3936 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____3937 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____3938 =
                                                             let uu____3939 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____3939)
                                                              in
                                                           let uu____3946 =
                                                             let uu____3947 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____3947)
                                                              in
                                                           let uu____3954 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____3955 =
                                                             let uu____3956 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____3956)
                                                              in
                                                           let uu____3963 =
                                                             let uu____3964 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____3964)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3936;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3937;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3938;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3946;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___74_3935.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3954;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3955;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3963;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____3971 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____3971
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3989
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____3989
                                                               then
                                                                 let uu____3990
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____3990
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
                                                                    let uu____4002
                                                                    =
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4014
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4014)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4005
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
                                                                    uu____4002;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4029
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4029
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4031
                                                                 =
                                                                 let uu____4034
                                                                   =
                                                                   let uu____4037
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4037
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4034
                                                                   sigelts'
                                                                  in
                                                               (uu____4031,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4094 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4094 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4127 = FStar_List.hd ses  in
            uu____4127.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4132 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4137,uu____4138);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4140;
               FStar_Syntax_Syntax.sigattrs = uu____4141;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4145);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4147;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4148;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4152);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4154;
                 FStar_Syntax_Syntax.sigattrs = uu____4155;_}::[]
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
                 let uu____4220 =
                   let uu____4223 =
                     let uu____4224 =
                       let uu____4231 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4231, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4224  in
                   FStar_Syntax_Syntax.mk uu____4223  in
                 uu____4220 FStar_Pervasives_Native.None r1  in
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
                   let uu____4249 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4249
                    in
                 let hd1 =
                   let uu____4251 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4251
                    in
                 let tl1 =
                   let uu____4253 =
                     let uu____4254 =
                       let uu____4257 =
                         let uu____4258 =
                           let uu____4265 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4265, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4258  in
                       FStar_Syntax_Syntax.mk uu____4257  in
                     uu____4254 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4253
                    in
                 let res =
                   let uu____4274 =
                     let uu____4277 =
                       let uu____4278 =
                         let uu____4285 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4285,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4278  in
                     FStar_Syntax_Syntax.mk uu____4277  in
                   uu____4274 FStar_Pervasives_Native.None r2  in
                 let uu____4291 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4291
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
               let uu____4330 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4330;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4335 ->
               let err_msg =
                 let uu____4339 =
                   let uu____4340 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4340  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4339
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
            let uu____4365 = FStar_Syntax_Util.type_u ()  in
            match uu____4365 with
            | (k,uu____4371) ->
                let phi1 =
                  let uu____4373 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____4373
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4375 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1  in
                  match uu____4375 with
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
          let uu____4417 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4417 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4450 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas
                   in
                FStar_All.pipe_right uu____4450 FStar_List.flatten  in
              ((let uu____4464 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____4464
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
                          let uu____4475 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4485,uu____4486,uu____4487,uu____4488,uu____4489)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4498 -> failwith "Impossible!"  in
                          match uu____4475 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4509 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4513,uu____4514,uu____4515,uu____4516,uu____4517)
                        -> lid
                    | uu____4526 -> failwith "Impossible"  in
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
                  let uu____4544 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4544
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
                     let uu____4567 =
                       let uu____4570 =
                         let uu____4571 =
                           FStar_TypeChecker_Env.get_range env1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4571;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       uu____4570 :: ses1  in
                     (uu____4567, data_ops_ses))
                   in
                (let uu____4581 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4615 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4640 ->
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
           let uu____4692 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4692 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4730 = cps_and_elaborate env1 ne  in
           (match uu____4730 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___75_4767 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___75_4767.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___75_4767.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___75_4767.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___75_4767.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___76_4769 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___76_4769.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___76_4769.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___76_4769.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___76_4769.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___77_4777 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___77_4777.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___77_4777.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___77_4777.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___77_4777.FStar_Syntax_Syntax.sigattrs)
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
           let uu____4785 =
             let uu____4792 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4792
              in
           (match uu____4785 with
            | (a,wp_a_src) ->
                let uu____4807 =
                  let uu____4814 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4814
                   in
                (match uu____4807 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4830 =
                         let uu____4833 =
                           let uu____4834 =
                             let uu____4841 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____4841)  in
                           FStar_Syntax_Syntax.NT uu____4834  in
                         [uu____4833]  in
                       FStar_Syntax_Subst.subst uu____4830 wp_b_tgt  in
                     let expected_k =
                       let uu____4845 =
                         let uu____4852 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____4853 =
                           let uu____4856 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____4856]  in
                         uu____4852 :: uu____4853  in
                       let uu____4857 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____4845 uu____4857  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4878 =
                           let uu____4883 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____4883)
                            in
                         let uu____4884 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____4878 uu____4884  in
                       let uu____4887 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____4887 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____4919 =
                             let uu____4920 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____4920  in
                           if uu____4919
                           then no_reify eff_name
                           else
                             (let uu____4926 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____4927 =
                                let uu____4930 =
                                  let uu____4931 =
                                    let uu____4946 =
                                      let uu____4949 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____4950 =
                                        let uu____4953 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____4953]  in
                                      uu____4949 :: uu____4950  in
                                    (repr, uu____4946)  in
                                  FStar_Syntax_Syntax.Tm_app uu____4931  in
                                FStar_Syntax_Syntax.mk uu____4930  in
                              uu____4927 FStar_Pervasives_Native.None
                                uu____4926)
                        in
                     let uu____4959 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____4987,lift_wp)) ->
                           let uu____5011 =
                             check_and_gen env1 lift_wp expected_k  in
                           (lift, uu____5011)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5037 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5037
                             then
                               let uu____5038 =
                                 FStar_Syntax_Print.term_to_string lift  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5038
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5041 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift  in
                             match uu____5041 with
                             | (lift1,comp,uu____5056) ->
                                 let uu____5057 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1
                                    in
                                 (match uu____5057 with
                                  | (uu____5070,lift_wp,lift_elab) ->
                                      let uu____5073 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5074 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____4959 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___78_5115 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___78_5115.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___78_5115.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___78_5115.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___78_5115.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___78_5115.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___78_5115.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___78_5115.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___78_5115.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___78_5115.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___78_5115.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___78_5115.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___78_5115.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___78_5115.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___78_5115.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___78_5115.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___78_5115.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___78_5115.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___78_5115.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___78_5115.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___78_5115.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___78_5115.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___78_5115.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___78_5115.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___78_5115.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___78_5115.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___78_5115.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___78_5115.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___78_5115.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___78_5115.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___78_5115.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___78_5115.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___78_5115.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___78_5115.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___78_5115.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5121,lift1)
                                ->
                                let uu____5133 =
                                  let uu____5140 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5140
                                   in
                                (match uu____5133 with
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
                                         let uu____5164 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5165 =
                                           let uu____5168 =
                                             let uu____5169 =
                                               let uu____5184 =
                                                 let uu____5187 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5188 =
                                                   let uu____5191 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5191]  in
                                                 uu____5187 :: uu____5188  in
                                               (lift_wp1, uu____5184)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5169
                                              in
                                           FStar_Syntax_Syntax.mk uu____5168
                                            in
                                         uu____5165
                                           FStar_Pervasives_Native.None
                                           uu____5164
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5200 =
                                         let uu____5207 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5208 =
                                           let uu____5211 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5212 =
                                             let uu____5215 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5215]  in
                                           uu____5211 :: uu____5212  in
                                         uu____5207 :: uu____5208  in
                                       let uu____5216 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5200
                                         uu____5216
                                        in
                                     let uu____5219 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5219 with
                                      | (expected_k2,uu____5229,uu____5230)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift2))
                             in
                          let sub2 =
                            let uu___79_5233 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___79_5233.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___79_5233.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___80_5235 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___80_5235.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___80_5235.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___80_5235.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___80_5235.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____5254 = FStar_Syntax_Subst.open_comp tps c  in
           (match uu____5254 with
            | (tps1,c1) ->
                let uu____5269 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1  in
                (match uu____5269 with
                 | (tps2,env3,us) ->
                     let uu____5287 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1  in
                     (match uu____5287 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2
                               in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2
                               in
                            let uu____5308 =
                              let uu____5309 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r
                                 in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5309
                               in
                            match uu____5308 with
                            | (uvs1,t) ->
                                let uu____5324 =
                                  let uu____5337 =
                                    let uu____5342 =
                                      let uu____5343 =
                                        FStar_Syntax_Subst.compress t  in
                                      uu____5343.FStar_Syntax_Syntax.n  in
                                    (tps3, uu____5342)  in
                                  match uu____5337 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5358,c4)) -> ([], c4)
                                  | (uu____5398,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5425 ->
                                      failwith "Impossible (t is an arrow)"
                                   in
                                (match uu____5324 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5469 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t
                                            in
                                         match uu____5469 with
                                         | (uu____5474,t1) ->
                                             let uu____5476 =
                                               let uu____5481 =
                                                 let uu____5482 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     lid
                                                    in
                                                 let uu____5483 =
                                                   FStar_All.pipe_right
                                                     (FStar_List.length uvs1)
                                                     FStar_Util.string_of_int
                                                    in
                                                 let uu____5484 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 FStar_Util.format3
                                                   "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                   uu____5482 uu____5483
                                                   uu____5484
                                                  in
                                               (FStar_Errors.Fatal_TooManyUniverse,
                                                 uu____5481)
                                                in
                                             FStar_Errors.raise_error
                                               uu____5476 r)
                                      else ();
                                      (let se1 =
                                         let uu___81_5487 = se  in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags1));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___81_5487.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___81_5487.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___81_5487.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___81_5487.FStar_Syntax_Syntax.sigattrs)
                                         }  in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5504,uu____5505,uu____5506) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5510  ->
                   match uu___56_5510 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5511 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5516,uu____5517) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5525  ->
                   match uu___56_5525 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5526 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5536 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5536
             then
               let uu____5537 =
                 let uu____5542 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid)
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5542)
                  in
               FStar_Errors.raise_error uu____5537 r
             else ());
            (let uu____5544 =
               if uvs = []
               then
                 let uu____5545 =
                   let uu____5546 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____5546  in
                 check_and_gen env2 t uu____5545
               else
                 (let uu____5552 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____5552 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5560 =
                          let uu____5561 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____5561  in
                        tc_check_trivial_guard env2 t1 uu____5560  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____5567 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____5567))
                in
             match uu____5544 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___82_5583 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___82_5583.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___82_5583.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___82_5583.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___82_5583.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5593 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____5593 with
            | (uu____5606,phi1) ->
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
           let uu____5616 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____5616 with
            | (e1,c,g1) ->
                let uu____5634 =
                  let uu____5641 =
                    let uu____5644 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____5644  in
                  let uu____5645 =
                    let uu____5650 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____5650)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5641 uu____5645
                   in
                (match uu____5634 with
                 | (e2,uu____5660,g) ->
                     ((let uu____5663 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5663);
                      (let se1 =
                         let uu___83_5665 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___83_5665.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___83_5665.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___83_5665.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___83_5665.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5716 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____5716
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5724 =
                      let uu____5729 =
                        let uu____5730 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____5731 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____5732 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____5730 uu____5731 uu____5732
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____5729)
                       in
                    FStar_Errors.raise_error uu____5724 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____5758 =
                   let uu____5759 = FStar_Syntax_Subst.compress def  in
                   uu____5759.FStar_Syntax_Syntax.n  in
                 match uu____5758 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5769,uu____5770)
                     -> binders
                 | uu____5791 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5801;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5879) -> val_bs1
                     | (uu____5902,[]) -> val_bs1
                     | ((body_bv,uu____5926)::bt,(val_bv,aqual)::vt) ->
                         let uu____5963 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____5979) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___84_5981 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___85_5984 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___85_5984.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___84_5981.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___84_5981.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____5963
                      in
                   let uu____5985 =
                     let uu____5988 =
                       let uu____5989 =
                         let uu____6002 = rename_binders1 def_bs val_bs  in
                         (uu____6002, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____5989  in
                     FStar_Syntax_Syntax.mk uu____5988  in
                   uu____5985 FStar_Pervasives_Native.None r1
               | uu____6020 -> typ1  in
             let uu___86_6021 = lb  in
             let uu____6022 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___86_6021.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___86_6021.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6022;
               FStar_Syntax_Syntax.lbeff =
                 (uu___86_6021.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___86_6021.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___86_6021.FStar_Syntax_Syntax.lbattrs)
             }  in
           let uu____6025 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6076  ->
                     fun lb  ->
                       match uu____6076 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6118 =
                             let uu____6129 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6129 with
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
                                   | uu____6214 ->
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
                                  (let uu____6257 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def)
                                      in
                                   (false, uu____6257, quals_opt1)))
                              in
                           (match uu____6118 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6025 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6351 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___57_6355  ->
                                match uu___57_6355 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6356 -> false))
                         in
                      if uu____6351
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6366 =
                    let uu____6369 =
                      let uu____6370 =
                        let uu____6383 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6383)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6370  in
                    FStar_Syntax_Syntax.mk uu____6369  in
                  uu____6366 FStar_Pervasives_Native.None r  in
                let uu____6401 =
                  let uu____6412 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___87_6421 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___87_6421.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___87_6421.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___87_6421.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___87_6421.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___87_6421.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___87_6421.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___87_6421.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___87_6421.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___87_6421.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___87_6421.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___87_6421.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___87_6421.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___87_6421.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___87_6421.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___87_6421.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___87_6421.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___87_6421.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___87_6421.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___87_6421.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___87_6421.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___87_6421.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___87_6421.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___87_6421.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___87_6421.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___87_6421.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___87_6421.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___87_6421.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___87_6421.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___87_6421.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___87_6421.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___87_6421.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___87_6421.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___87_6421.FStar_TypeChecker_Env.dep_graph)
                       }) e
                     in
                  match uu____6412 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6434;
                       FStar_Syntax_Syntax.vars = uu____6435;_},uu____6436,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6465 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6465)  in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6483,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6488 -> quals  in
                      ((let uu___88_6496 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___88_6496.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___88_6496.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___88_6496.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6505 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6401 with
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
                      (let uu____6554 = log env2  in
                       if uu____6554
                       then
                         let uu____6555 =
                           let uu____6556 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6571 =
                                         let uu____6580 =
                                           let uu____6581 =
                                             let uu____6584 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____6584.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____6581.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6580
                                          in
                                       match uu____6571 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6591 -> false  in
                                     if should_log
                                     then
                                       let uu____6600 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____6601 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6600 uu____6601
                                     else ""))
                              in
                           FStar_All.pipe_right uu____6556
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____6555
                       else ());
                      ([se1], [])))))
  
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
             (fun uu___58_6647  ->
                match uu___58_6647 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____6648 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____6654) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____6660 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____6669 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____6674 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____6699 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6723) ->
          let uu____6732 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____6732
          then
            let for_export_bundle se1 uu____6763 =
              match uu____6763 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____6802,uu____6803) ->
                       let dec =
                         let uu___89_6813 = se1  in
                         let uu____6814 =
                           let uu____6815 =
                             let uu____6822 =
                               let uu____6825 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____6825  in
                             (l, us, uu____6822)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____6815  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____6814;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___89_6813.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___89_6813.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___89_6813.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____6837,uu____6838,uu____6839) ->
                       let dec =
                         let uu___90_6845 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___90_6845.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___90_6845.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___90_6845.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____6850 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____6872,uu____6873,uu____6874) ->
          let uu____6875 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____6875 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____6896 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____6896
          then
            ([(let uu___91_6912 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___91_6912.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___91_6912.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___91_6912.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____6914 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___59_6918  ->
                       match uu___59_6918 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____6919 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____6924 -> true
                       | uu____6925 -> false))
                in
             if uu____6914 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____6943 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____6948 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6953 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____6958 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6963 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____6981) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____6998 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____6998
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
          let uu____7029 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7029
          then
            let uu____7038 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___92_7051 = se  in
                      let uu____7052 =
                        let uu____7053 =
                          let uu____7060 =
                            let uu____7061 =
                              let uu____7064 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7064.FStar_Syntax_Syntax.fv_name  in
                            uu____7061.FStar_Syntax_Syntax.v  in
                          (uu____7060, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7053  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7052;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___92_7051.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___92_7051.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___92_7051.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7038, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7084 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7101 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7116) ->
          let env1 =
            let uu____7120 = FStar_Options.using_facts_from ()  in
            FStar_TypeChecker_Env.set_proof_ns uu____7120 env  in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7122 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7123 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7133 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7133) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7134,uu____7135,uu____7136) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7140  ->
                  match uu___60_7140 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7141 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7142,uu____7143) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7151  ->
                  match uu___60_7151 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7152 -> false))
          -> env
      | uu____7153 -> FStar_TypeChecker_Env.push_sigelt env se
  
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
      let rec process_one_decl uu____7213 se =
        match uu____7213 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7266 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7266
              then
                let uu____7267 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7267
              else ());
             (let uu____7269 = tc_decl env1 se  in
              match uu____7269 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7319 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____7319
                             then
                               let uu____7320 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7320
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
                    (let uu____7343 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____7343
                     then
                       let uu____7344 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7350 =
                                  let uu____7351 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____7351 "\n"  in
                                Prims.strcat s uu____7350) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____7344
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7356 =
                       if dont_use_exports
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____7399 se1 =
                            match uu____7399 with
                            | (exports1,hidden1) ->
                                let uu____7427 = for_export hidden1 se1  in
                                (match uu____7427 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____7356 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___93_7506 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___93_7506.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___93_7506.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___93_7506.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___93_7506.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____7584 = acc  in
        match uu____7584 with
        | (uu____7619,uu____7620,env1,uu____7622) ->
            let uu____7635 =
              FStar_Util.record_time
                (fun uu____7681  -> process_one_decl acc se)
               in
            (match uu____7635 with
             | (r,ms_elapsed) ->
                 ((let uu____7745 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____7745
                   then
                     let uu____7746 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____7747 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____7746 uu____7747
                   else ());
                  r))
         in
      let uu____7749 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____7749 with
      | (ses1,exports,env1,uu____7797) ->
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
        (let uu____7837 = FStar_Options.debug_any ()  in
         if uu____7837
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
           let uu___94_7843 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___94_7843.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___94_7843.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___94_7843.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___94_7843.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___94_7843.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___94_7843.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___94_7843.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___94_7843.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___94_7843.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___94_7843.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___94_7843.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___94_7843.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___94_7843.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___94_7843.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___94_7843.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___94_7843.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___94_7843.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___94_7843.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___94_7843.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___94_7843.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___94_7843.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___94_7843.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___94_7843.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___94_7843.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___94_7843.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___94_7843.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___94_7843.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___94_7843.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___94_7843.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___94_7843.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___94_7843.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___94_7843.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___94_7843.FStar_TypeChecker_Env.dep_graph)
           }  in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name
             in
          let uu____7847 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations  in
          match uu____7847 with
          | (ses,exports,env3) ->
              ((let uu___95_7880 = modul  in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___95_7880.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___95_7880.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___95_7880.FStar_Syntax_Syntax.is_interface)
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
        let uu____7902 = tc_decls env decls  in
        match uu____7902 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___96_7933 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___96_7933.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___96_7933.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___96_7933.FStar_Syntax_Syntax.is_interface)
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
          let uu___97_7950 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___97_7950.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___97_7950.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___97_7950.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___97_7950.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___97_7950.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___97_7950.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___97_7950.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___97_7950.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___97_7950.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___97_7950.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___97_7950.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___97_7950.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___97_7950.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___97_7950.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___97_7950.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___97_7950.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___97_7950.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___97_7950.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___97_7950.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___97_7950.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___97_7950.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___97_7950.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___97_7950.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___97_7950.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___97_7950.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___97_7950.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___97_7950.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___97_7950.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___97_7950.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___97_7950.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___97_7950.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___97_7950.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term1 lid univs1 t =
          let uu____7961 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____7961 with
          | (univs2,t1) ->
              ((let uu____7969 =
                  let uu____7970 =
                    let uu____7973 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____7973  in
                  FStar_All.pipe_left uu____7970
                    (FStar_Options.Other "Exports")
                   in
                if uu____7969
                then
                  let uu____7974 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____7975 =
                    let uu____7976 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____7976
                      (FStar_String.concat ", ")
                     in
                  let uu____7985 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____7974 uu____7975 uu____7985
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____7988 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____7988 FStar_Pervasives.ignore))
           in
        let check_term2 lid univs1 t =
          (let uu____8012 =
             let uu____8013 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8014 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8013 uu____8014
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8012);
          check_term1 lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8021) ->
              let uu____8030 =
                let uu____8031 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8031  in
              if uu____8030
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8041,uu____8042) ->
              let t =
                let uu____8054 =
                  let uu____8057 =
                    let uu____8058 =
                      let uu____8071 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8071)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8058  in
                  FStar_Syntax_Syntax.mk uu____8057  in
                uu____8054 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8078,uu____8079,uu____8080) ->
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8088 =
                let uu____8089 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8089  in
              if uu____8088 then check_term2 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8093,lbs),uu____8095) ->
              let uu____8110 =
                let uu____8111 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8111  in
              if uu____8110
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        check_term2
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags1) ->
              let uu____8130 =
                let uu____8131 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8131  in
              if uu____8130
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term2 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8138 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8139 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8146 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8147 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8148 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8149 -> ()  in
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
              let uu___98_8168 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___98_8168.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (uu___98_8168.FStar_Syntax_Syntax.declarations);
                FStar_Syntax_Syntax.exports =
                  (modul.FStar_Syntax_Syntax.declarations);
                FStar_Syntax_Syntax.is_interface =
                  (uu___98_8168.FStar_Syntax_Syntax.is_interface)
              }
            else
              (let uu___99_8170 = modul  in
               {
                 FStar_Syntax_Syntax.name =
                   (uu___99_8170.FStar_Syntax_Syntax.name);
                 FStar_Syntax_Syntax.declarations =
                   (uu___99_8170.FStar_Syntax_Syntax.declarations);
                 FStar_Syntax_Syntax.exports = exports;
                 FStar_Syntax_Syntax.is_interface =
                   (uu___99_8170.FStar_Syntax_Syntax.is_interface)
               })
             in
          let env1 = FStar_TypeChecker_Env.finish_module env modul1  in
          (let uu____8173 =
             ((let uu____8176 = FStar_Options.lax ()  in
               Prims.op_Negation uu____8176) &&
                (Prims.op_Negation dont_use_exports))
               && must_check_exports
              in
           if uu____8173 then check_exports env1 modul1 exports else ());
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
            (Prims.strcat "Ending modul "
               (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
            env1 modul1;
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
            ();
          (let uu____8182 =
             let uu____8183 = FStar_Options.interactive ()  in
             Prims.op_Negation uu____8183  in
           if uu____8182
           then
             let uu____8184 = FStar_Options.restore_cmd_line_options true  in
             FStar_All.pipe_right uu____8184 FStar_Pervasives.ignore
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
      (let uu____8194 =
         let uu____8195 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
         Prims.strcat "Internals for " uu____8195  in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
         uu____8194);
      (let env2 =
         FStar_List.fold_left
           (fun env2  ->
              fun se  ->
                let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
                let lids = FStar_Syntax_Util.lids_of_sigelt se  in
                FStar_All.pipe_right lids
                  (FStar_List.iter
                     (fun lid  ->
                        let uu____8214 =
                          FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                        ()));
                env3) env1 modul.FStar_Syntax_Syntax.declarations
          in
       let uu____8235 =
         finish_partial_modul false env2 modul
           modul.FStar_Syntax_Syntax.exports
          in
       FStar_Pervasives_Native.snd uu____8235)
  
let (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun modul  ->
      let uu____8250 = tc_partial_modul env modul true  in
      match uu____8250 with
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
                 let uu____8395 =
                   FStar_ST.op_Bang abstract_inductive_datacons  in
                 FStar_List.existsb (fun l'  -> FStar_Ident.lid_equals l l')
                   uu____8395
             | FStar_Syntax_Syntax.Projector (l,uu____8446) ->
                 let uu____8447 =
                   FStar_ST.op_Bang abstract_inductive_datacons  in
                 FStar_List.existsb (fun l'  -> FStar_Ident.lid_equals l l')
                   uu____8447
             | uu____8497 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8516 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____8547 ->
                   let uu____8548 =
                     let uu____8551 =
                       let uu____8552 =
                         let uu____8565 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____8565)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____8552  in
                     FStar_Syntax_Syntax.mk uu____8551  in
                   uu____8548 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____8573,uu____8574) ->
            let s1 =
              let uu___100_8584 = s  in
              let uu____8585 =
                let uu____8586 =
                  let uu____8593 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____8593)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____8586  in
              let uu____8594 =
                let uu____8597 =
                  filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals
                   in
                FStar_Syntax_Syntax.Assumption :: uu____8597  in
              {
                FStar_Syntax_Syntax.sigel = uu____8585;
                FStar_Syntax_Syntax.sigrng =
                  (uu___100_8584.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____8594;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___100_8584.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___100_8584.FStar_Syntax_Syntax.sigattrs)
              }  in
            if
              Prims.op_Negation
                (is_noeq_or_unopteq s.FStar_Syntax_Syntax.sigquals)
            then
              let uu____8600 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8600 with
               | (usubst,uvs1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let uu____8620 =
                     FStar_TypeChecker_Util.get_optimized_haseq_axiom env1 s
                       usubst uvs1
                      in
                   (match uu____8620 with
                    | (axiom_lid,fml,uu____8633,uu____8634,uu____8635) ->
                        let uu____8636 =
                          FStar_TypeChecker_Util.generalize_universes env1
                            fml
                           in
                        (match uu____8636 with
                         | (uvs2,fml1) ->
                             let s2 =
                               let uu___101_8644 = s  in
                               let uu____8645 =
                                 let uu____8648 =
                                   filter_out_abstract
                                     s.FStar_Syntax_Syntax.sigquals
                                    in
                                 FStar_Syntax_Syntax.Assumption :: uu____8648
                                  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_assume
                                      (axiom_lid, uvs2, fml1));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___101_8644.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = uu____8645;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___101_8644.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___101_8644.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             [s1; s2])))
            else [s1]
        | uu____8654 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____8672 =
        match uu____8672 with
        | (uvs,c_or_t) ->
            let t =
              let uu____8694 = FStar_All.pipe_right c_or_t FStar_Util.is_left
                 in
              if uu____8694
              then
                let uu____8701 = FStar_All.pipe_right c_or_t FStar_Util.left
                   in
                FStar_All.pipe_right uu____8701 FStar_Syntax_Util.comp_result
              else FStar_All.pipe_right c_or_t FStar_Util.right  in
            let uu___102_8713 = s  in
            let uu____8714 =
              let uu____8717 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____8717  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___102_8713.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____8714;
              FStar_Syntax_Syntax.sigmeta =
                (uu___102_8713.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___102_8713.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let extract_lb_annotation lb lid r =
        let opt =
          let uu____8773 = FStar_ST.op_Bang val_typs  in
          FStar_List.tryFind
            (fun uu____8865  ->
               match uu____8865 with
               | (l,uu____8877,uu____8878) -> FStar_Ident.lid_equals lid l)
            uu____8773
           in
        if FStar_Util.is_some opt
        then
          let uu____8911 = FStar_All.pipe_right opt FStar_Util.must  in
          match uu____8911 with
          | (uu____8968,uvs,t) ->
              let uu____8979 =
                let uu___103_8980 = lb  in
                let uu____8981 =
                  FStar_Syntax_Util.ascribe lb.FStar_Syntax_Syntax.lbdef
                    ((FStar_Util.Inl t), FStar_Pervasives_Native.None)
                   in
                {
                  FStar_Syntax_Syntax.lbname =
                    (uu___103_8980.FStar_Syntax_Syntax.lbname);
                  FStar_Syntax_Syntax.lbunivs = uvs;
                  FStar_Syntax_Syntax.lbtyp =
                    (uu___103_8980.FStar_Syntax_Syntax.lbtyp);
                  FStar_Syntax_Syntax.lbeff =
                    (uu___103_8980.FStar_Syntax_Syntax.lbeff);
                  FStar_Syntax_Syntax.lbdef = uu____8981;
                  FStar_Syntax_Syntax.lbattrs =
                    (uu___103_8980.FStar_Syntax_Syntax.lbattrs)
                }  in
              (uu____8979,
                (FStar_Pervasives_Native.Some (uvs, (FStar_Util.Inr t))))
        else
          (let uu____9039 =
             let uu____9040 =
               FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
             uu____9040.FStar_Syntax_Syntax.n  in
           match uu____9039 with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____9057 =
                 let uu____9058 =
                   FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef
                    in
                 uu____9058.FStar_Syntax_Syntax.n  in
               (match uu____9057 with
                | FStar_Syntax_Syntax.Tm_ascribed
                    (uu____9075,(FStar_Util.Inr c,uu____9077),uu____9078) ->
                    (lb,
                      (FStar_Pervasives_Native.Some
                         ((lb.FStar_Syntax_Syntax.lbunivs),
                           (FStar_Util.Inl c))))
                | FStar_Syntax_Syntax.Tm_ascribed
                    (uu____9161,(FStar_Util.Inl t,uu____9163),uu____9164) ->
                    (lb,
                      (FStar_Pervasives_Native.Some
                         ((lb.FStar_Syntax_Syntax.lbunivs),
                           (FStar_Util.Inr t))))
                | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____9249) ->
                    let uu____9270 =
                      let uu____9271 = FStar_Syntax_Subst.compress e  in
                      uu____9271.FStar_Syntax_Syntax.n  in
                    (match uu____9270 with
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (uu____9288,(FStar_Util.Inr c,uu____9290),uu____9291)
                         ->
                         let uu____9338 =
                           let uu____9353 =
                             let uu____9366 =
                               let uu____9373 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                                   FStar_Pervasives_Native.None r
                                  in
                               FStar_Util.Inr uu____9373  in
                             ((lb.FStar_Syntax_Syntax.lbunivs), uu____9366)
                              in
                           FStar_Pervasives_Native.Some uu____9353  in
                         (lb, uu____9338)
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (uu____9420,(FStar_Util.Inl t,uu____9422),uu____9423)
                         ->
                         let c =
                           let uu____9471 = FStar_Options.ml_ish ()  in
                           if uu____9471
                           then FStar_Syntax_Util.ml_comp t r
                           else FStar_Syntax_Syntax.mk_Total t  in
                         let uu____9473 =
                           let uu____9488 =
                             let uu____9501 =
                               let uu____9508 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                                   FStar_Pervasives_Native.None r
                                  in
                               FStar_Util.Inr uu____9508  in
                             ((lb.FStar_Syntax_Syntax.lbunivs), uu____9501)
                              in
                           FStar_Pervasives_Native.Some uu____9488  in
                         (lb, uu____9473)
                     | uu____9553 -> (lb, FStar_Pervasives_Native.None))
                | uu____9572 -> (lb, FStar_Pervasives_Native.None))
           | uu____9591 ->
               (lb,
                 (FStar_Pervasives_Native.Some
                    ((lb.FStar_Syntax_Syntax.lbunivs),
                      (FStar_Util.Inr (lb.FStar_Syntax_Syntax.lbtyp))))))
         in
      let should_keep_lbdef c_or_t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____9645 -> failwith "Impossible!"  in
        ((FStar_Util.is_right c_or_t) &&
           (let uu____9647 =
              let uu____9648 = FStar_All.pipe_right c_or_t FStar_Util.right
                 in
              FStar_Syntax_Util.is_function_typ uu____9648  in
            Prims.op_Negation uu____9647))
          ||
          (let c =
             let uu____9655 = FStar_Util.is_left c_or_t  in
             if uu____9655
             then FStar_All.pipe_right c_or_t FStar_Util.left
             else
               (let uu____9661 =
                  let uu____9662 =
                    let uu____9665 =
                      FStar_All.pipe_right c_or_t FStar_Util.right  in
                    FStar_Syntax_Subst.compress uu____9665  in
                  uu____9662.FStar_Syntax_Syntax.n  in
                match uu____9661 with
                | FStar_Syntax_Syntax.Tm_arrow (uu____9670,c) -> c
                | uu____9688 -> failwith "Impossible!")
              in
           ((FStar_Syntax_Util.is_pure_or_ghost_comp c) ||
              (let uu____9690 = comp_effect_name1 c  in
               FStar_TypeChecker_Util.is_reifiable env uu____9690))
             &&
             (let uu____9692 =
                let uu____9693 =
                  FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
                FStar_All.pipe_right uu____9693 FStar_Syntax_Util.is_unit  in
              Prims.op_Negation uu____9692))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____9708 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____9727 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____9773,uu____9774,uu____9775,uu____9776,uu____9777,uu____9778)
                         ->
                         let uu____9787 = vals_of_abstract_inductive s1  in
                         FStar_List.append uu____9787 sigelts1
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____9791,uu____9792,uu____9793,uu____9794,uu____9795)
                         ->
                         ((let uu____9801 =
                             let uu____9804 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____9804  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____9801);
                          sigelts1)
                     | uu____9897 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9904 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9904
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____9910 =
                   let uu___104_9911 = s  in
                   let uu____9912 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___104_9911.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___104_9911.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9912;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___104_9911.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___104_9911.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9910])
              else
                ((let uu____9917 =
                    let uu____9930 = FStar_ST.op_Bang val_typs  in
                    (lid, uvs, t) :: uu____9930  in
                  FStar_ST.op_Colon_Equals val_typs uu____9917);
                 [])
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____10081 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____10081
            then []
            else
              (let uu____10085 = lbs  in
               match uu____10085 with
               | (flbs,slbs) ->
                   let uu____10094 =
                     FStar_List.fold_left2
                       (fun uu____10144  ->
                          fun lb  ->
                            fun lid  ->
                              match uu____10144 with
                              | (b,lbs1,typs) ->
                                  let uu____10218 =
                                    extract_lb_annotation lb lid
                                      s.FStar_Syntax_Syntax.sigrng
                                     in
                                  (match uu____10218 with
                                   | (lb1,t) ->
                                       (((FStar_Util.is_some t) && b), (lb1
                                         :: lbs1), (t :: typs))))
                       (true, [], []) slbs lids
                      in
                   (match uu____10094 with
                    | (b,lbs1,typs) ->
                        let uu____10364 =
                          ((FStar_List.rev_append lbs1 []),
                            (FStar_List.rev_append typs []))
                           in
                        (match uu____10364 with
                         | (lbs2,typs1) ->
                             let s1 =
                               let uu___105_10450 = s  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_let
                                      ((flbs, lbs2), lids));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___105_10450.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___105_10450.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___105_10450.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___105_10450.FStar_Syntax_Syntax.sigattrs)
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
                                  let uu____10465 =
                                    let uu____10470 =
                                      let uu____10471 =
                                        let uu____10472 = FStar_List.hd lids
                                           in
                                        uu____10472.FStar_Ident.str  in
                                      Prims.strcat
                                        "For extracting interfaces, abstract and irreducible defns must be annotated at the top-level: "
                                        uu____10471
                                       in
                                    (FStar_Errors.Fatal_IllTyped,
                                      uu____10470)
                                     in
                                  FStar_Errors.raise_error uu____10465
                                    s1.FStar_Syntax_Syntax.sigrng
                                else [s1])
                             else
                               (let is_lemma1 =
                                  FStar_List.existsML
                                    (fun opt  ->
                                       let uu____10503 =
                                         FStar_All.pipe_right opt
                                           FStar_Util.must
                                          in
                                       match uu____10503 with
                                       | (uu____10538,c_or_t) ->
                                           (FStar_Util.is_right c_or_t) &&
                                             (let uu____10549 =
                                                FStar_All.pipe_right c_or_t
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____10549
                                                FStar_Syntax_Util.is_lemma))
                                    typs1
                                   in
                                let vals =
                                  FStar_List.map2
                                    (fun lid  ->
                                       fun opt  ->
                                         let uu____10582 =
                                           FStar_All.pipe_right opt
                                             FStar_Util.must
                                            in
                                         val_of_lb s1 lid uu____10582) lids
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
                                          let uu____10644 =
                                            let uu____10649 =
                                              FStar_All.pipe_right opt
                                                FStar_Util.must
                                               in
                                            FStar_All.pipe_right uu____10649
                                              FStar_Pervasives_Native.snd
                                             in
                                          should_keep_lbdef uu____10644)
                                       typs1
                                      in
                                   if should_keep_defs then [s1] else vals)))))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lids,uvs,t) ->
            let uu____10709 =
              let uu___106_10710 = s  in
              let uu____10711 =
                filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___106_10710.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___106_10710.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____10711;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___106_10710.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___106_10710.FStar_Syntax_Syntax.sigattrs)
              }  in
            [uu____10709]
        | FStar_Syntax_Syntax.Sig_new_effect uu____10714 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10715 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____10716 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10717 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____10730 -> [s]  in
      let uu___107_10731 = m  in
      let uu____10732 =
        let uu____10733 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____10733  in
      {
        FStar_Syntax_Syntax.name = (uu___107_10731.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10732;
        FStar_Syntax_Syntax.exports =
          (uu___107_10731.FStar_Syntax_Syntax.exports);
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
      (let uu____10751 = FStar_Options.debug_any ()  in
       if uu____10751
       then
         let uu____10752 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____10752
       else ());
      (let env1 =
         let uu___108_10756 = env  in
         let uu____10757 =
           let uu____10758 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____10758  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___108_10756.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___108_10756.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___108_10756.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___108_10756.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___108_10756.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___108_10756.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___108_10756.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___108_10756.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___108_10756.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___108_10756.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___108_10756.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___108_10756.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___108_10756.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___108_10756.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___108_10756.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___108_10756.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___108_10756.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___108_10756.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____10757;
           FStar_TypeChecker_Env.lax_universes =
             (uu___108_10756.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___108_10756.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___108_10756.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___108_10756.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___108_10756.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___108_10756.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___108_10756.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___108_10756.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___108_10756.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___108_10756.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___108_10756.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___108_10756.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___108_10756.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___108_10756.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___108_10756.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___108_10756.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____10759 = tc_modul env1 m  in
       match uu____10759 with
       | (m1,env2) ->
           ((let uu____10771 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____10771
             then
               let uu____10772 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____10772
             else ());
            (let uu____10775 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____10775
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
                       let uu____10806 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____10806 with
                       | (univnames1,e) ->
                           let uu___109_10813 = lb  in
                           let uu____10814 =
                             let uu____10817 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____10817 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___109_10813.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___109_10813.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___109_10813.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___109_10813.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____10814;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___109_10813.FStar_Syntax_Syntax.lbattrs)
                           }
                        in
                     let uu___110_10818 = se  in
                     let uu____10819 =
                       let uu____10820 =
                         let uu____10827 =
                           let uu____10834 = FStar_List.map update lbs  in
                           (b, uu____10834)  in
                         (uu____10827, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____10820  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____10819;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___110_10818.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___110_10818.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___110_10818.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___110_10818.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____10847 -> se  in
               let normalized_module =
                 let uu___111_10849 = m1  in
                 let uu____10850 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___111_10849.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____10850;
                   FStar_Syntax_Syntax.exports =
                     (uu___111_10849.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___111_10849.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____10851 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____10851
             else ());
            (m1, env2)))
  