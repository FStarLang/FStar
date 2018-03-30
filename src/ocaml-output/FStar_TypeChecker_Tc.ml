open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      let tbl =
        FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst
         in
      let get_n lid =
        let n_opt = FStar_Util.smap_try_find tbl lid.FStar_Ident.str  in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else (Prims.parse_int "0")  in
      let uu____42 = FStar_Options.reuse_hint_for ()  in
      match uu____42 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____47 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____47 l  in
          let uu___63_48 = env  in
          let uu____49 =
            let uu____62 =
              let uu____69 = let uu____74 = get_n lid  in (lid, uu____74)  in
              FStar_Pervasives_Native.Some uu____69  in
            (tbl, uu____62)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___63_48.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___63_48.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___63_48.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___63_48.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___63_48.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___63_48.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___63_48.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___63_48.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___63_48.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___63_48.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___63_48.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___63_48.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___63_48.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___63_48.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___63_48.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___63_48.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___63_48.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___63_48.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___63_48.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___63_48.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___63_48.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___63_48.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___63_48.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___63_48.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___63_48.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___63_48.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___63_48.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____49;
            FStar_TypeChecker_Env.proof_ns =
              (uu___63_48.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___63_48.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___63_48.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___63_48.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___63_48.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___63_48.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___63_48.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___63_48.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____91 = FStar_TypeChecker_Env.current_module env  in
                let uu____92 =
                  let uu____93 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____93 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____91 uu____92
            | l::uu____95 -> l  in
          let uu___64_98 = env  in
          let uu____99 =
            let uu____112 =
              let uu____119 = let uu____124 = get_n lid  in (lid, uu____124)
                 in
              FStar_Pervasives_Native.Some uu____119  in
            (tbl, uu____112)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___64_98.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___64_98.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___64_98.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___64_98.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___64_98.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___64_98.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___64_98.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___64_98.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___64_98.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___64_98.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___64_98.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___64_98.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___64_98.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___64_98.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___64_98.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___64_98.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___64_98.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___64_98.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___64_98.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___64_98.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___64_98.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___64_98.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___64_98.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___64_98.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___64_98.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___64_98.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___64_98.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____99;
            FStar_TypeChecker_Env.proof_ns =
              (uu___64_98.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___64_98.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___64_98.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___64_98.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___64_98.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___64_98.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___64_98.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___64_98.FStar_TypeChecker_Env.dep_graph)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____141 =
         let uu____142 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____142  in
       Prims.op_Negation uu____141)
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____152 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____152 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____173 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____173
         then
           let uu____174 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____174
         else ());
        (let uu____176 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____176 with
         | (t',uu____184,uu____185) ->
             ((let uu____187 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____187
               then
                 let uu____188 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____188
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
        let uu____199 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____199
  
let check_nogen :
  'Auu____204 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____204 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____224 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1
           in
        ([], uu____224)
  
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
        let fail1 uu____251 =
          let uu____252 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____257 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____252 uu____257  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____297)::(wp,uu____299)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____314 -> fail1 ())
        | uu____315 -> fail1 ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____322 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____322 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____348 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____348 t  in
          let open_univs_binders n_binders bs =
            let uu____358 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____358 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____366 =
            let uu____373 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____374 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____373 uu____374  in
          (match uu____366 with
           | (effect_params_un,signature_un,opening) ->
               let uu____384 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
                  in
               (match uu____384 with
                | (effect_params,env,uu____393) ->
                    let uu____394 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                       in
                    (match uu____394 with
                     | (signature,uu____400) ->
                         let ed1 =
                           let uu___65_402 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___65_402.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___65_402.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___65_402.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___65_402.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___65_402.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___65_402.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___65_402.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___65_402.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___65_402.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___65_402.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___65_402.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___65_402.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___65_402.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___65_402.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___65_402.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___65_402.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___65_402.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___65_402.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____418 ->
                               let op uu____440 =
                                 match uu____440 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____460 =
                                       let uu____461 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____470 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____461
                                         uu____470
                                        in
                                     (us, uu____460)
                                  in
                               let uu___66_479 = ed1  in
                               let uu____480 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____481 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____482 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____483 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____484 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____485 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____486 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____487 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____488 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____489 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____490 =
                                 let uu____491 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____491  in
                               let uu____502 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____503 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____504 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___67_512 = a  in
                                      let uu____513 =
                                        let uu____514 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____514
                                         in
                                      let uu____523 =
                                        let uu____524 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____524
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___67_512.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___67_512.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___67_512.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___67_512.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____513;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____523
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___66_479.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___66_479.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___66_479.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___66_479.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____480;
                                 FStar_Syntax_Syntax.bind_wp = uu____481;
                                 FStar_Syntax_Syntax.if_then_else = uu____482;
                                 FStar_Syntax_Syntax.ite_wp = uu____483;
                                 FStar_Syntax_Syntax.stronger = uu____484;
                                 FStar_Syntax_Syntax.close_wp = uu____485;
                                 FStar_Syntax_Syntax.assert_p = uu____486;
                                 FStar_Syntax_Syntax.assume_p = uu____487;
                                 FStar_Syntax_Syntax.null_wp = uu____488;
                                 FStar_Syntax_Syntax.trivial = uu____489;
                                 FStar_Syntax_Syntax.repr = uu____490;
                                 FStar_Syntax_Syntax.return_repr = uu____502;
                                 FStar_Syntax_Syntax.bind_repr = uu____503;
                                 FStar_Syntax_Syntax.actions = uu____504;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___66_479.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail1 t =
                             let uu____559 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t
                                in
                             let uu____564 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____559 uu____564  in
                           let uu____571 =
                             let uu____572 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____572.FStar_Syntax_Syntax.n  in
                           match uu____571 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____607)::(wp,uu____609)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____624 -> fail1 signature1)
                           | uu____625 -> fail1 signature1  in
                         let uu____626 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____626 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____648 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____655 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un
                                       in
                                    (match uu____655 with
                                     | (signature1,uu____667) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____668 ->
                                    let uu____671 =
                                      let uu____676 =
                                        let uu____677 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____677)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____676
                                       in
                                    (match uu____671 with
                                     | (uu____686,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env1 =
                                let uu____689 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env uu____689
                                 in
                              ((let uu____691 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____691
                                then
                                  let uu____692 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____693 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____694 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____695 =
                                    let uu____696 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____696
                                     in
                                  let uu____697 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____692 uu____693 uu____694 uu____695
                                    uu____697
                                else ());
                               (let check_and_gen' env2 uu____713 k =
                                  match uu____713 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____727::uu____728 ->
                                           let uu____731 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____731 with
                                            | (us1,t1) ->
                                                let uu____740 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____740 with
                                                 | (us2,t2) ->
                                                     let uu____747 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k
                                                        in
                                                     let uu____748 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____748))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____753 =
                                      let uu____760 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____761 =
                                        let uu____764 =
                                          let uu____765 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____765
                                           in
                                        [uu____764]  in
                                      uu____760 :: uu____761  in
                                    let uu____766 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____753
                                      uu____766
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____770 = fresh_effect_signature ()
                                     in
                                  match uu____770 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____786 =
                                          let uu____793 =
                                            let uu____794 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____794
                                             in
                                          [uu____793]  in
                                        let uu____795 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____786
                                          uu____795
                                         in
                                      let expected_k =
                                        let uu____801 =
                                          let uu____808 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____809 =
                                            let uu____812 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____813 =
                                              let uu____816 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____817 =
                                                let uu____820 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____821 =
                                                  let uu____824 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____824]  in
                                                uu____820 :: uu____821  in
                                              uu____816 :: uu____817  in
                                            uu____812 :: uu____813  in
                                          uu____808 :: uu____809  in
                                        let uu____825 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____801
                                          uu____825
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____830 =
                                      let uu____833 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____833
                                       in
                                    let uu____834 =
                                      let uu____835 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____835
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____830
                                      uu____834
                                     in
                                  let expected_k =
                                    let uu____847 =
                                      let uu____854 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____855 =
                                        let uu____858 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____859 =
                                          let uu____862 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____863 =
                                            let uu____866 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____866]  in
                                          uu____862 :: uu____863  in
                                        uu____858 :: uu____859  in
                                      uu____854 :: uu____855  in
                                    let uu____867 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____847
                                      uu____867
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____874 =
                                      let uu____881 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____882 =
                                        let uu____885 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____885]  in
                                      uu____881 :: uu____882  in
                                    let uu____886 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____874
                                      uu____886
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____890 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____890 with
                                  | (t,uu____896) ->
                                      let expected_k =
                                        let uu____900 =
                                          let uu____907 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____908 =
                                            let uu____911 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____912 =
                                              let uu____915 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____915]  in
                                            uu____911 :: uu____912  in
                                          uu____907 :: uu____908  in
                                        let uu____916 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____900
                                          uu____916
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____921 =
                                      let uu____924 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____924
                                       in
                                    let uu____925 =
                                      let uu____926 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____926
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____921
                                      uu____925
                                     in
                                  let b_wp_a =
                                    let uu____938 =
                                      let uu____945 =
                                        let uu____946 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____946
                                         in
                                      [uu____945]  in
                                    let uu____947 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____938
                                      uu____947
                                     in
                                  let expected_k =
                                    let uu____953 =
                                      let uu____960 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____961 =
                                        let uu____964 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____965 =
                                          let uu____968 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____968]  in
                                        uu____964 :: uu____965  in
                                      uu____960 :: uu____961  in
                                    let uu____969 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____953
                                      uu____969
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____976 =
                                      let uu____983 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____984 =
                                        let uu____987 =
                                          let uu____988 =
                                            let uu____989 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____989
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____988
                                           in
                                        let uu____998 =
                                          let uu____1001 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1001]  in
                                        uu____987 :: uu____998  in
                                      uu____983 :: uu____984  in
                                    let uu____1002 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____976
                                      uu____1002
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1009 =
                                      let uu____1016 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1017 =
                                        let uu____1020 =
                                          let uu____1021 =
                                            let uu____1022 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1022
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1021
                                           in
                                        let uu____1031 =
                                          let uu____1034 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1034]  in
                                        uu____1020 :: uu____1031  in
                                      uu____1016 :: uu____1017  in
                                    let uu____1035 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1009
                                      uu____1035
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1042 =
                                      let uu____1049 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1049]  in
                                    let uu____1050 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1042
                                      uu____1050
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1054 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1054 with
                                  | (t,uu____1060) ->
                                      let expected_k =
                                        let uu____1064 =
                                          let uu____1071 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1072 =
                                            let uu____1075 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1075]  in
                                          uu____1071 :: uu____1072  in
                                        let uu____1076 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1064
                                          uu____1076
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1079 =
                                  let uu____1090 =
                                    let uu____1091 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1091.FStar_Syntax_Syntax.n  in
                                  match uu____1090 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1106 ->
                                      let repr =
                                        let uu____1108 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1108 with
                                        | (t,uu____1114) ->
                                            let expected_k =
                                              let uu____1118 =
                                                let uu____1125 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1126 =
                                                  let uu____1129 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1129]  in
                                                uu____1125 :: uu____1126  in
                                              let uu____1130 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1118 uu____1130
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
                                        let uu____1143 =
                                          let uu____1146 =
                                            let uu____1147 =
                                              let uu____1162 =
                                                let uu____1165 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1166 =
                                                  let uu____1169 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1169]  in
                                                uu____1165 :: uu____1166  in
                                              (repr1, uu____1162)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1147
                                             in
                                          FStar_Syntax_Syntax.mk uu____1146
                                           in
                                        uu____1143
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1184 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1184 wp  in
                                      let destruct_repr t =
                                        let uu____1197 =
                                          let uu____1198 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1198.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1197 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1209,(t1,uu____1211)::
                                             (wp,uu____1213)::[])
                                            -> (t1, wp)
                                        | uu____1256 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1267 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1267
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1268 =
                                          fresh_effect_signature ()  in
                                        match uu____1268 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1284 =
                                                let uu____1291 =
                                                  let uu____1292 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1292
                                                   in
                                                [uu____1291]  in
                                              let uu____1293 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1284 uu____1293
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
                                              let uu____1299 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1299
                                               in
                                            let wp_g_x =
                                              let uu____1303 =
                                                let uu____1304 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1305 =
                                                  let uu____1306 =
                                                    let uu____1307 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1307
                                                     in
                                                  [uu____1306]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1304 uu____1305
                                                 in
                                              uu____1303
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1316 =
                                                  let uu____1317 =
                                                    let uu____1318 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1318
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1327 =
                                                    let uu____1328 =
                                                      let uu____1331 =
                                                        let uu____1334 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1335 =
                                                          let uu____1338 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1339 =
                                                            let uu____1342 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1343 =
                                                              let uu____1346
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1346]
                                                               in
                                                            uu____1342 ::
                                                              uu____1343
                                                             in
                                                          uu____1338 ::
                                                            uu____1339
                                                           in
                                                        uu____1334 ::
                                                          uu____1335
                                                         in
                                                      r :: uu____1331  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1328
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1317 uu____1327
                                                   in
                                                uu____1316
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____1352 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____1352
                                              then
                                                let uu____1355 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____1356 =
                                                  let uu____1359 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____1359]  in
                                                uu____1355 :: uu____1356
                                              else []  in
                                            let expected_k =
                                              let uu____1364 =
                                                let uu____1371 =
                                                  let uu____1374 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____1375 =
                                                    let uu____1378 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____1378]  in
                                                  uu____1374 :: uu____1375
                                                   in
                                                let uu____1379 =
                                                  let uu____1382 =
                                                    let uu____1385 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1386 =
                                                      let uu____1389 =
                                                        let uu____1390 =
                                                          let uu____1391 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1391
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1390
                                                         in
                                                      let uu____1392 =
                                                        let uu____1395 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1396 =
                                                          let uu____1399 =
                                                            let uu____1400 =
                                                              let uu____1401
                                                                =
                                                                let uu____1408
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1408]
                                                                 in
                                                              let uu____1409
                                                                =
                                                                let uu____1412
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1412
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1401
                                                                uu____1409
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1400
                                                             in
                                                          [uu____1399]  in
                                                        uu____1395 ::
                                                          uu____1396
                                                         in
                                                      uu____1389 ::
                                                        uu____1392
                                                       in
                                                    uu____1385 :: uu____1386
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____1382
                                                   in
                                                FStar_List.append uu____1371
                                                  uu____1379
                                                 in
                                              let uu____1413 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1364 uu____1413
                                               in
                                            let uu____1416 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k
                                               in
                                            (match uu____1416 with
                                             | (expected_k1,uu____1424,uu____1425)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env3 =
                                                   let uu___68_1430 = env2
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___68_1430.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1440 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1440
                                           in
                                        let res =
                                          let wp =
                                            let uu____1447 =
                                              let uu____1448 =
                                                let uu____1449 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1449
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1458 =
                                                let uu____1459 =
                                                  let uu____1462 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1463 =
                                                    let uu____1466 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1466]  in
                                                  uu____1462 :: uu____1463
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1459
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1448 uu____1458
                                               in
                                            uu____1447
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1472 =
                                            let uu____1479 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1480 =
                                              let uu____1483 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1483]  in
                                            uu____1479 :: uu____1480  in
                                          let uu____1484 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1472
                                            uu____1484
                                           in
                                        let uu____1487 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k
                                           in
                                        match uu____1487 with
                                        | (expected_k1,uu____1501,uu____1502)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1506 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1506 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1527 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let act1 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then act
                                            else
                                              (let uu____1556 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____1556 with
                                               | (usubst,uvs) ->
                                                   let uu___69_1575 = act  in
                                                   let uu____1576 =
                                                     FStar_Syntax_Subst.subst_binders
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_params
                                                      in
                                                   let uu____1577 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_defn
                                                      in
                                                   let uu____1578 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       =
                                                       (uu___69_1575.FStar_Syntax_Syntax.action_name);
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       =
                                                       (uu___69_1575.FStar_Syntax_Syntax.action_unqualified_name);
                                                     FStar_Syntax_Syntax.action_univs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.action_params
                                                       = uu____1576;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____1577;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____1578
                                                   })
                                             in
                                          let act_typ =
                                            let uu____1582 =
                                              let uu____1583 =
                                                FStar_Syntax_Subst.compress
                                                  act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              uu____1583.FStar_Syntax_Syntax.n
                                               in
                                            match uu____1582 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) ->
                                                let c1 =
                                                  FStar_Syntax_Util.comp_to_comp_typ
                                                    c
                                                   in
                                                let uu____1607 =
                                                  FStar_Ident.lid_equals
                                                    c1.FStar_Syntax_Syntax.effect_name
                                                    ed2.FStar_Syntax_Syntax.mname
                                                   in
                                                if uu____1607
                                                then
                                                  let uu____1610 =
                                                    let uu____1613 =
                                                      let uu____1614 =
                                                        let uu____1615 =
                                                          FStar_List.hd
                                                            c1.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        FStar_Pervasives_Native.fst
                                                          uu____1615
                                                         in
                                                      mk_repr'
                                                        c1.FStar_Syntax_Syntax.result_typ
                                                        uu____1614
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total
                                                      uu____1613
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____1610
                                                else
                                                  act1.FStar_Syntax_Syntax.action_typ
                                            | uu____1631 ->
                                                act1.FStar_Syntax_Syntax.action_typ
                                             in
                                          let uu____1632 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1 act_typ
                                             in
                                          match uu____1632 with
                                          | (act_typ1,uu____1640,g_t) ->
                                              let env' =
                                                let uu___70_1643 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ1
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___70_1643.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth_hook
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.synth_hook);
                                                  FStar_TypeChecker_Env.splice
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.splice);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___70_1643.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1645 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1645
                                                then
                                                  let uu____1646 =
                                                    FStar_Ident.text_of_lid
                                                      act1.FStar_Syntax_Syntax.action_name
                                                     in
                                                  let uu____1647 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act1.FStar_Syntax_Syntax.action_defn
                                                     in
                                                  let uu____1648 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ1
                                                     in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    uu____1646 uu____1647
                                                    uu____1648
                                                else ());
                                               (let uu____1650 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act1.FStar_Syntax_Syntax.action_defn
                                                   in
                                                match uu____1650 with
                                                | (act_defn,uu____1658,g_a)
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
                                                    let uu____1662 =
                                                      let act_typ3 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ2
                                                         in
                                                      match act_typ3.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1690 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c
                                                             in
                                                          (match uu____1690
                                                           with
                                                           | (bs1,uu____1700)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let k =
                                                                 let uu____1707
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1707
                                                                  in
                                                               let uu____1710
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k
                                                                  in
                                                               (match uu____1710
                                                                with
                                                                | (k1,uu____1722,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1724 ->
                                                          let uu____1725 =
                                                            let uu____1730 =
                                                              let uu____1731
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ3
                                                                 in
                                                              let uu____1732
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ3
                                                                 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1731
                                                                uu____1732
                                                               in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1730)
                                                             in
                                                          FStar_Errors.raise_error
                                                            uu____1725
                                                            act_defn1.FStar_Syntax_Syntax.pos
                                                       in
                                                    (match uu____1662 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ2
                                                             expected_k
                                                            in
                                                         ((let uu____1741 =
                                                             let uu____1742 =
                                                               let uu____1743
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1743
                                                                in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1742
                                                              in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1741);
                                                          (let act_typ3 =
                                                             let uu____1747 =
                                                               let uu____1748
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1748.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1747
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1771
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1771
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1780
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1780
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1802
                                                                    =
                                                                    let uu____1803
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1803]
                                                                     in
                                                                    let uu____1804
                                                                    =
                                                                    let uu____1813
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1813]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1802;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1804;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1814
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1814))
                                                             | uu____1817 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1820 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1
                                                              in
                                                           match uu____1820
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
                                                               let uu___71_1829
                                                                 = act1  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___71_1829.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___71_1829.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___71_1829.FStar_Syntax_Syntax.action_params);
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
                                match uu____1079 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1853 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1853
                                       in
                                    let uu____1856 =
                                      let uu____1863 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1863 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1884 ->
                                               let uu____1887 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____1893 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____1893 =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____1887
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1903 =
                                                    let uu____1908 =
                                                      let uu____1909 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1910 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1909 uu____1910
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1908)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1903
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1856 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1924 =
                                             let uu____1929 =
                                               let uu____1930 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1930.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1929)  in
                                           match uu____1924 with
                                           | ([],uu____1933) -> t
                                           | (uu____1944,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1945,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1963 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1976 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1976
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1981 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1983 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1983))
                                                && (m <> n1)
                                               in
                                            if uu____1981
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____1999 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____2006 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____2007 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1999 uu____2006
                                                  uu____2007
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____2015 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____2015 with
                                           | (univs2,defn) ->
                                               let uu____2022 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____2022 with
                                                | (univs',typ) ->
                                                    let uu___72_2032 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___72_2032.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___72_2032.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___72_2032.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___73_2037 = ed2  in
                                           let uu____2038 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____2039 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____2040 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____2041 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____2042 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____2043 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____2044 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____2045 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____2046 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____2047 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____2048 =
                                             let uu____2049 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____2049
                                              in
                                           let uu____2060 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____2061 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____2062 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___73_2037.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___73_2037.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2038;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2039;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2040;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2041;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2042;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2043;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2044;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2045;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2046;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2047;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2048;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2060;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2061;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2062;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___73_2037.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____2066 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____2066
                                           then
                                             let uu____2067 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____2067
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
      let uu____2085 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2085 with
      | (effect_binders_un,signature_un) ->
          let uu____2102 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2102 with
           | (effect_binders,env1,uu____2121) ->
               let uu____2122 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2122 with
                | (signature,uu____2138) ->
                    let raise_error1 a uu____2149 =
                      match uu____2149 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2175  ->
                           match uu____2175 with
                           | (bv,qual) ->
                               let uu____2186 =
                                 let uu___74_2187 = bv  in
                                 let uu____2188 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___74_2187.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___74_2187.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2188
                                 }  in
                               (uu____2186, qual)) effect_binders
                       in
                    let uu____2191 =
                      let uu____2198 =
                        let uu____2199 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2199.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2198 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2209)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2231 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2191 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2249 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2249
                           then
                             let uu____2250 =
                               let uu____2253 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2253  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2250
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2287 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2287 with
                           | (t2,comp,uu____2300) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2307 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2307 with
                          | (repr,_comp) ->
                              ((let uu____2329 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2329
                                then
                                  let uu____2330 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2330
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
                                  let uu____2336 =
                                    let uu____2337 =
                                      let uu____2338 =
                                        let uu____2353 =
                                          let uu____2360 =
                                            let uu____2365 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2366 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2365, uu____2366)  in
                                          [uu____2360]  in
                                        (wp_type1, uu____2353)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2338
                                       in
                                    mk1 uu____2337  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2336
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2391 =
                                      let uu____2396 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2396)  in
                                    let uu____2397 =
                                      let uu____2404 =
                                        let uu____2405 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2405
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2404]  in
                                    uu____2391 :: uu____2397  in
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
                                  let uu____2468 = item  in
                                  match uu____2468 with
                                  | (u_item,item1) ->
                                      let uu____2489 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2489 with
                                       | (item2,item_comp) ->
                                           ((let uu____2505 =
                                               let uu____2506 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2506
                                                in
                                             if uu____2505
                                             then
                                               let uu____2507 =
                                                 let uu____2512 =
                                                   let uu____2513 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2514 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2513 uu____2514
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2512)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2507
                                             else ());
                                            (let uu____2516 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2516 with
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
                                let uu____2536 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2536 with
                                | (dmff_env1,uu____2560,bind_wp,bind_elab) ->
                                    let uu____2563 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2563 with
                                     | (dmff_env2,uu____2587,return_wp,return_elab)
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
                                           let uu____2594 =
                                             let uu____2595 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2595.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2594 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2639 =
                                                       let uu____2654 =
                                                         let uu____2659 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2659
                                                          in
                                                       match uu____2654 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2723 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2639 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2762 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2762
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2779 =
                                                               let uu____2780
                                                                 =
                                                                 let uu____2795
                                                                   =
                                                                   let uu____2802
                                                                    =
                                                                    let uu____2807
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2808
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2807,
                                                                    uu____2808)
                                                                     in
                                                                   [uu____2802]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2795)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2780
                                                                in
                                                             mk1 uu____2779
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2823 =
                                                           let uu____2832 =
                                                             let uu____2833 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2833
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2832
                                                            in
                                                         (match uu____2823
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail1 a393
                                                                =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2852
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2854
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    let uu____2855
                                                                    =
                                                                    match what'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2854
                                                                    uu____2855
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                                    error_msg)))
                                                                  a393
                                                                 in
                                                              ((match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail1 ()
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    (
                                                                    (
                                                                    let uu____2860
                                                                    =
                                                                    let uu____2861
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____2861
                                                                     in
                                                                    if
                                                                    uu____2860
                                                                    then
                                                                    fail1 ()
                                                                    else ());
                                                                    (
                                                                    let uu____2863
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
                                                                    fail1 ())
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2863
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
                                                                  let uu____2890
                                                                    =
                                                                    let uu____2891
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2892
                                                                    =
                                                                    let uu____2893
                                                                    =
                                                                    let uu____2900
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2900,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2893]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2891
                                                                    uu____2892
                                                                     in
                                                                  uu____2890
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2925
                                                                  =
                                                                  let uu____2926
                                                                    =
                                                                    let uu____2933
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2933]
                                                                     in
                                                                  b11 ::
                                                                    uu____2926
                                                                   in
                                                                let uu____2938
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2925
                                                                  uu____2938
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2939 ->
                                                  Obj.repr
                                                    (let uu____2940 =
                                                       let uu____2945 =
                                                         let uu____2946 =
                                                           FStar_Syntax_Print.term_to_string
                                                             return_wp
                                                            in
                                                         FStar_Util.format1
                                                           "unexpected shape for return: %s"
                                                           uu____2946
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         uu____2945)
                                                        in
                                                     raise_error1 ()
                                                       uu____2940))
                                            in
                                         let return_wp1 =
                                           let uu____2948 =
                                             let uu____2949 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2949.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2948 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2993 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2993
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____3006 ->
                                                  Obj.repr
                                                    (let uu____3007 =
                                                       let uu____3012 =
                                                         let uu____3013 =
                                                           FStar_Syntax_Print.term_to_string
                                                             return_wp
                                                            in
                                                         FStar_Util.format1
                                                           "unexpected shape for return: %s"
                                                           uu____3013
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         uu____3012)
                                                        in
                                                     raise_error1 ()
                                                       uu____3007))
                                            in
                                         let bind_wp1 =
                                           let uu____3015 =
                                             let uu____3016 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____3016.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____3015 with
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
                                                     let uu____3043 =
                                                       let uu____3044 =
                                                         let uu____3047 =
                                                           let uu____3048 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____3048
                                                            in
                                                         [uu____3047]  in
                                                       FStar_List.append
                                                         uu____3044 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____3043 body what)
                                              | uu____3049 ->
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
                                             (let uu____3067 =
                                                let uu____3068 =
                                                  let uu____3069 =
                                                    let uu____3084 =
                                                      let uu____3085 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3085
                                                       in
                                                    (t, uu____3084)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3069
                                                   in
                                                mk1 uu____3068  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3067)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3115 = f a2  in
                                               [uu____3115]
                                           | x::xs ->
                                               let uu____3120 =
                                                 apply_last1 f xs  in
                                               x :: uu____3120
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
                                           let uu____3138 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3138 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3168 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3168
                                                 then
                                                   let uu____3169 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3169
                                                 else ());
                                                (let uu____3171 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3171))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3180 =
                                                 let uu____3185 = mk_lid name
                                                    in
                                                 let uu____3186 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3185 uu____3186
                                                  in
                                               (match uu____3180 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3190 =
                                                        let uu____3193 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3193
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3190);
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
                                          (let uu____3290 =
                                             let uu____3293 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3294 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3293 :: uu____3294  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3290);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3392 =
                                               let uu____3395 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3396 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3395 :: uu____3396  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3392);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3491 =
                                                FStar_List.fold_left
                                                  (fun uu____3531  ->
                                                     fun action  ->
                                                       match uu____3531 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3552 =
                                                             let uu____3559 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3559
                                                               params_un
                                                              in
                                                           (match uu____3552
                                                            with
                                                            | (action_params,env',uu____3568)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3588
                                                                     ->
                                                                    match uu____3588
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3599
                                                                    =
                                                                    let uu___75_3600
                                                                    = bv  in
                                                                    let uu____3601
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___75_3600.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___75_3600.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3601
                                                                    }  in
                                                                    (uu____3599,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3605
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3605
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
                                                                    uu____3635
                                                                    ->
                                                                    let uu____3636
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3636
                                                                     in
                                                                    ((
                                                                    let uu____3640
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3640
                                                                    then
                                                                    let uu____3641
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3642
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3643
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3644
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3641
                                                                    uu____3642
                                                                    uu____3643
                                                                    uu____3644
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
                                                                    let uu____3648
                                                                    =
                                                                    let uu____3651
                                                                    =
                                                                    let uu___76_3652
                                                                    = action
                                                                     in
                                                                    let uu____3653
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3654
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___76_3652.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___76_3652.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___76_3652.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3653;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3654
                                                                    }  in
                                                                    uu____3651
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3648))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3491 with
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
                                                      let uu____3687 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3688 =
                                                        let uu____3691 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3691]  in
                                                      uu____3687 ::
                                                        uu____3688
                                                       in
                                                    let uu____3692 =
                                                      let uu____3693 =
                                                        let uu____3694 =
                                                          let uu____3695 =
                                                            let uu____3710 =
                                                              let uu____3717
                                                                =
                                                                let uu____3722
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3723
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3722,
                                                                  uu____3723)
                                                                 in
                                                              [uu____3717]
                                                               in
                                                            (repr,
                                                              uu____3710)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3695
                                                           in
                                                        mk1 uu____3694  in
                                                      let uu____3738 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3693
                                                        uu____3738
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3692
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3741 =
                                                    let uu____3748 =
                                                      let uu____3749 =
                                                        let uu____3752 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3752
                                                         in
                                                      uu____3749.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3748 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3762)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3791
                                                                =
                                                                let uu____3808
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3808
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3866
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3791
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3916
                                                                    =
                                                                    let uu____3917
                                                                    =
                                                                    let uu____3920
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3920
                                                                     in
                                                                    uu____3917.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3916
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3945
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3945
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3958
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3983
                                                                     ->
                                                                    match uu____3983
                                                                    with
                                                                    | 
                                                                    (bv,uu____3989)
                                                                    ->
                                                                    let uu____3990
                                                                    =
                                                                    let uu____3991
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3991
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3990
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3958
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
                                                                    let uu____4055
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4055
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4060
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4068
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4068
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4073
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4076
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4073,
                                                                    uu____4076)))
                                                                    | 
                                                                    uu____4083
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4084
                                                                    =
                                                                    let uu____4089
                                                                    =
                                                                    let uu____4090
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4090
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4089)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4084)))
                                                       | uu____4091 ->
                                                           Obj.repr
                                                             (let uu____4092
                                                                =
                                                                let uu____4097
                                                                  =
                                                                  let uu____4098
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____4098
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____4097)
                                                                 in
                                                              raise_error1 ()
                                                                uu____4092))
                                                     in
                                                  (match uu____3741 with
                                                   | (pre,post) ->
                                                       ((let uu____4116 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4118 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4120 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___77_4122 =
                                                             ed  in
                                                           let uu____4123 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4124 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____4125 =
                                                             let uu____4126 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4126)
                                                              in
                                                           let uu____4133 =
                                                             let uu____4134 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4134)
                                                              in
                                                           let uu____4141 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____4142 =
                                                             let uu____4143 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4143)
                                                              in
                                                           let uu____4150 =
                                                             let uu____4151 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4151)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4123;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4124;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4125;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4133;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4141;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4142;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4150;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___77_4122.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____4158 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4158
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4176
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4176
                                                               then
                                                                 let uu____4177
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4177
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
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4192
                                                                    =
                                                                    let uu____4201
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4201)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4192
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
                                                                    uu____4189;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4216
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4216
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4218
                                                                 =
                                                                 let uu____4221
                                                                   =
                                                                   let uu____4224
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4224
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4221
                                                                   sigelts'
                                                                  in
                                                               (uu____4218,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4281 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4281 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4314 = FStar_List.hd ses  in
            uu____4314.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4319 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4323,[],t,uu____4325,uu____4326);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4328;
               FStar_Syntax_Syntax.sigattrs = uu____4329;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4331,_t_top,_lex_t_top,_0_40,uu____4334);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4336;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4337;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4339,_t_cons,_lex_t_cons,_0_41,uu____4342);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4344;
                 FStar_Syntax_Syntax.sigattrs = uu____4345;_}::[]
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
                 let uu____4404 =
                   let uu____4407 =
                     let uu____4408 =
                       let uu____4415 =
                         let uu____4416 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____4416
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4415, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4408  in
                   FStar_Syntax_Syntax.mk uu____4407  in
                 uu____4404 FStar_Pervasives_Native.None r1  in
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
                   let uu____4434 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4434
                    in
                 let hd1 =
                   let uu____4436 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4436
                    in
                 let tl1 =
                   let uu____4438 =
                     let uu____4439 =
                       let uu____4442 =
                         let uu____4443 =
                           let uu____4450 =
                             let uu____4451 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____4451
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4450, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4443  in
                       FStar_Syntax_Syntax.mk uu____4442  in
                     uu____4439 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4438
                    in
                 let res =
                   let uu____4460 =
                     let uu____4463 =
                       let uu____4464 =
                         let uu____4471 =
                           let uu____4472 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____4472
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4471,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4464  in
                     FStar_Syntax_Syntax.mk uu____4463  in
                   uu____4460 FStar_Pervasives_Native.None r2  in
                 let uu____4478 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4478
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
               let uu____4517 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4517;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4522 ->
               let err_msg =
                 let uu____4526 =
                   let uu____4527 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4527  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4526
                  in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.formula ->
      FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun phi  ->
      fun r  ->
        let env1 = FStar_TypeChecker_Env.set_range env r  in
        let uu____4542 = FStar_Syntax_Util.type_u ()  in
        match uu____4542 with
        | (k,uu____4548) ->
            let phi1 =
              let uu____4550 = tc_check_trivial_guard env1 phi k  in
              FStar_All.pipe_right uu____4550
                (FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env1)
               in
            (FStar_TypeChecker_Util.check_uvars r phi1; phi1)
  
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive"  in
          let uu____4583 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4583 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4614 =
                  FStar_List.map
                    (FStar_TypeChecker_TcInductive.mk_data_operations quals
                       env1 tcs) datas
                   in
                FStar_All.pipe_right uu____4614 FStar_List.flatten  in
              ((let uu____4628 =
                  (FStar_Options.no_positivity ()) ||
                    (let uu____4630 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     Prims.op_Negation uu____4630)
                   in
                if uu____4628
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
                          let uu____4641 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4651,uu____4652,uu____4653,uu____4654,uu____4655)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4664 -> failwith "Impossible!"  in
                          match uu____4641 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4675 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4679,uu____4680,uu____4681,uu____4682,uu____4683)
                        -> lid
                    | uu____4692 -> failwith "Impossible"  in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    FStar_TypeChecker_TcInductive.early_prims_inductives
                   in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals
                   in
                let res =
                  let uu____4705 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4705
                  then (sig_bndle, data_ops_ses)
                  else
                    (let is_unopteq =
                       FStar_List.existsb
                         (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals
                        in
                     let ses1 =
                       if is_unopteq
                       then
                         FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                           sig_bndle tcs datas env1
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1
                        in
                     (sig_bndle, (FStar_List.append ses1 data_ops_ses)))
                   in
                (let uu____4727 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____4732 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____4732 en  in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh (); env
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4767 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4792 ->
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
           let ses1 =
             let uu____4847 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env2)
                in
             if uu____4847
             then
               let ses1 =
                 let uu____4853 =
                   let uu____4854 =
                     let uu____4855 =
                       tc_inductive
                         (let uu___78_4864 = env2  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___78_4864.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___78_4864.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___78_4864.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___78_4864.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___78_4864.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___78_4864.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___78_4864.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___78_4864.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___78_4864.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___78_4864.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___78_4864.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___78_4864.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___78_4864.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___78_4864.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___78_4864.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___78_4864.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___78_4864.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___78_4864.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___78_4864.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___78_4864.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___78_4864.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___78_4864.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___78_4864.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___78_4864.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___78_4864.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___78_4864.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___78_4864.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___78_4864.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___78_4864.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___78_4864.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___78_4864.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___78_4864.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___78_4864.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___78_4864.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___78_4864.FStar_TypeChecker_Env.dep_graph)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____4855
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____4854
                     (FStar_TypeChecker_Normalize.elim_uvars env2)
                    in
                 FStar_All.pipe_right uu____4853
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____4876 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____4876
                 then
                   let uu____4877 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___79_4880 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___79_4880.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___79_4880.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___79_4880.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___79_4880.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____4877
                 else ());
                ses1)
             else ses  in
           let uu____4887 =
             tc_inductive env2 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4887 with
            | (sigbndle,projectors_ses) -> ([sigbndle], projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4919 = cps_and_elaborate env1 ne  in
           (match uu____4919 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___80_4956 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___80_4956.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___80_4956.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___80_4956.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___80_4956.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___81_4958 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___81_4958.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___81_4958.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___81_4958.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___81_4958.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____4965 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____4965
             then
               let ne1 =
                 let uu____4967 =
                   let uu____4968 =
                     let uu____4969 =
                       tc_eff_decl
                         (let uu___82_4972 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___82_4972.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___82_4972.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___82_4972.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___82_4972.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___82_4972.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___82_4972.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___82_4972.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___82_4972.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___82_4972.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___82_4972.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___82_4972.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___82_4972.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___82_4972.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___82_4972.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___82_4972.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___82_4972.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___82_4972.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___82_4972.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___82_4972.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___82_4972.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___82_4972.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___82_4972.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___82_4972.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___82_4972.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___82_4972.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___82_4972.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___82_4972.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___82_4972.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___82_4972.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___82_4972.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___82_4972.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___82_4972.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___82_4972.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___82_4972.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___82_4972.FStar_TypeChecker_Env.dep_graph)
                          }) ne
                        in
                     FStar_All.pipe_right uu____4969
                       (fun ne1  ->
                          let uu___83_4976 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___83_4976.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___83_4976.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___83_4976.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___83_4976.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____4968
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____4967
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____4978 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____4978
                 then
                   let uu____4979 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___84_4982 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___84_4982.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___84_4982.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___84_4982.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___84_4982.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____4979
                 else ());
                ne1)
             else ne  in
           let ne2 = tc_eff_decl env1 ne1  in
           let se1 =
             let uu___85_4987 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___85_4987.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___85_4987.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___85_4987.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___85_4987.FStar_Syntax_Syntax.sigattrs)
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
           let uu____4995 =
             let uu____5002 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5002
              in
           (match uu____4995 with
            | (a,wp_a_src) ->
                let uu____5017 =
                  let uu____5024 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____5024
                   in
                (match uu____5017 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____5040 =
                         let uu____5043 =
                           let uu____5044 =
                             let uu____5051 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____5051)  in
                           FStar_Syntax_Syntax.NT uu____5044  in
                         [uu____5043]  in
                       FStar_Syntax_Subst.subst uu____5040 wp_b_tgt  in
                     let expected_k =
                       let uu____5055 =
                         let uu____5062 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____5063 =
                           let uu____5066 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____5066]  in
                         uu____5062 :: uu____5063  in
                       let uu____5067 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____5055 uu____5067  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5088 =
                           let uu____5093 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5093)
                            in
                         let uu____5094 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____5088 uu____5094  in
                       let uu____5097 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____5097 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____5129 =
                             let uu____5130 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____5130  in
                           if uu____5129
                           then no_reify eff_name
                           else
                             (let uu____5136 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____5137 =
                                let uu____5140 =
                                  let uu____5141 =
                                    let uu____5156 =
                                      let uu____5159 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____5160 =
                                        let uu____5163 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____5163]  in
                                      uu____5159 :: uu____5160  in
                                    (repr, uu____5156)  in
                                  FStar_Syntax_Syntax.Tm_app uu____5141  in
                                FStar_Syntax_Syntax.mk uu____5140  in
                              uu____5137 FStar_Pervasives_Native.None
                                uu____5136)
                        in
                     let uu____5169 =
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
                               let uu____5222 =
                                 let uu____5225 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 FStar_Pervasives_Native.fst uu____5225  in
                               FStar_Syntax_Subst.subst uu____5222 lift_wp
                             else lift_wp  in
                           let uu____5239 =
                             check_and_gen env1 lift_wp1 expected_k  in
                           (lift, uu____5239)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let lift1 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5265 =
                                 let uu____5268 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 FStar_Pervasives_Native.fst uu____5268  in
                               FStar_Syntax_Subst.subst uu____5265 lift
                             else lift  in
                           ((let uu____5283 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5283
                             then
                               let uu____5284 =
                                 FStar_Syntax_Print.term_to_string lift1  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5284
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5287 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift1
                                in
                             match uu____5287 with
                             | (lift2,comp,uu____5302) ->
                                 let uu____5303 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift2
                                    in
                                 (match uu____5303 with
                                  | (uu____5316,lift_wp,lift_elab) ->
                                      let uu____5319 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5320 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____5169 with
                      | (lift,lift_wp) ->
                          let env2 =
                            let uu___86_5360 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___86_5360.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___86_5360.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___86_5360.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___86_5360.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___86_5360.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___86_5360.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___86_5360.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___86_5360.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___86_5360.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___86_5360.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___86_5360.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___86_5360.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___86_5360.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___86_5360.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___86_5360.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___86_5360.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___86_5360.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___86_5360.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___86_5360.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___86_5360.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___86_5360.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___86_5360.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___86_5360.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___86_5360.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___86_5360.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___86_5360.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___86_5360.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___86_5360.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___86_5360.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___86_5360.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___86_5360.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___86_5360.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___86_5360.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___86_5360.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___86_5360.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let lift2 =
                                  let uu____5379 =
                                    let uu____5382 =
                                      FStar_Syntax_Subst.univ_var_opening uvs
                                       in
                                    FStar_Pervasives_Native.fst uu____5382
                                     in
                                  FStar_Syntax_Subst.subst uu____5379 lift1
                                   in
                                let uu____5395 =
                                  let uu____5402 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5402
                                   in
                                (match uu____5395 with
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
                                         let uu____5426 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5427 =
                                           let uu____5430 =
                                             let uu____5431 =
                                               let uu____5446 =
                                                 let uu____5449 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5450 =
                                                   let uu____5453 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5453]  in
                                                 uu____5449 :: uu____5450  in
                                               (lift_wp1, uu____5446)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5431
                                              in
                                           FStar_Syntax_Syntax.mk uu____5430
                                            in
                                         uu____5427
                                           FStar_Pervasives_Native.None
                                           uu____5426
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5462 =
                                         let uu____5469 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5470 =
                                           let uu____5473 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5474 =
                                             let uu____5477 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5477]  in
                                           uu____5473 :: uu____5474  in
                                         uu____5469 :: uu____5470  in
                                       let uu____5478 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5462
                                         uu____5478
                                        in
                                     let uu____5481 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5481 with
                                      | (expected_k2,uu____5491,uu____5492)
                                          ->
                                          let lift3 =
                                            check_and_gen env2 lift2
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift3))
                             in
                          let sub2 =
                            let uu___87_5495 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___87_5495.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___87_5495.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___88_5497 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___88_5497.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___88_5497.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___88_5497.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___88_5497.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let uu____5512 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (uvs, tps, c)
             else
               (let uu____5526 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____5526 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____5553 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____5553 c  in
                    (uvs1, tps1, c1))
              in
           (match uu____5512 with
            | (uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____5574 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____5574 with
                 | (tps2,c2) ->
                     let uu____5589 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____5589 with
                      | (tps3,env3,us) ->
                          let uu____5607 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____5607 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____5628 =
                                   let uu____5629 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____5629
                                    in
                                 match uu____5628 with
                                 | (uvs2,t) ->
                                     let uu____5644 =
                                       let uu____5657 =
                                         let uu____5662 =
                                           let uu____5663 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____5663.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____5662)  in
                                       match uu____5657 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____5678,c5)) -> ([], c5)
                                       | (uu____5718,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____5745 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____5644 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____5789 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____5789 with
                                              | (uu____5794,t1) ->
                                                  let uu____5796 =
                                                    let uu____5801 =
                                                      let uu____5802 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____5803 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____5804 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____5802 uu____5803
                                                        uu____5804
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____5801)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5796 r)
                                           else ();
                                           (let se1 =
                                              let uu___89_5807 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___89_5807.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___89_5807.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___89_5807.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___89_5807.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5824,uu____5825,uu____5826) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___58_5830  ->
                   match uu___58_5830 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5831 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5836,uu____5837) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___58_5845  ->
                   match uu___58_5845 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5846 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5856 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5856
             then
               let uu____5857 =
                 let uu____5862 =
                   let uu____5863 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____5863
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5862)
                  in
               FStar_Errors.raise_error uu____5857 r
             else ());
            (let uu____5865 =
               if uvs = []
               then
                 let uu____5866 =
                   let uu____5867 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____5867  in
                 check_and_gen env2 t uu____5866
               else
                 (let uu____5873 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____5873 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5881 =
                          let uu____5882 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____5882  in
                        tc_check_trivial_guard env2 t1 uu____5881  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____5888 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____5888))
                in
             match uu____5865 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___90_5904 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___90_5904.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___90_5904.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___90_5904.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___90_5904.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5914 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____5914 with
            | (uu____5927,phi1) ->
                let phi2 =
                  let uu____5930 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env1)
                     in
                  if uu____5930
                  then
                    let phi2 =
                      let uu____5932 =
                        tc_assume
                          (let uu___91_5935 = env1  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___91_5935.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___91_5935.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___91_5935.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___91_5935.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___91_5935.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___91_5935.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___91_5935.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___91_5935.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___91_5935.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___91_5935.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___91_5935.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___91_5935.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___91_5935.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___91_5935.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___91_5935.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___91_5935.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___91_5935.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___91_5935.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___91_5935.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___91_5935.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___91_5935.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___91_5935.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___91_5935.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___91_5935.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___91_5935.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___91_5935.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___91_5935.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___91_5935.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___91_5935.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___91_5935.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___91_5935.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___91_5935.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___91_5935.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___91_5935.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___91_5935.FStar_TypeChecker_Env.dep_graph)
                           }) phi1 r
                         in
                      FStar_All.pipe_right uu____5932
                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                           env1)
                       in
                    ((let uu____5937 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____5937
                      then
                        let uu____5938 =
                          FStar_Syntax_Print.term_to_string phi2  in
                        FStar_Util.print1 "Assume after phase 1: %s\n"
                          uu____5938
                      else ());
                     phi2)
                  else phi1  in
                let phi3 = tc_assume env1 phi2 r  in
                let uu____5942 =
                  FStar_TypeChecker_Util.generalize_universes env1 phi3  in
                (match uu____5942 with
                 | (us1,phi4) ->
                     ([{
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_assume (lid, us1, phi4));
                         FStar_Syntax_Syntax.sigrng = r;
                         FStar_Syntax_Syntax.sigquals =
                           (se.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }], [])))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit
              in
           let uu____5966 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____5966 with
            | (e1,c,g1) ->
                let uu____5984 =
                  let uu____5991 =
                    let uu____5994 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____5994  in
                  let uu____5995 =
                    let uu____6000 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____6000)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5991 uu____5995
                   in
                (match uu____5984 with
                 | (e2,uu____6010,g) ->
                     ((let uu____6013 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____6013);
                      (let se1 =
                         let uu___92_6015 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_6015.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___92_6015.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_6015.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_6015.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____6027 = FStar_Options.debug_any ()  in
             if uu____6027
             then
               let uu____6028 =
                 FStar_Ident.string_of_lid
                   env1.FStar_TypeChecker_Env.curmodule
                  in
               let uu____6029 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____6028
                 uu____6029
             else ());
            (let ses = env1.FStar_TypeChecker_Env.splice env1 t  in
             let lids' =
               FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses  in
             FStar_List.iter
               (fun lid  ->
                  let uu____6042 =
                    FStar_List.tryFind (FStar_Ident.lid_equals lid) lids'  in
                  match uu____6042 with
                  | FStar_Pervasives_Native.Some uu____6045 -> ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____6046 =
                        let uu____6051 =
                          let uu____6052 = FStar_Ident.string_of_lid lid  in
                          let uu____6053 =
                            let uu____6054 =
                              FStar_List.map FStar_Ident.string_of_lid lids'
                               in
                            FStar_All.pipe_left (FStar_String.concat ", ")
                              uu____6054
                             in
                          FStar_Util.format2
                            "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                            uu____6052 uu____6053
                           in
                        (FStar_Errors.Fatal_SplicedUndef, uu____6051)  in
                      FStar_Errors.raise_error uu____6046 r) lids;
             ([], ses)))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____6109 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____6109
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____6117 =
                      let uu____6122 =
                        let uu____6123 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____6124 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____6125 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____6123 uu____6124 uu____6125
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____6122)
                       in
                    FStar_Errors.raise_error uu____6117 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____6151 =
                   let uu____6152 = FStar_Syntax_Subst.compress def  in
                   uu____6152.FStar_Syntax_Syntax.n  in
                 match uu____6151 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6162,uu____6163)
                     -> binders
                 | uu____6184 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6194;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6272) -> val_bs1
                     | (uu____6295,[]) -> val_bs1
                     | ((body_bv,uu____6319)::bt,(val_bv,aqual)::vt) ->
                         let uu____6356 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6372) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___93_6374 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___94_6377 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___94_6377.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___93_6374.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___93_6374.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6356
                      in
                   let uu____6378 =
                     let uu____6381 =
                       let uu____6382 =
                         let uu____6395 = rename_binders1 def_bs val_bs  in
                         (uu____6395, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6382  in
                     FStar_Syntax_Syntax.mk uu____6381  in
                   uu____6378 FStar_Pervasives_Native.None r1
               | uu____6413 -> typ1  in
             let uu___95_6414 = lb  in
             let uu____6415 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___95_6414.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___95_6414.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6415;
               FStar_Syntax_Syntax.lbeff =
                 (uu___95_6414.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___95_6414.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___95_6414.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___95_6414.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____6418 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6469  ->
                     fun lb  ->
                       match uu____6469 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6511 =
                             let uu____6522 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6522 with
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
                                   | uu____6607 ->
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
                                  (let uu____6650 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def,
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____6650, quals_opt1)))
                              in
                           (match uu____6511 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6418 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6744 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___59_6748  ->
                                match uu___59_6748 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6749 -> false))
                         in
                      if uu____6744
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6759 =
                    let uu____6762 =
                      let uu____6763 =
                        let uu____6776 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6776)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6763  in
                    FStar_Syntax_Syntax.mk uu____6762  in
                  uu____6759 FStar_Pervasives_Native.None r  in
                let env0 =
                  let uu___96_6795 = env2  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___96_6795.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___96_6795.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___96_6795.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___96_6795.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___96_6795.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___96_6795.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___96_6795.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___96_6795.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___96_6795.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___96_6795.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___96_6795.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___96_6795.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___96_6795.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___96_6795.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___96_6795.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___96_6795.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___96_6795.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___96_6795.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___96_6795.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___96_6795.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___96_6795.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___96_6795.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___96_6795.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___96_6795.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___96_6795.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___96_6795.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___96_6795.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___96_6795.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___96_6795.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___96_6795.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___96_6795.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___96_6795.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___96_6795.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___96_6795.FStar_TypeChecker_Env.dep_graph)
                  }  in
                let e1 =
                  let uu____6797 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env0)
                     in
                  if uu____6797
                  then
                    let drop_lbtyp e_lax =
                      let uu____6802 =
                        let uu____6803 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____6803.FStar_Syntax_Syntax.n  in
                      match uu____6802 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____6821 =
                              let uu____6822 = FStar_Syntax_Subst.compress e
                                 in
                              uu____6822.FStar_Syntax_Syntax.n  in
                            match uu____6821 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____6825,lb1::[]),uu____6827) ->
                                let uu____6840 =
                                  let uu____6841 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____6841.FStar_Syntax_Syntax.n  in
                                uu____6840 = FStar_Syntax_Syntax.Tm_unknown
                            | uu____6844 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___97_6845 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___98_6857 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___98_6857.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___98_6857.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___98_6857.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___98_6857.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___98_6857.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___98_6857.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___97_6845.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___97_6845.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____6859 -> e_lax  in
                    let e1 =
                      let uu____6861 =
                        let uu____6862 =
                          let uu____6863 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___99_6872 = env0  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___99_6872.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___99_6872.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___99_6872.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___99_6872.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___99_6872.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___99_6872.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___99_6872.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___99_6872.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___99_6872.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___99_6872.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___99_6872.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___99_6872.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___99_6872.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___99_6872.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___99_6872.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___99_6872.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___99_6872.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___99_6872.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___99_6872.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___99_6872.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___99_6872.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___99_6872.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___99_6872.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___99_6872.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___99_6872.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___99_6872.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___99_6872.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___99_6872.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___99_6872.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___99_6872.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___99_6872.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___99_6872.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___99_6872.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___99_6872.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___99_6872.FStar_TypeChecker_Env.dep_graph)
                               }) e
                             in
                          FStar_All.pipe_right uu____6863
                            (fun uu____6883  ->
                               match uu____6883 with
                               | (e1,uu____6891,uu____6892) -> e1)
                           in
                        FStar_All.pipe_right uu____6862
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env0)
                         in
                      FStar_All.pipe_right uu____6861 drop_lbtyp  in
                    ((let uu____6894 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env2)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____6894
                      then
                        let uu____6895 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____6895
                      else ());
                     e1)
                  else e  in
                let uu____6898 =
                  let uu____6909 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1
                     in
                  match uu____6909 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e2);
                       FStar_Syntax_Syntax.pos = uu____6928;
                       FStar_Syntax_Syntax.vars = uu____6929;_},uu____6930,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6959 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6959)  in
                      let quals1 =
                        match e2.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6977,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6982 -> quals  in
                      ((let uu___100_6990 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___100_6990.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___100_6990.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___100_6990.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6999 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6898 with
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
                      (let uu____7048 = log env2  in
                       if uu____7048
                       then
                         let uu____7049 =
                           let uu____7050 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____7065 =
                                         let uu____7074 =
                                           let uu____7075 =
                                             let uu____7078 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____7078.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____7075.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____7074
                                          in
                                       match uu____7065 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____7085 -> false  in
                                     if should_log
                                     then
                                       let uu____7094 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____7095 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____7094 uu____7095
                                     else ""))
                              in
                           FStar_All.pipe_right uu____7050
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____7049
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
             (fun uu___60_7141  ->
                match uu___60_7141 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7142 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7148) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7154 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7163 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____7168 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7183 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7208 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7232) ->
          let uu____7241 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7241
          then
            let for_export_bundle se1 uu____7272 =
              match uu____7272 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7311,uu____7312) ->
                       let dec =
                         let uu___101_7322 = se1  in
                         let uu____7323 =
                           let uu____7324 =
                             let uu____7331 =
                               let uu____7334 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7334  in
                             (l, us, uu____7331)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7324  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7323;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___101_7322.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___101_7322.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___101_7322.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7346,uu____7347,uu____7348) ->
                       let dec =
                         let uu___102_7354 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___102_7354.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___102_7354.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___102_7354.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7359 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7381,uu____7382,uu____7383) ->
          let uu____7384 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7384 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7405 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7405
          then
            ([(let uu___103_7421 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___103_7421.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___103_7421.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___103_7421.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7423 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___61_7427  ->
                       match uu___61_7427 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7428 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7433 -> true
                       | uu____7434 -> false))
                in
             if uu____7423 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7452 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7457 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7462 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7467 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7472 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7490) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7507 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7507
          then ([], hidden)
          else
            (let dec =
               let uu____7524 = FStar_Ident.range_of_lid lid  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____7524;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____7539 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7539
          then
            let uu____7548 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___104_7561 = se  in
                      let uu____7562 =
                        let uu____7563 =
                          let uu____7570 =
                            let uu____7571 =
                              let uu____7574 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7574.FStar_Syntax_Syntax.fv_name  in
                            uu____7571.FStar_Syntax_Syntax.v  in
                          (uu____7570, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7563  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7562;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___104_7561.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___104_7561.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___104_7561.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7548, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7594 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7611 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7626) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____7629 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7630 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7640 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7640) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7641,uu____7642,uu____7643) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7647  ->
                  match uu___62_7647 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7648 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7649,uu____7650) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7658  ->
                  match uu___62_7658 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7659 -> false))
          -> env
      | uu____7660 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7720 se =
        match uu____7720 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7773 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7773
              then
                let uu____7774 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7774
              else ());
             (let uu____7776 = tc_decl env1 se  in
              match uu____7776 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7826 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____7826
                             then
                               let uu____7827 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7827
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
                    (let uu____7850 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____7850
                     then
                       let uu____7851 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7857 =
                                  let uu____7858 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____7858 "\n"  in
                                Prims.strcat s uu____7857) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____7851
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7863 =
                       let uu____7872 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____7872
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____7907 se1 =
                            match uu____7907 with
                            | (exports1,hidden1) ->
                                let uu____7935 = for_export hidden1 se1  in
                                (match uu____7935 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____7863 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___105_8014 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___105_8014.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___105_8014.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___105_8014.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___105_8014.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____8092 = acc  in
        match uu____8092 with
        | (uu____8127,uu____8128,env1,uu____8130) ->
            let uu____8143 =
              FStar_Util.record_time
                (fun uu____8189  -> process_one_decl acc se)
               in
            (match uu____8143 with
             | (r,ms_elapsed) ->
                 ((let uu____8253 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8253
                   then
                     let uu____8254 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8255 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8254 uu____8255
                   else ());
                  r))
         in
      let uu____8257 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8257 with
      | (ses1,exports,env1,uu____8305) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___106_8336 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___106_8336.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___106_8336.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___106_8336.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___106_8336.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___106_8336.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___106_8336.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___106_8336.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___106_8336.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___106_8336.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___106_8336.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___106_8336.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___106_8336.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___106_8336.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___106_8336.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___106_8336.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___106_8336.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___106_8336.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___106_8336.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___106_8336.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___106_8336.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___106_8336.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___106_8336.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___106_8336.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___106_8336.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___106_8336.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___106_8336.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___106_8336.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___106_8336.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___106_8336.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___106_8336.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___106_8336.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___106_8336.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___106_8336.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8347 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8347 with
          | (univs2,t1) ->
              ((let uu____8355 =
                  let uu____8356 =
                    let uu____8359 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8359  in
                  FStar_All.pipe_left uu____8356
                    (FStar_Options.Other "Exports")
                   in
                if uu____8355
                then
                  let uu____8360 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8361 =
                    let uu____8362 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8362
                      (FStar_String.concat ", ")
                     in
                  let uu____8371 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8360 uu____8361 uu____8371
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____8374 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____8374 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____8398 =
             let uu____8399 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8400 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8399 uu____8400
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8398);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8407) ->
              let uu____8416 =
                let uu____8417 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8417  in
              if uu____8416
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8427,uu____8428) ->
              let t =
                let uu____8440 =
                  let uu____8443 =
                    let uu____8444 =
                      let uu____8457 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8457)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8444  in
                  FStar_Syntax_Syntax.mk uu____8443  in
                uu____8440 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8464,uu____8465,uu____8466) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8474 =
                let uu____8475 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8475  in
              if uu____8474 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8479,lbs),uu____8481) ->
              let uu____8496 =
                let uu____8497 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8497  in
              if uu____8496
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
              let uu____8516 =
                let uu____8517 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8517  in
              if uu____8516
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8524 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8525 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8532 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8533 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8534 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____8535 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8542 -> ()  in
        let uu____8543 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____8543 then () else FStar_List.iter check_sigelt exports
  
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
      let abstract_inductive_tycons = FStar_Util.mk_ref []  in
      let abstract_inductive_datacons = FStar_Util.mk_ref []  in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q  ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l,uu____8620) -> true
             | uu____8621 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8640 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____8671 ->
                   let uu____8672 =
                     let uu____8675 =
                       let uu____8676 =
                         let uu____8689 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____8689)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____8676  in
                     FStar_Syntax_Syntax.mk uu____8675  in
                   uu____8672 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____8697,uu____8698) ->
            let s1 =
              let uu___107_8708 = s  in
              let uu____8709 =
                let uu____8710 =
                  let uu____8717 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____8717)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____8710  in
              let uu____8718 =
                let uu____8721 =
                  let uu____8724 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____8724  in
                FStar_Syntax_Syntax.Assumption :: uu____8721  in
              {
                FStar_Syntax_Syntax.sigel = uu____8709;
                FStar_Syntax_Syntax.sigrng =
                  (uu___107_8708.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____8718;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___107_8708.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___107_8708.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____8727 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____8741 =
        match uu____8741 with
        | (uvs,t) ->
            let uu___108_8748 = s  in
            let uu____8749 =
              let uu____8752 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____8752  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___108_8748.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____8749;
              FStar_Syntax_Syntax.sigmeta =
                (uu___108_8748.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___108_8748.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____8764 -> failwith "Impossible!"  in
        let c_opt =
          let uu____8768 = FStar_Syntax_Util.is_unit t  in
          if uu____8768
          then
            let uu____8771 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____8771
          else
            (let uu____8773 =
               let uu____8774 = FStar_Syntax_Subst.compress t  in
               uu____8774.FStar_Syntax_Syntax.n  in
             match uu____8773 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____8779,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____8799 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____8808 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____8808
           then
             let uu____8809 =
               let uu____8810 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____8810 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____8809
           else
             (let uu____8818 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect env uu____8818))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____8827 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____8846 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_splice uu____8863 ->
            failwith "Impossible! Trying to extract splice"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____8903,uu____8904,uu____8905,uu____8906,uu____8907)
                         ->
                         ((let uu____8917 =
                             let uu____8920 =
                               FStar_ST.op_Bang abstract_inductive_tycons  in
                             lid :: uu____8920  in
                           FStar_ST.op_Colon_Equals abstract_inductive_tycons
                             uu____8917);
                          (let uu____9013 = vals_of_abstract_inductive s1  in
                           FStar_List.append uu____9013 sigelts1))
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____9017,uu____9018,uu____9019,uu____9020,uu____9021)
                         ->
                         ((let uu____9027 =
                             let uu____9030 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____9030  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____9027);
                          sigelts1)
                     | uu____9123 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9130 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9130
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____9136 =
                   let uu___109_9137 = s  in
                   let uu____9138 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___109_9137.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___109_9137.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9138;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___109_9137.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___109_9137.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9136])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____9148 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9148
            then []
            else
              (let uu____9152 = lbs  in
               match uu____9152 with
               | (flbs,slbs) ->
                   let typs =
                     FStar_All.pipe_right slbs
                       (FStar_List.map
                          (fun lb  ->
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))))
                      in
                   let is_lemma1 =
                     FStar_List.existsML
                       (fun uu____9208  ->
                          match uu____9208 with
                          | (uu____9215,t) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____9233  ->
                            match uu____9233 with
                            | (u,t) -> val_of_lb s lid (u, t)) lids typs
                      in
                   if
                     ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                        (is_irreducible1 s.FStar_Syntax_Syntax.sigquals))
                       || is_lemma1
                   then vals
                   else
                     (let should_keep_defs =
                        FStar_List.existsML
                          (fun uu____9253  ->
                             match uu____9253 with
                             | (uu____9260,t) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____9273,uu____9274) ->
            let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____9279 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____9330 =
                       FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                        in
                     FStar_Ident.lid_equals lid uu____9330) uu____9279
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____9333 =
                   let uu___110_9334 = s  in
                   let uu____9335 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___110_9334.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___110_9334.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9335;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___110_9334.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___110_9334.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9333]
               else [])
            else
              (let uu____9340 =
                 let uu___111_9341 = s  in
                 let uu____9342 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___111_9341.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___111_9341.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____9342;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___111_9341.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___111_9341.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____9340])
        | FStar_Syntax_Syntax.Sig_new_effect uu____9345 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9346 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____9347 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9348 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____9361 -> [s]  in
      let uu___112_9362 = m  in
      let uu____9363 =
        let uu____9364 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____9364  in
      {
        FStar_Syntax_Syntax.name = (uu___112_9362.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9363;
        FStar_Syntax_Syntax.exports =
          (uu___112_9362.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      (let uu____9378 = FStar_Syntax_DsEnv.pop ()  in
       FStar_All.pipe_right uu____9378 FStar_Pervasives.ignore);
      (let en = FStar_TypeChecker_Env.pop env msg  in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
       en)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let dsenv1 = FStar_Syntax_DsEnv.push env.FStar_TypeChecker_Env.dsenv
         in
      let env1 = FStar_TypeChecker_Env.push env msg  in
      let uu___113_9389 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___113_9389.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___113_9389.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___113_9389.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___113_9389.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___113_9389.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___113_9389.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___113_9389.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___113_9389.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___113_9389.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___113_9389.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___113_9389.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___113_9389.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___113_9389.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___113_9389.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___113_9389.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___113_9389.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___113_9389.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___113_9389.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___113_9389.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___113_9389.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___113_9389.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___113_9389.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___113_9389.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___113_9389.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___113_9389.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___113_9389.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___113_9389.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___113_9389.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___113_9389.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___113_9389.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___113_9389.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___113_9389.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___113_9389.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___113_9389.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv1;
        FStar_TypeChecker_Env.dep_graph =
          (uu___113_9389.FStar_TypeChecker_Env.dep_graph)
      }
  
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
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
      (let uu____9410 = FStar_Options.debug_any ()  in
       if uu____9410
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
       let env1 =
         let uu___114_9415 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___114_9415.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___114_9415.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___114_9415.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___114_9415.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___114_9415.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___114_9415.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___114_9415.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___114_9415.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___114_9415.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___114_9415.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___114_9415.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___114_9415.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___114_9415.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___114_9415.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___114_9415.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___114_9415.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___114_9415.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___114_9415.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___114_9415.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___114_9415.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___114_9415.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___114_9415.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___114_9415.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___114_9415.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___114_9415.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___114_9415.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___114_9415.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___114_9415.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___114_9415.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___114_9415.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___114_9415.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___114_9415.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___114_9415.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___114_9415.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____9417 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____9417 with
       | (ses,exports,env3) ->
           ((let uu___115_9450 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___115_9450.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___115_9450.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___115_9450.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
  
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
        let uu____9472 = tc_decls env decls  in
        match uu____9472 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___116_9503 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___116_9503.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___116_9503.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___116_9503.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
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
        let uu____9548 =
          FStar_Ident.lid_equals env0.FStar_TypeChecker_Env.curmodule
            FStar_Parser_Const.prims_lid
           in
        if uu____9548
        then
          let uu___117_9549 = env0  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___117_9549.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___117_9549.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___117_9549.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___117_9549.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___117_9549.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___117_9549.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___117_9549.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___117_9549.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___117_9549.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___117_9549.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___117_9549.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___117_9549.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___117_9549.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___117_9549.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___117_9549.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___117_9549.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___117_9549.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___117_9549.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes =
              (uu___117_9549.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___117_9549.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___117_9549.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___117_9549.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___117_9549.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___117_9549.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___117_9549.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___117_9549.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___117_9549.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___117_9549.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___117_9549.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___117_9549.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___117_9549.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___117_9549.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___117_9549.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___117_9549.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___117_9549.FStar_TypeChecker_Env.dep_graph)
          }
        else env0  in
      let msg =
        Prims.strcat "Internals for "
          (m.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let env02 = push_context env01 msg  in
      let uu____9553 = tc_partial_modul env02 m  in
      match uu____9553 with
      | (modul,non_private_decls,env) ->
          let uu____9577 =
            finish_partial_modul false env modul non_private_decls  in
          (match uu____9577 with
           | (m1,m_opt,env1) ->
               (m1, m_opt,
                 (let uu___118_9604 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___118_9604.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___118_9604.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___118_9604.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___118_9604.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___118_9604.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___118_9604.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___118_9604.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___118_9604.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___118_9604.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___118_9604.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___118_9604.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___118_9604.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___118_9604.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___118_9604.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___118_9604.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___118_9604.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___118_9604.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___118_9604.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = lax_mode;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___118_9604.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___118_9604.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___118_9604.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___118_9604.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___118_9604.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___118_9604.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___118_9604.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___118_9604.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___118_9604.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___118_9604.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___118_9604.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___118_9604.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___118_9604.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___118_9604.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___118_9604.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___118_9604.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___118_9604.FStar_TypeChecker_Env.dep_graph)
                  })))

and (finish_partial_modul :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                       FStar_Pervasives_Native.option,
            FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun loading_from_cache  ->
    fun en  ->
      fun m  ->
        fun exports  ->
          let uu____9619 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
             in
          if uu____9619
          then
            let en0 =
              pop_context en
                (Prims.strcat "Ending modul "
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
               in
            let en01 =
              let uu___119_9630 = en0  in
              let uu____9631 =
                let uu____9644 =
                  FStar_All.pipe_right
                    en.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                (uu____9644, FStar_Pervasives_Native.None)  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___119_9630.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___119_9630.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___119_9630.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___119_9630.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___119_9630.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___119_9630.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___119_9630.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___119_9630.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___119_9630.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___119_9630.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___119_9630.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___119_9630.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___119_9630.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___119_9630.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___119_9630.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___119_9630.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___119_9630.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___119_9630.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___119_9630.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___119_9630.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___119_9630.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___119_9630.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___119_9630.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___119_9630.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___119_9630.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___119_9630.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___119_9630.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index = uu____9631;
                FStar_TypeChecker_Env.proof_ns =
                  (uu___119_9630.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___119_9630.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___119_9630.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___119_9630.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___119_9630.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___119_9630.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___119_9630.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___119_9630.FStar_TypeChecker_Env.dep_graph)
              }  in
            let en02 =
              let uu____9682 =
                let uu____9683 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9683  in
              if uu____9682
              then
                ((let uu____9685 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____9685 FStar_Pervasives.ignore);
                 z3_reset_options en01)
              else en01  in
            let modul_iface = extract_interface en m  in
            ((let uu____9689 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                  FStar_Options.Low
                 in
              if uu____9689
              then
                let uu____9690 =
                  let uu____9691 =
                    FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9691 then "" else " (in lax mode) "  in
                let uu____9693 =
                  let uu____9694 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9694
                  then
                    let uu____9695 =
                      let uu____9696 = FStar_Syntax_Print.modul_to_string m
                         in
                      Prims.strcat uu____9696 "\n"  in
                    Prims.strcat "\nfrom: " uu____9695
                  else ""  in
                let uu____9698 =
                  let uu____9699 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9699
                  then
                    let uu____9700 =
                      let uu____9701 =
                        FStar_Syntax_Print.modul_to_string modul_iface  in
                      Prims.strcat uu____9701 "\n"  in
                    Prims.strcat "\nto: " uu____9700
                  else ""  in
                FStar_Util.print4
                  "Extracting and type checking module %s interface%s%s%s\n"
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____9690
                  uu____9693 uu____9698
              else ());
             (let env0 =
                let uu___120_9705 = en02  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___120_9705.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___120_9705.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___120_9705.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___120_9705.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___120_9705.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___120_9705.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___120_9705.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___120_9705.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___120_9705.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___120_9705.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___120_9705.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___120_9705.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___120_9705.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___120_9705.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___120_9705.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___120_9705.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface = true;
                  FStar_TypeChecker_Env.admit =
                    (uu___120_9705.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___120_9705.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___120_9705.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___120_9705.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___120_9705.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___120_9705.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___120_9705.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___120_9705.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___120_9705.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___120_9705.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___120_9705.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___120_9705.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___120_9705.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___120_9705.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___120_9705.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___120_9705.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___120_9705.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___120_9705.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___120_9705.FStar_TypeChecker_Env.dep_graph)
                }  in
              let uu____9706 = tc_modul en02 modul_iface  in
              match uu____9706 with
              | (modul_iface1,must_be_none,env) ->
                  if must_be_none <> FStar_Pervasives_Native.None
                  then
                    failwith
                      "Impossible! Expected the second component to be None"
                  else
                    (((let uu___121_9752 = m  in
                       {
                         FStar_Syntax_Syntax.name =
                           (uu___121_9752.FStar_Syntax_Syntax.name);
                         FStar_Syntax_Syntax.declarations =
                           (uu___121_9752.FStar_Syntax_Syntax.declarations);
                         FStar_Syntax_Syntax.exports =
                           (modul_iface1.FStar_Syntax_Syntax.exports);
                         FStar_Syntax_Syntax.is_interface =
                           (uu___121_9752.FStar_Syntax_Syntax.is_interface)
                       })), (FStar_Pervasives_Native.Some modul_iface1), env)))
          else
            (let modul =
               let uu____9755 = FStar_Options.use_extracted_interfaces ()  in
               if uu____9755
               then
                 let uu___122_9756 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___122_9756.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___122_9756.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___122_9756.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___123_9758 = m  in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___123_9758.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___123_9758.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___123_9758.FStar_Syntax_Syntax.is_interface)
                  })
                in
             let env = FStar_TypeChecker_Env.finish_module en modul  in
             (let uu____9761 =
                FStar_All.pipe_right
                  env.FStar_TypeChecker_Env.qtbl_name_and_index
                  FStar_Pervasives_Native.fst
                 in
              FStar_All.pipe_right uu____9761 FStar_Util.smap_clear);
             (let uu____9789 =
                ((let uu____9792 = FStar_Options.lax ()  in
                  Prims.op_Negation uu____9792) &&
                   (let uu____9794 =
                      FStar_Options.use_extracted_interfaces ()  in
                    Prims.op_Negation uu____9794))
                  && (Prims.op_Negation loading_from_cache)
                 in
              if uu____9789 then check_exports env modul exports else ());
             (let uu____9797 =
                pop_context env
                  (Prims.strcat "Ending modul "
                     (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 in
              FStar_All.pipe_right uu____9797 FStar_Pervasives.ignore);
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
               env modul;
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ();
             (let uu____9801 =
                let uu____9802 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9802  in
              if uu____9801
              then
                let uu____9803 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____9803 FStar_Pervasives.ignore
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
      let env1 =
        let uu____9815 =
          let uu____9816 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____9816  in
        push_context env uu____9815  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____9835 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____9856 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports  in
      match uu____9856 with | (uu____9865,uu____9866,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      (let uu____9887 = FStar_Options.debug_any ()  in
       if uu____9887
       then
         let uu____9888 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____9888
       else ());
      (let env1 =
         let uu___124_9892 = env  in
         let uu____9893 =
           let uu____9894 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____9894  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_9892.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_9892.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_9892.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_9892.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_9892.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_9892.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_9892.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_9892.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_9892.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_9892.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_9892.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_9892.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___124_9892.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___124_9892.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_9892.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_9892.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___124_9892.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___124_9892.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____9893;
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_9892.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___124_9892.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___124_9892.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___124_9892.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___124_9892.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_9892.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___124_9892.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___124_9892.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___124_9892.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___124_9892.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___124_9892.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___124_9892.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___124_9892.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___124_9892.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___124_9892.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___124_9892.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___124_9892.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____9895 = tc_modul env1 m  in
       match uu____9895 with
       | (m1,m_iface_opt,env2) ->
           ((let uu____9920 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____9920
             then
               let uu____9921 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____9921
             else ());
            (let uu____9924 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____9924
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
                       let uu____9955 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____9955 with
                       | (univnames1,e) ->
                           let uu___125_9962 = lb  in
                           let uu____9963 =
                             let uu____9966 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____9966 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___125_9962.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_9962.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___125_9962.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_9962.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____9963;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___125_9962.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___125_9962.FStar_Syntax_Syntax.lbpos)
                           }
                        in
                     let uu___126_9967 = se  in
                     let uu____9968 =
                       let uu____9969 =
                         let uu____9976 =
                           let uu____9983 = FStar_List.map update lbs  in
                           (b, uu____9983)  in
                         (uu____9976, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____9969  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____9968;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___126_9967.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___126_9967.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___126_9967.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___126_9967.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____9996 -> se  in
               let normalized_module =
                 let uu___127_9998 = m1  in
                 let uu____9999 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___127_9998.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____9999;
                   FStar_Syntax_Syntax.exports =
                     (uu___127_9998.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___127_9998.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____10000 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____10000
             else ());
            (m1, m_iface_opt, env2)))
  