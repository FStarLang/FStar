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
          FStar_Errors.raise_error uu____252 (FStar_Ident.range_of_lid m)  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____296)::(wp,uu____298)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____313 -> fail1 ())
        | uu____314 -> fail1 ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____321 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____321 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____347 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____347 t  in
          let open_univs_binders n_binders bs =
            let uu____357 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____357 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____365 =
            let uu____372 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____373 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____372 uu____373  in
          (match uu____365 with
           | (effect_params_un,signature_un,opening) ->
               let uu____383 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
                  in
               (match uu____383 with
                | (effect_params,env,uu____392) ->
                    let uu____393 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                       in
                    (match uu____393 with
                     | (signature,uu____399) ->
                         let ed1 =
                           let uu___65_401 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___65_401.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___65_401.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___65_401.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___65_401.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___65_401.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___65_401.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___65_401.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___65_401.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___65_401.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___65_401.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___65_401.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___65_401.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___65_401.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___65_401.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___65_401.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___65_401.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___65_401.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___65_401.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____417 ->
                               let op uu____439 =
                                 match uu____439 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____459 =
                                       let uu____460 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____469 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____460
                                         uu____469
                                        in
                                     (us, uu____459)
                                  in
                               let uu___66_478 = ed1  in
                               let uu____479 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____480 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____481 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____482 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____483 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____484 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____485 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____486 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____487 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____488 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____489 =
                                 let uu____490 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____490  in
                               let uu____501 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____502 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____503 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___67_511 = a  in
                                      let uu____512 =
                                        let uu____513 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____513
                                         in
                                      let uu____522 =
                                        let uu____523 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____523
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___67_511.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___67_511.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___67_511.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___67_511.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____512;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____522
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___66_478.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___66_478.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___66_478.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___66_478.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____479;
                                 FStar_Syntax_Syntax.bind_wp = uu____480;
                                 FStar_Syntax_Syntax.if_then_else = uu____481;
                                 FStar_Syntax_Syntax.ite_wp = uu____482;
                                 FStar_Syntax_Syntax.stronger = uu____483;
                                 FStar_Syntax_Syntax.close_wp = uu____484;
                                 FStar_Syntax_Syntax.assert_p = uu____485;
                                 FStar_Syntax_Syntax.assume_p = uu____486;
                                 FStar_Syntax_Syntax.null_wp = uu____487;
                                 FStar_Syntax_Syntax.trivial = uu____488;
                                 FStar_Syntax_Syntax.repr = uu____489;
                                 FStar_Syntax_Syntax.return_repr = uu____501;
                                 FStar_Syntax_Syntax.bind_repr = uu____502;
                                 FStar_Syntax_Syntax.actions = uu____503;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___66_478.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail1 t =
                             let uu____558 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t
                                in
                             FStar_Errors.raise_error uu____558
                               (FStar_Ident.range_of_lid mname)
                              in
                           let uu____569 =
                             let uu____570 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____570.FStar_Syntax_Syntax.n  in
                           match uu____569 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____605)::(wp,uu____607)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____622 -> fail1 signature1)
                           | uu____623 -> fail1 signature1  in
                         let uu____624 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____624 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____646 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____653 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un
                                       in
                                    (match uu____653 with
                                     | (signature1,uu____665) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____666 ->
                                    let uu____669 =
                                      let uu____674 =
                                        let uu____675 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____675)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____674
                                       in
                                    (match uu____669 with
                                     | (uu____684,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env1 =
                                let uu____687 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env uu____687
                                 in
                              ((let uu____689 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____689
                                then
                                  let uu____690 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____691 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____692 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____693 =
                                    let uu____694 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____694
                                     in
                                  let uu____695 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____690 uu____691 uu____692 uu____693
                                    uu____695
                                else ());
                               (let check_and_gen' env2 uu____711 k =
                                  match uu____711 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____725::uu____726 ->
                                           let uu____729 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____729 with
                                            | (us1,t1) ->
                                                let uu____738 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____738 with
                                                 | (us2,t2) ->
                                                     let uu____745 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k
                                                        in
                                                     let uu____746 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____746))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____751 =
                                      let uu____758 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____759 =
                                        let uu____762 =
                                          let uu____763 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____763
                                           in
                                        [uu____762]  in
                                      uu____758 :: uu____759  in
                                    let uu____764 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____751
                                      uu____764
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____768 = fresh_effect_signature ()
                                     in
                                  match uu____768 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____784 =
                                          let uu____791 =
                                            let uu____792 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____792
                                             in
                                          [uu____791]  in
                                        let uu____793 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____784
                                          uu____793
                                         in
                                      let expected_k =
                                        let uu____799 =
                                          let uu____806 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____807 =
                                            let uu____810 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____811 =
                                              let uu____814 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____815 =
                                                let uu____818 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____819 =
                                                  let uu____822 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____822]  in
                                                uu____818 :: uu____819  in
                                              uu____814 :: uu____815  in
                                            uu____810 :: uu____811  in
                                          uu____806 :: uu____807  in
                                        let uu____823 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____799
                                          uu____823
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____828 =
                                      let uu____829 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____829
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____828
                                     in
                                  let expected_k =
                                    let uu____841 =
                                      let uu____848 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____849 =
                                        let uu____852 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____853 =
                                          let uu____856 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____857 =
                                            let uu____860 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____860]  in
                                          uu____856 :: uu____857  in
                                        uu____852 :: uu____853  in
                                      uu____848 :: uu____849  in
                                    let uu____861 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____841
                                      uu____861
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____868 =
                                      let uu____875 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____876 =
                                        let uu____879 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____879]  in
                                      uu____875 :: uu____876  in
                                    let uu____880 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____868
                                      uu____880
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____884 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____884 with
                                  | (t,uu____890) ->
                                      let expected_k =
                                        let uu____894 =
                                          let uu____901 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____902 =
                                            let uu____905 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____906 =
                                              let uu____909 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____909]  in
                                            uu____905 :: uu____906  in
                                          uu____901 :: uu____902  in
                                        let uu____910 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____894
                                          uu____910
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____915 =
                                      let uu____916 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____916
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____915
                                     in
                                  let b_wp_a =
                                    let uu____928 =
                                      let uu____935 =
                                        let uu____936 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____936
                                         in
                                      [uu____935]  in
                                    let uu____937 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____928
                                      uu____937
                                     in
                                  let expected_k =
                                    let uu____943 =
                                      let uu____950 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____951 =
                                        let uu____954 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____955 =
                                          let uu____958 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____958]  in
                                        uu____954 :: uu____955  in
                                      uu____950 :: uu____951  in
                                    let uu____959 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____943
                                      uu____959
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
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
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____999 =
                                      let uu____1006 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1007 =
                                        let uu____1010 =
                                          let uu____1011 =
                                            let uu____1012 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1012
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1011
                                           in
                                        let uu____1021 =
                                          let uu____1024 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1024]  in
                                        uu____1010 :: uu____1021  in
                                      uu____1006 :: uu____1007  in
                                    let uu____1025 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____999
                                      uu____1025
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1032 =
                                      let uu____1039 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1039]  in
                                    let uu____1040 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1032
                                      uu____1040
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1044 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1044 with
                                  | (t,uu____1050) ->
                                      let expected_k =
                                        let uu____1054 =
                                          let uu____1061 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1062 =
                                            let uu____1065 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1065]  in
                                          uu____1061 :: uu____1062  in
                                        let uu____1066 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1054
                                          uu____1066
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1069 =
                                  let uu____1080 =
                                    let uu____1081 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1081.FStar_Syntax_Syntax.n  in
                                  match uu____1080 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1096 ->
                                      let repr =
                                        let uu____1098 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1098 with
                                        | (t,uu____1104) ->
                                            let expected_k =
                                              let uu____1108 =
                                                let uu____1115 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1116 =
                                                  let uu____1119 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1119]  in
                                                uu____1115 :: uu____1116  in
                                              let uu____1120 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1108 uu____1120
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
                                        let uu____1133 =
                                          let uu____1136 =
                                            let uu____1137 =
                                              let uu____1152 =
                                                let uu____1155 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1156 =
                                                  let uu____1159 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1159]  in
                                                uu____1155 :: uu____1156  in
                                              (repr1, uu____1152)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1137
                                             in
                                          FStar_Syntax_Syntax.mk uu____1136
                                           in
                                        uu____1133
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1174 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1174 wp  in
                                      let destruct_repr t =
                                        let uu____1187 =
                                          let uu____1188 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1188.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1187 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1199,(t1,uu____1201)::
                                             (wp,uu____1203)::[])
                                            -> (t1, wp)
                                        | uu____1246 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1257 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1257
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1258 =
                                          fresh_effect_signature ()  in
                                        match uu____1258 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1274 =
                                                let uu____1281 =
                                                  let uu____1282 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1282
                                                   in
                                                [uu____1281]  in
                                              let uu____1283 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1274 uu____1283
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
                                              let uu____1289 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1289
                                               in
                                            let wp_g_x =
                                              let uu____1293 =
                                                let uu____1294 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1295 =
                                                  let uu____1296 =
                                                    let uu____1297 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1297
                                                     in
                                                  [uu____1296]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1294 uu____1295
                                                 in
                                              uu____1293
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1306 =
                                                  let uu____1307 =
                                                    let uu____1308 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1308
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1317 =
                                                    let uu____1318 =
                                                      let uu____1321 =
                                                        let uu____1324 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1325 =
                                                          let uu____1328 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1329 =
                                                            let uu____1332 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1333 =
                                                              let uu____1336
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1336]
                                                               in
                                                            uu____1332 ::
                                                              uu____1333
                                                             in
                                                          uu____1328 ::
                                                            uu____1329
                                                           in
                                                        uu____1324 ::
                                                          uu____1325
                                                         in
                                                      r :: uu____1321  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1318
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1307 uu____1317
                                                   in
                                                uu____1306
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____1342 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____1342
                                              then
                                                let uu____1345 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____1346 =
                                                  let uu____1349 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____1349]  in
                                                uu____1345 :: uu____1346
                                              else []  in
                                            let expected_k =
                                              let uu____1354 =
                                                let uu____1361 =
                                                  let uu____1364 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____1365 =
                                                    let uu____1368 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____1368]  in
                                                  uu____1364 :: uu____1365
                                                   in
                                                let uu____1369 =
                                                  let uu____1372 =
                                                    let uu____1375 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1376 =
                                                      let uu____1379 =
                                                        let uu____1380 =
                                                          let uu____1381 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1381
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1380
                                                         in
                                                      let uu____1382 =
                                                        let uu____1385 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1386 =
                                                          let uu____1389 =
                                                            let uu____1390 =
                                                              let uu____1391
                                                                =
                                                                let uu____1398
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1398]
                                                                 in
                                                              let uu____1399
                                                                =
                                                                let uu____1402
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1402
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1391
                                                                uu____1399
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1390
                                                             in
                                                          [uu____1389]  in
                                                        uu____1385 ::
                                                          uu____1386
                                                         in
                                                      uu____1379 ::
                                                        uu____1382
                                                       in
                                                    uu____1375 :: uu____1376
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____1372
                                                   in
                                                FStar_List.append uu____1361
                                                  uu____1369
                                                 in
                                              let uu____1403 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1354 uu____1403
                                               in
                                            let uu____1406 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k
                                               in
                                            (match uu____1406 with
                                             | (expected_k1,uu____1414,uu____1415)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env3 =
                                                   let uu___68_1420 = env2
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___68_1420.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1430 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1430
                                           in
                                        let res =
                                          let wp =
                                            let uu____1437 =
                                              let uu____1438 =
                                                let uu____1439 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1439
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1448 =
                                                let uu____1449 =
                                                  let uu____1452 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1453 =
                                                    let uu____1456 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1456]  in
                                                  uu____1452 :: uu____1453
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1449
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1438 uu____1448
                                               in
                                            uu____1437
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1462 =
                                            let uu____1469 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1470 =
                                              let uu____1473 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1473]  in
                                            uu____1469 :: uu____1470  in
                                          let uu____1474 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1462
                                            uu____1474
                                           in
                                        let uu____1477 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k
                                           in
                                        match uu____1477 with
                                        | (expected_k1,uu____1491,uu____1492)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1496 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1496 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1517 ->
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
                                              (let uu____1544 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____1544 with
                                               | (usubst,uvs) ->
                                                   let uu___69_1563 = act  in
                                                   let uu____1564 =
                                                     FStar_Syntax_Subst.subst_binders
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_params
                                                      in
                                                   let uu____1565 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_defn
                                                      in
                                                   let uu____1566 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       =
                                                       (uu___69_1563.FStar_Syntax_Syntax.action_name);
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       =
                                                       (uu___69_1563.FStar_Syntax_Syntax.action_unqualified_name);
                                                     FStar_Syntax_Syntax.action_univs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.action_params
                                                       = uu____1564;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____1565;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____1566
                                                   })
                                             in
                                          let act_typ =
                                            let uu____1570 =
                                              let uu____1571 =
                                                FStar_Syntax_Subst.compress
                                                  act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              uu____1571.FStar_Syntax_Syntax.n
                                               in
                                            match uu____1570 with
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
                                                  let uu____1597 =
                                                    let uu____1600 =
                                                      let uu____1601 =
                                                        let uu____1602 =
                                                          FStar_List.hd
                                                            c1.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        FStar_Pervasives_Native.fst
                                                          uu____1602
                                                         in
                                                      mk_repr'
                                                        c1.FStar_Syntax_Syntax.result_typ
                                                        uu____1601
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total
                                                      uu____1600
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____1597
                                                else
                                                  act1.FStar_Syntax_Syntax.action_typ
                                            | uu____1618 ->
                                                act1.FStar_Syntax_Syntax.action_typ
                                             in
                                          let uu____1619 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1 act_typ
                                             in
                                          match uu____1619 with
                                          | (act_typ1,uu____1627,g_t) ->
                                              let env' =
                                                let uu___70_1630 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ1
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___70_1630.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth_hook
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.synth_hook);
                                                  FStar_TypeChecker_Env.splice
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.splice);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___70_1630.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1632 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1632
                                                then
                                                  let uu____1633 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act1.FStar_Syntax_Syntax.action_defn
                                                     in
                                                  let uu____1634 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ1
                                                     in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act1.FStar_Syntax_Syntax.action_name)
                                                    uu____1633 uu____1634
                                                else ());
                                               (let uu____1636 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act1.FStar_Syntax_Syntax.action_defn
                                                   in
                                                match uu____1636 with
                                                | (act_defn,uu____1644,g_a)
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
                                                    let uu____1648 =
                                                      let act_typ3 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ2
                                                         in
                                                      match act_typ3.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1676 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c
                                                             in
                                                          (match uu____1676
                                                           with
                                                           | (bs1,uu____1686)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let k =
                                                                 let uu____1693
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1693
                                                                  in
                                                               let uu____1696
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k
                                                                  in
                                                               (match uu____1696
                                                                with
                                                                | (k1,uu____1708,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1710 ->
                                                          let uu____1711 =
                                                            let uu____1716 =
                                                              let uu____1717
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ3
                                                                 in
                                                              let uu____1718
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ3
                                                                 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1717
                                                                uu____1718
                                                               in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1716)
                                                             in
                                                          FStar_Errors.raise_error
                                                            uu____1711
                                                            act_defn1.FStar_Syntax_Syntax.pos
                                                       in
                                                    (match uu____1648 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ2
                                                             expected_k
                                                            in
                                                         ((let uu____1727 =
                                                             let uu____1728 =
                                                               let uu____1729
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1729
                                                                in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1728
                                                              in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1727);
                                                          (let act_typ3 =
                                                             let uu____1733 =
                                                               let uu____1734
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1734.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1733
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1757
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1757
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1766
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1766
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1788
                                                                    =
                                                                    let uu____1789
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1789]
                                                                     in
                                                                    let uu____1790
                                                                    =
                                                                    let uu____1799
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1799]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1788;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1790;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1800
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1800))
                                                             | uu____1803 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1806 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1
                                                              in
                                                           match uu____1806
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
                                                               let uu___71_1815
                                                                 = act1  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___71_1815.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___71_1815.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___71_1815.FStar_Syntax_Syntax.action_params);
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
                                match uu____1069 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1839 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1839
                                       in
                                    let uu____1842 =
                                      let uu____1849 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1849 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1870 ->
                                               let uu____1873 =
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
                                               if uu____1873
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1887 =
                                                    let uu____1892 =
                                                      let uu____1893 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1894 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1893 uu____1894
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1892)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1887
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1842 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1908 =
                                             let uu____1913 =
                                               let uu____1914 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1914.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1913)  in
                                           match uu____1908 with
                                           | ([],uu____1917) -> t
                                           | (uu____1928,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1929,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1947 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1960 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1960
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1965 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1967 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1967))
                                                && (m <> n1)
                                               in
                                            if uu____1965
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____1983 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____1990 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____1991 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1983 uu____1990
                                                  uu____1991
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____1999 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____1999 with
                                           | (univs2,defn) ->
                                               let uu____2006 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____2006 with
                                                | (univs',typ) ->
                                                    let uu___72_2016 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___72_2016.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___72_2016.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___72_2016.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___73_2021 = ed2  in
                                           let uu____2022 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____2023 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____2024 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____2025 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____2026 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____2027 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____2028 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____2029 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____2030 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____2031 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____2032 =
                                             let uu____2033 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____2033
                                              in
                                           let uu____2044 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____2045 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____2046 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___73_2021.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___73_2021.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2022;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2023;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2024;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2025;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2026;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2027;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2028;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2029;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2030;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2031;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2032;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2044;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2045;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2046;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___73_2021.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____2050 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____2050
                                           then
                                             let uu____2051 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____2051
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
      let uu____2069 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2069 with
      | (effect_binders_un,signature_un) ->
          let uu____2086 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2086 with
           | (effect_binders,env1,uu____2105) ->
               let uu____2106 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2106 with
                | (signature,uu____2122) ->
                    let raise_error1 a uu____2133 =
                      match uu____2133 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2159  ->
                           match uu____2159 with
                           | (bv,qual) ->
                               let uu____2170 =
                                 let uu___74_2171 = bv  in
                                 let uu____2172 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___74_2171.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___74_2171.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2172
                                 }  in
                               (uu____2170, qual)) effect_binders
                       in
                    let uu____2175 =
                      let uu____2182 =
                        let uu____2183 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2183.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2182 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2193)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2215 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2175 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2233 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2233
                           then
                             let uu____2234 =
                               let uu____2237 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2237  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2234
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2271 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2271 with
                           | (t2,comp,uu____2284) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2291 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2291 with
                          | (repr,_comp) ->
                              ((let uu____2313 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2313
                                then
                                  let uu____2314 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2314
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
                                  let uu____2320 =
                                    let uu____2321 =
                                      let uu____2322 =
                                        let uu____2337 =
                                          let uu____2344 =
                                            let uu____2349 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2350 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2349, uu____2350)  in
                                          [uu____2344]  in
                                        (wp_type1, uu____2337)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2322
                                       in
                                    mk1 uu____2321  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2320
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2375 =
                                      let uu____2380 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2380)  in
                                    let uu____2381 =
                                      let uu____2388 =
                                        let uu____2389 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2389
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2388]  in
                                    uu____2375 :: uu____2381  in
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
                                  let uu____2452 = item  in
                                  match uu____2452 with
                                  | (u_item,item1) ->
                                      let uu____2473 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2473 with
                                       | (item2,item_comp) ->
                                           ((let uu____2489 =
                                               let uu____2490 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2490
                                                in
                                             if uu____2489
                                             then
                                               let uu____2491 =
                                                 let uu____2496 =
                                                   let uu____2497 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2498 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2497 uu____2498
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2496)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2491
                                             else ());
                                            (let uu____2500 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2500 with
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
                                let uu____2520 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2520 with
                                | (dmff_env1,uu____2544,bind_wp,bind_elab) ->
                                    let uu____2547 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2547 with
                                     | (dmff_env2,uu____2571,return_wp,return_elab)
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
                                           let uu____2578 =
                                             let uu____2579 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2579.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2578 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2623 =
                                                       let uu____2638 =
                                                         let uu____2643 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2643
                                                          in
                                                       match uu____2638 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2707 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2623 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2746 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2746
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2763 =
                                                               let uu____2764
                                                                 =
                                                                 let uu____2779
                                                                   =
                                                                   let uu____2786
                                                                    =
                                                                    let uu____2791
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2792
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2791,
                                                                    uu____2792)
                                                                     in
                                                                   [uu____2786]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2779)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2764
                                                                in
                                                             mk1 uu____2763
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2807 =
                                                           let uu____2816 =
                                                             let uu____2817 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2817
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2816
                                                            in
                                                         (match uu____2807
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail1 a415
                                                                =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2836
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2838
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2838
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
                                                                    fail1 ()
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    (
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                    then
                                                                    fail1 ()
                                                                    else ();
                                                                    (
                                                                    let uu____2844
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
                                                                    uu____2844
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
                                                                  let uu____2871
                                                                    =
                                                                    let uu____2872
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2873
                                                                    =
                                                                    let uu____2874
                                                                    =
                                                                    let uu____2881
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2881,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2874]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2872
                                                                    uu____2873
                                                                     in
                                                                  uu____2871
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2906
                                                                  =
                                                                  let uu____2907
                                                                    =
                                                                    let uu____2914
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2914]
                                                                     in
                                                                  b11 ::
                                                                    uu____2907
                                                                   in
                                                                let uu____2919
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2906
                                                                  uu____2919
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2920 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let return_wp1 =
                                           let uu____2922 =
                                             let uu____2923 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2923.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2922 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2967 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2967
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____2980 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let bind_wp1 =
                                           let uu____2982 =
                                             let uu____2983 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____2983.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2982 with
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
                                                     let uu____3010 =
                                                       let uu____3011 =
                                                         let uu____3014 =
                                                           let uu____3015 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____3015
                                                            in
                                                         [uu____3014]  in
                                                       FStar_List.append
                                                         uu____3011 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____3010 body what)
                                              | uu____3016 ->
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
                                             (let uu____3034 =
                                                let uu____3035 =
                                                  let uu____3036 =
                                                    let uu____3051 =
                                                      let uu____3052 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3052
                                                       in
                                                    (t, uu____3051)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3036
                                                   in
                                                mk1 uu____3035  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3034)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3082 = f a2  in
                                               [uu____3082]
                                           | x::xs ->
                                               let uu____3087 =
                                                 apply_last1 f xs  in
                                               x :: uu____3087
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
                                           let uu____3107 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3107 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3137 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3137
                                                 then
                                                   let uu____3138 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3138
                                                 else ());
                                                (let uu____3140 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3140))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3149 =
                                                 let uu____3154 = mk_lid name
                                                    in
                                                 let uu____3155 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3154 uu____3155
                                                  in
                                               (match uu____3149 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3159 =
                                                        let uu____3162 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3162
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3159);
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
                                          (let uu____3259 =
                                             let uu____3262 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3263 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3262 :: uu____3263  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3259);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3361 =
                                               let uu____3364 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3365 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3364 :: uu____3365  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3361);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3460 =
                                                FStar_List.fold_left
                                                  (fun uu____3500  ->
                                                     fun action  ->
                                                       match uu____3500 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3521 =
                                                             let uu____3528 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3528
                                                               params_un
                                                              in
                                                           (match uu____3521
                                                            with
                                                            | (action_params,env',uu____3537)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3557
                                                                     ->
                                                                    match uu____3557
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3568
                                                                    =
                                                                    let uu___75_3569
                                                                    = bv  in
                                                                    let uu____3570
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___75_3569.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___75_3569.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3570
                                                                    }  in
                                                                    (uu____3568,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3574
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3574
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
                                                                    uu____3604
                                                                    ->
                                                                    let uu____3605
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3605
                                                                     in
                                                                    ((
                                                                    let uu____3609
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3609
                                                                    then
                                                                    let uu____3610
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3611
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3612
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3613
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3610
                                                                    uu____3611
                                                                    uu____3612
                                                                    uu____3613
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
                                                                    let uu____3617
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu___76_3621
                                                                    = action
                                                                     in
                                                                    let uu____3622
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3623
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___76_3621.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___76_3621.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___76_3621.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3622;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3623
                                                                    }  in
                                                                    uu____3620
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3617))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3460 with
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
                                                      let uu____3656 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3657 =
                                                        let uu____3660 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3660]  in
                                                      uu____3656 ::
                                                        uu____3657
                                                       in
                                                    let uu____3661 =
                                                      let uu____3662 =
                                                        let uu____3663 =
                                                          let uu____3664 =
                                                            let uu____3679 =
                                                              let uu____3686
                                                                =
                                                                let uu____3691
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3692
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3691,
                                                                  uu____3692)
                                                                 in
                                                              [uu____3686]
                                                               in
                                                            (repr,
                                                              uu____3679)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3664
                                                           in
                                                        mk1 uu____3663  in
                                                      let uu____3707 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3662
                                                        uu____3707
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3661
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3710 =
                                                    let uu____3717 =
                                                      let uu____3718 =
                                                        let uu____3721 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3721
                                                         in
                                                      uu____3718.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3717 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3731)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3760
                                                                =
                                                                let uu____3777
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3777
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3835
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3760
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3885
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    let uu____3889
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3889
                                                                     in
                                                                    uu____3886.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3885
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3914
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3914
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3927
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3952
                                                                     ->
                                                                    match uu____3952
                                                                    with
                                                                    | 
                                                                    (bv,uu____3958)
                                                                    ->
                                                                    let uu____3959
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3960
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3959
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3927
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
                                                                    let uu____4024
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4024
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4029
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4037
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4037
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4042
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4045
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4042,
                                                                    uu____4045)))
                                                                    | 
                                                                    uu____4052
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4053
                                                                    =
                                                                    let uu____4058
                                                                    =
                                                                    let uu____4059
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4059
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4058)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4053)))
                                                       | uu____4060 ->
                                                           Obj.repr
                                                             (let uu____4061
                                                                =
                                                                let uu____4066
                                                                  =
                                                                  let uu____4067
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____4067
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____4066)
                                                                 in
                                                              raise_error1 ()
                                                                uu____4061))
                                                     in
                                                  (match uu____3710 with
                                                   | (pre,post) ->
                                                       ((let uu____4085 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4087 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4089 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___77_4091 =
                                                             ed  in
                                                           let uu____4092 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4093 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____4094 =
                                                             let uu____4095 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4095)
                                                              in
                                                           let uu____4102 =
                                                             let uu____4103 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4103)
                                                              in
                                                           let uu____4110 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____4111 =
                                                             let uu____4112 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4112)
                                                              in
                                                           let uu____4119 =
                                                             let uu____4120 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4120)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4092;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4093;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4094;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4102;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4110;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4111;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4119;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___77_4091.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____4127 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4127
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4145
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4145
                                                               then
                                                                 let uu____4146
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4146
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
                                                                    let uu____4158
                                                                    =
                                                                    let uu____4161
                                                                    =
                                                                    let uu____4170
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4170)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4161
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
                                                                    uu____4158;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4185
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4185
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4187
                                                                 =
                                                                 let uu____4190
                                                                   =
                                                                   let uu____4193
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4193
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4190
                                                                   sigelts'
                                                                  in
                                                               (uu____4187,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4250 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4250 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4283 = FStar_List.hd ses  in
            uu____4283.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4288 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4292,[],t,uu____4294,uu____4295);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4297;
               FStar_Syntax_Syntax.sigattrs = uu____4298;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4300,_t_top,_lex_t_top,_0_40,uu____4303);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4305;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4306;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4308,_t_cons,_lex_t_cons,_0_41,uu____4311);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4313;
                 FStar_Syntax_Syntax.sigattrs = uu____4314;_}::[]
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
                 let uu____4373 =
                   let uu____4376 =
                     let uu____4377 =
                       let uu____4384 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4384, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4377  in
                   FStar_Syntax_Syntax.mk uu____4376  in
                 uu____4373 FStar_Pervasives_Native.None r1  in
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
                   let uu____4402 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4402
                    in
                 let hd1 =
                   let uu____4404 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4404
                    in
                 let tl1 =
                   let uu____4406 =
                     let uu____4407 =
                       let uu____4410 =
                         let uu____4411 =
                           let uu____4418 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4418, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4411  in
                       FStar_Syntax_Syntax.mk uu____4410  in
                     uu____4407 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4406
                    in
                 let res =
                   let uu____4427 =
                     let uu____4430 =
                       let uu____4431 =
                         let uu____4438 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4438,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4431  in
                     FStar_Syntax_Syntax.mk uu____4430  in
                   uu____4427 FStar_Pervasives_Native.None r2  in
                 let uu____4444 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4444
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
               let uu____4483 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4483;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4488 ->
               let err_msg =
                 let uu____4492 =
                   let uu____4493 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4493  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4492
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
            let uu____4518 = FStar_Syntax_Util.type_u ()  in
            match uu____4518 with
            | (k,uu____4524) ->
                let phi1 =
                  let uu____4526 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____4526
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4528 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1  in
                  match uu____4528 with
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
          let uu____4570 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4570 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4603 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas
                   in
                FStar_All.pipe_right uu____4603 FStar_List.flatten  in
              ((let uu____4617 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____4617
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
                          let uu____4628 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4638,uu____4639,uu____4640,uu____4641,uu____4642)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4651 -> failwith "Impossible!"  in
                          match uu____4628 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4662 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4666,uu____4667,uu____4668,uu____4669,uu____4670)
                        -> lid
                    | uu____4679 -> failwith "Impossible"  in
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
                  let uu____4697 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4697
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
                     let uu____4720 =
                       let uu____4723 =
                         let uu____4724 =
                           FStar_TypeChecker_Env.get_range env1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4724;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       uu____4723 :: ses1  in
                     (uu____4720, data_ops_ses))
                   in
                (let uu____4734 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____4739 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____4739 en  in
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4774 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4799 ->
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
           let uu____4851 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4851 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4889 = cps_and_elaborate env1 ne  in
           (match uu____4889 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___78_4926 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___78_4926.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___78_4926.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___78_4926.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___78_4926.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___79_4928 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___79_4928.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___79_4928.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___79_4928.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___79_4928.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___80_4936 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___80_4936.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___80_4936.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___80_4936.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___80_4936.FStar_Syntax_Syntax.sigattrs)
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
           let uu____4944 =
             let uu____4951 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4951
              in
           (match uu____4944 with
            | (a,wp_a_src) ->
                let uu____4966 =
                  let uu____4973 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4973
                   in
                (match uu____4966 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4989 =
                         let uu____4992 =
                           let uu____4993 =
                             let uu____5000 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____5000)  in
                           FStar_Syntax_Syntax.NT uu____4993  in
                         [uu____4992]  in
                       FStar_Syntax_Subst.subst uu____4989 wp_b_tgt  in
                     let expected_k =
                       let uu____5004 =
                         let uu____5011 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____5012 =
                           let uu____5015 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____5015]  in
                         uu____5011 :: uu____5012  in
                       let uu____5016 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____5004 uu____5016  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5037 =
                           let uu____5042 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5042)
                            in
                         let uu____5043 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____5037 uu____5043  in
                       let uu____5046 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____5046 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____5078 =
                             let uu____5079 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____5079  in
                           if uu____5078
                           then no_reify eff_name
                           else
                             (let uu____5085 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____5086 =
                                let uu____5089 =
                                  let uu____5090 =
                                    let uu____5105 =
                                      let uu____5108 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____5109 =
                                        let uu____5112 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____5112]  in
                                      uu____5108 :: uu____5109  in
                                    (repr, uu____5105)  in
                                  FStar_Syntax_Syntax.Tm_app uu____5090  in
                                FStar_Syntax_Syntax.mk uu____5089  in
                              uu____5086 FStar_Pervasives_Native.None
                                uu____5085)
                        in
                     let uu____5118 =
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
                               let uu____5171 =
                                 let uu____5174 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 FStar_Pervasives_Native.fst uu____5174  in
                               FStar_Syntax_Subst.subst uu____5171 lift_wp
                             else lift_wp  in
                           let uu____5188 =
                             check_and_gen env1 lift_wp1 expected_k  in
                           (lift, uu____5188)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let lift1 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5214 =
                                 let uu____5217 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 FStar_Pervasives_Native.fst uu____5217  in
                               FStar_Syntax_Subst.subst uu____5214 lift
                             else lift  in
                           ((let uu____5232 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5232
                             then
                               let uu____5233 =
                                 FStar_Syntax_Print.term_to_string lift1  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5233
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5236 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift1
                                in
                             match uu____5236 with
                             | (lift2,comp,uu____5251) ->
                                 let uu____5252 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift2
                                    in
                                 (match uu____5252 with
                                  | (uu____5265,lift_wp,lift_elab) ->
                                      let uu____5268 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5269 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____5118 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___81_5310 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___81_5310.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___81_5310.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___81_5310.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___81_5310.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___81_5310.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___81_5310.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___81_5310.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___81_5310.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___81_5310.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___81_5310.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___81_5310.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___81_5310.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___81_5310.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___81_5310.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___81_5310.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___81_5310.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___81_5310.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___81_5310.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___81_5310.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___81_5310.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___81_5310.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___81_5310.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___81_5310.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___81_5310.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___81_5310.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___81_5310.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___81_5310.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___81_5310.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___81_5310.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___81_5310.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___81_5310.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___81_5310.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___81_5310.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___81_5310.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___81_5310.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let lift2 =
                                  let uu____5329 =
                                    let uu____5332 =
                                      FStar_Syntax_Subst.univ_var_opening uvs
                                       in
                                    FStar_Pervasives_Native.fst uu____5332
                                     in
                                  FStar_Syntax_Subst.subst uu____5329 lift1
                                   in
                                let uu____5345 =
                                  let uu____5352 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5352
                                   in
                                (match uu____5345 with
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
                                         let uu____5376 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5377 =
                                           let uu____5380 =
                                             let uu____5381 =
                                               let uu____5396 =
                                                 let uu____5399 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5400 =
                                                   let uu____5403 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5403]  in
                                                 uu____5399 :: uu____5400  in
                                               (lift_wp1, uu____5396)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5381
                                              in
                                           FStar_Syntax_Syntax.mk uu____5380
                                            in
                                         uu____5377
                                           FStar_Pervasives_Native.None
                                           uu____5376
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5412 =
                                         let uu____5419 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5420 =
                                           let uu____5423 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5424 =
                                             let uu____5427 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5427]  in
                                           uu____5423 :: uu____5424  in
                                         uu____5419 :: uu____5420  in
                                       let uu____5428 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5412
                                         uu____5428
                                        in
                                     let uu____5431 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5431 with
                                      | (expected_k2,uu____5441,uu____5442)
                                          ->
                                          let lift3 =
                                            check_and_gen env2 lift2
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift3))
                             in
                          let sub2 =
                            let uu___82_5445 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___82_5445.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___82_5445.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___83_5447 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___83_5447.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___83_5447.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___83_5447.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___83_5447.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let uu____5462 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (uvs, tps, c)
             else
               (let uu____5476 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____5476 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____5503 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____5503 c  in
                    (uvs1, tps1, c1))
              in
           (match uu____5462 with
            | (uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____5524 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____5524 with
                 | (tps2,c2) ->
                     let uu____5539 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____5539 with
                      | (tps3,env3,us) ->
                          let uu____5557 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____5557 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____5578 =
                                   let uu____5579 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____5579
                                    in
                                 match uu____5578 with
                                 | (uvs2,t) ->
                                     let uu____5594 =
                                       let uu____5607 =
                                         let uu____5612 =
                                           let uu____5613 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____5613.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____5612)  in
                                       match uu____5607 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____5628,c5)) -> ([], c5)
                                       | (uu____5668,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____5695 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____5594 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____5739 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____5739 with
                                              | (uu____5744,t1) ->
                                                  let uu____5746 =
                                                    let uu____5751 =
                                                      let uu____5752 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____5753 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____5754 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____5752 uu____5753
                                                        uu____5754
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____5751)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5746 r)
                                           else ();
                                           (let se1 =
                                              let uu___84_5757 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___84_5757.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___84_5757.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___84_5757.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___84_5757.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5774,uu____5775,uu____5776) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___58_5780  ->
                   match uu___58_5780 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5781 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5786,uu____5787) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___58_5795  ->
                   match uu___58_5795 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5796 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5806 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5806
             then
               let uu____5807 =
                 let uu____5812 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid)
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5812)
                  in
               FStar_Errors.raise_error uu____5807 r
             else ());
            (let uu____5814 =
               if uvs = []
               then
                 let uu____5815 =
                   let uu____5816 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____5816  in
                 check_and_gen env2 t uu____5815
               else
                 (let uu____5822 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____5822 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5830 =
                          let uu____5831 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____5831  in
                        tc_check_trivial_guard env2 t1 uu____5830  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____5837 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____5837))
                in
             match uu____5814 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___85_5853 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___85_5853.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___85_5853.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___85_5853.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___85_5853.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5863 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____5863 with
            | (uu____5876,phi1) ->
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
           let uu____5886 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____5886 with
            | (e1,c,g1) ->
                let uu____5904 =
                  let uu____5911 =
                    let uu____5914 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____5914  in
                  let uu____5915 =
                    let uu____5920 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____5920)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5911 uu____5915
                   in
                (match uu____5904 with
                 | (e2,uu____5930,g) ->
                     ((let uu____5933 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5933);
                      (let se1 =
                         let uu___86_5935 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___86_5935.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___86_5935.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___86_5935.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___86_5935.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_splice t ->
           ((let uu____5942 = FStar_Options.debug_any ()  in
             if uu____5942
             then
               let uu____5943 =
                 FStar_Ident.string_of_lid
                   env1.FStar_TypeChecker_Env.curmodule
                  in
               let uu____5944 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____5943
                 uu____5944
             else ());
            (let ses = env1.FStar_TypeChecker_Env.splice env1 t  in ([], ses)))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5999 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____5999
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____6007 =
                      let uu____6012 =
                        let uu____6013 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____6014 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____6015 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____6013 uu____6014 uu____6015
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____6012)
                       in
                    FStar_Errors.raise_error uu____6007 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____6041 =
                   let uu____6042 = FStar_Syntax_Subst.compress def  in
                   uu____6042.FStar_Syntax_Syntax.n  in
                 match uu____6041 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6052,uu____6053)
                     -> binders
                 | uu____6074 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6084;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6162) -> val_bs1
                     | (uu____6185,[]) -> val_bs1
                     | ((body_bv,uu____6209)::bt,(val_bv,aqual)::vt) ->
                         let uu____6246 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6262) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___87_6264 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___88_6267 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___88_6267.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___87_6264.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___87_6264.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6246
                      in
                   let uu____6268 =
                     let uu____6271 =
                       let uu____6272 =
                         let uu____6285 = rename_binders1 def_bs val_bs  in
                         (uu____6285, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6272  in
                     FStar_Syntax_Syntax.mk uu____6271  in
                   uu____6268 FStar_Pervasives_Native.None r1
               | uu____6303 -> typ1  in
             let uu___89_6304 = lb  in
             let uu____6305 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___89_6304.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___89_6304.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6305;
               FStar_Syntax_Syntax.lbeff =
                 (uu___89_6304.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___89_6304.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___89_6304.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___89_6304.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____6308 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6359  ->
                     fun lb  ->
                       match uu____6359 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6401 =
                             let uu____6412 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6412 with
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
                                   | uu____6497 ->
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
                                  (let uu____6540 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def,
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____6540, quals_opt1)))
                              in
                           (match uu____6401 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6308 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6634 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___59_6638  ->
                                match uu___59_6638 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6639 -> false))
                         in
                      if uu____6634
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6649 =
                    let uu____6652 =
                      let uu____6653 =
                        let uu____6666 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6666)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6653  in
                    FStar_Syntax_Syntax.mk uu____6652  in
                  uu____6649 FStar_Pervasives_Native.None r  in
                let uu____6684 =
                  let uu____6695 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___90_6704 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___90_6704.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___90_6704.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___90_6704.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___90_6704.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___90_6704.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___90_6704.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___90_6704.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___90_6704.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___90_6704.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___90_6704.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___90_6704.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___90_6704.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___90_6704.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___90_6704.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___90_6704.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___90_6704.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___90_6704.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___90_6704.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___90_6704.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___90_6704.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___90_6704.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___90_6704.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___90_6704.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___90_6704.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___90_6704.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___90_6704.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___90_6704.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___90_6704.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___90_6704.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___90_6704.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___90_6704.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___90_6704.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___90_6704.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___90_6704.FStar_TypeChecker_Env.dep_graph)
                       }) e
                     in
                  match uu____6695 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6717;
                       FStar_Syntax_Syntax.vars = uu____6718;_},uu____6719,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6748 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6748)  in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6766,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6771 -> quals  in
                      ((let uu___91_6779 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___91_6779.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___91_6779.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___91_6779.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6788 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6684 with
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
                      (let uu____6837 = log env2  in
                       if uu____6837
                       then
                         let uu____6838 =
                           let uu____6839 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6854 =
                                         let uu____6863 =
                                           let uu____6864 =
                                             let uu____6867 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____6867.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____6864.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6863
                                          in
                                       match uu____6854 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6874 -> false  in
                                     if should_log
                                     then
                                       let uu____6883 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____6884 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6883 uu____6884
                                     else ""))
                              in
                           FStar_All.pipe_right uu____6839
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____6838
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
             (fun uu___60_6930  ->
                match uu___60_6930 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____6931 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____6937) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____6943 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____6952 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____6957 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____6966 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____6991 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7015) ->
          let uu____7024 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7024
          then
            let for_export_bundle se1 uu____7055 =
              match uu____7055 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7094,uu____7095) ->
                       let dec =
                         let uu___92_7105 = se1  in
                         let uu____7106 =
                           let uu____7107 =
                             let uu____7114 =
                               let uu____7117 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7117  in
                             (l, us, uu____7114)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7107  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7106;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_7105.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_7105.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_7105.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7129,uu____7130,uu____7131) ->
                       let dec =
                         let uu___93_7137 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___93_7137.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___93_7137.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___93_7137.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7142 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7164,uu____7165,uu____7166) ->
          let uu____7167 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7167 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7188 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7188
          then
            ([(let uu___94_7204 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___94_7204.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___94_7204.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___94_7204.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7206 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___61_7210  ->
                       match uu___61_7210 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7211 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7216 -> true
                       | uu____7217 -> false))
                in
             if uu____7206 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7235 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7240 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7245 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7250 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7255 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7273) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7290 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7290
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
          let uu____7321 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7321
          then
            let uu____7330 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___95_7343 = se  in
                      let uu____7344 =
                        let uu____7345 =
                          let uu____7352 =
                            let uu____7353 =
                              let uu____7356 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7356.FStar_Syntax_Syntax.fv_name  in
                            uu____7353.FStar_Syntax_Syntax.v  in
                          (uu____7352, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7345  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7344;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___95_7343.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___95_7343.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___95_7343.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7330, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7376 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7393 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7408) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____7411 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7412 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7422 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7422) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7423,uu____7424,uu____7425) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7429  ->
                  match uu___62_7429 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7430 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7431,uu____7432) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7440  ->
                  match uu___62_7440 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7441 -> false))
          -> env
      | uu____7442 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7502 se =
        match uu____7502 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7555 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7555
              then
                let uu____7556 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7556
              else ());
             (let uu____7558 = tc_decl env1 se  in
              match uu____7558 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7608 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____7608
                             then
                               let uu____7609 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7609
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
                    (let uu____7632 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____7632
                     then
                       let uu____7633 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7639 =
                                  let uu____7640 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____7640 "\n"  in
                                Prims.strcat s uu____7639) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____7633
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7645 =
                       let uu____7654 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____7654
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____7689 se1 =
                            match uu____7689 with
                            | (exports1,hidden1) ->
                                let uu____7717 = for_export hidden1 se1  in
                                (match uu____7717 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____7645 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___96_7796 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___96_7796.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___96_7796.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___96_7796.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___96_7796.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____7874 = acc  in
        match uu____7874 with
        | (uu____7909,uu____7910,env1,uu____7912) ->
            let uu____7925 =
              FStar_Util.record_time
                (fun uu____7971  -> process_one_decl acc se)
               in
            (match uu____7925 with
             | (r,ms_elapsed) ->
                 ((let uu____8035 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8035
                   then
                     let uu____8036 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8037 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8036 uu____8037
                   else ());
                  r))
         in
      let uu____8039 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8039 with
      | (ses1,exports,env1,uu____8087) ->
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
          let uu___97_8118 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___97_8118.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___97_8118.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___97_8118.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___97_8118.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___97_8118.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___97_8118.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___97_8118.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___97_8118.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___97_8118.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___97_8118.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___97_8118.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___97_8118.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___97_8118.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___97_8118.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___97_8118.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___97_8118.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___97_8118.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___97_8118.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___97_8118.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___97_8118.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___97_8118.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___97_8118.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___97_8118.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___97_8118.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___97_8118.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___97_8118.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___97_8118.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___97_8118.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___97_8118.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___97_8118.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___97_8118.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___97_8118.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___97_8118.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8129 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8129 with
          | (univs2,t1) ->
              ((let uu____8137 =
                  let uu____8138 =
                    let uu____8141 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8141  in
                  FStar_All.pipe_left uu____8138
                    (FStar_Options.Other "Exports")
                   in
                if uu____8137
                then
                  let uu____8142 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8143 =
                    let uu____8144 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8144
                      (FStar_String.concat ", ")
                     in
                  let uu____8153 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8142 uu____8143 uu____8153
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____8156 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____8156 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____8180 =
             let uu____8181 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8182 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8181 uu____8182
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8180);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8189) ->
              let uu____8198 =
                let uu____8199 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8199  in
              if uu____8198
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8209,uu____8210) ->
              let t =
                let uu____8222 =
                  let uu____8225 =
                    let uu____8226 =
                      let uu____8239 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8239)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8226  in
                  FStar_Syntax_Syntax.mk uu____8225  in
                uu____8222 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8246,uu____8247,uu____8248) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8256 =
                let uu____8257 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8257  in
              if uu____8256 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8261,lbs),uu____8263) ->
              let uu____8278 =
                let uu____8279 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8279  in
              if uu____8278
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
              let uu____8298 =
                let uu____8299 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8299  in
              if uu____8298
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8306 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8307 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8314 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8315 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8316 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____8317 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8318 -> ()  in
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
             | FStar_Syntax_Syntax.Projector (l,uu____8395) -> true
             | uu____8396 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8415 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____8446 ->
                   let uu____8447 =
                     let uu____8450 =
                       let uu____8451 =
                         let uu____8464 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____8464)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____8451  in
                     FStar_Syntax_Syntax.mk uu____8450  in
                   uu____8447 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____8472,uu____8473) ->
            let s1 =
              let uu___98_8483 = s  in
              let uu____8484 =
                let uu____8485 =
                  let uu____8492 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____8492)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____8485  in
              let uu____8493 =
                let uu____8496 =
                  let uu____8499 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____8499  in
                FStar_Syntax_Syntax.Assumption :: uu____8496  in
              {
                FStar_Syntax_Syntax.sigel = uu____8484;
                FStar_Syntax_Syntax.sigrng =
                  (uu___98_8483.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____8493;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___98_8483.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___98_8483.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____8502 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____8516 =
        match uu____8516 with
        | (uvs,t) ->
            let uu___99_8523 = s  in
            let uu____8524 =
              let uu____8527 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____8527  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___99_8523.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____8524;
              FStar_Syntax_Syntax.sigmeta =
                (uu___99_8523.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___99_8523.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____8539 -> failwith "Impossible!"  in
        let c_opt =
          let uu____8543 = FStar_Syntax_Util.is_unit t  in
          if uu____8543
          then
            let uu____8546 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____8546
          else
            (let uu____8548 =
               let uu____8549 = FStar_Syntax_Subst.compress t  in
               uu____8549.FStar_Syntax_Syntax.n  in
             match uu____8548 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____8554,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____8574 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____8583 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____8583
           then
             let uu____8584 =
               let uu____8585 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____8585 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____8584
           else
             (let uu____8593 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect env uu____8593))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____8602 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____8621 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_splice uu____8638 ->
            failwith "Impossible! Trying to extract splice"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____8672,uu____8673,uu____8674,uu____8675,uu____8676)
                         ->
                         ((let uu____8686 =
                             let uu____8689 =
                               FStar_ST.op_Bang abstract_inductive_tycons  in
                             lid :: uu____8689  in
                           FStar_ST.op_Colon_Equals abstract_inductive_tycons
                             uu____8686);
                          (let uu____8782 = vals_of_abstract_inductive s1  in
                           FStar_List.append uu____8782 sigelts1))
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____8786,uu____8787,uu____8788,uu____8789,uu____8790)
                         ->
                         ((let uu____8796 =
                             let uu____8799 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____8799  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____8796);
                          sigelts1)
                     | uu____8892 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____8899 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____8899
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____8905 =
                   let uu___100_8906 = s  in
                   let uu____8907 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___100_8906.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___100_8906.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____8907;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___100_8906.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___100_8906.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____8905])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____8917 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____8917
            then []
            else
              (let uu____8921 = lbs  in
               match uu____8921 with
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
                       (fun uu____8977  ->
                          match uu____8977 with
                          | (uu____8984,t) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____9002  ->
                            match uu____9002 with
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
                          (fun uu____9022  ->
                             match uu____9022 with
                             | (uu____9029,t) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____9042,uu____9043) ->
            let is_haseq = FStar_TypeChecker_Util.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____9048 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____9099 =
                       FStar_TypeChecker_Util.get_haseq_axiom_lid l  in
                     FStar_Ident.lid_equals lid uu____9099) uu____9048
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____9102 =
                   let uu___101_9103 = s  in
                   let uu____9104 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___101_9103.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___101_9103.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9104;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___101_9103.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___101_9103.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9102]
               else [])
            else
              (let uu____9109 =
                 let uu___102_9110 = s  in
                 let uu____9111 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___102_9110.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___102_9110.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____9111;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___102_9110.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___102_9110.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____9109])
        | FStar_Syntax_Syntax.Sig_new_effect uu____9114 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9115 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____9116 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9117 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____9130 -> [s]  in
      let uu___103_9131 = m  in
      let uu____9132 =
        let uu____9133 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____9133  in
      {
        FStar_Syntax_Syntax.name = (uu___103_9131.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9132;
        FStar_Syntax_Syntax.exports =
          (uu___103_9131.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      (let uu____9147 = FStar_Syntax_DsEnv.pop ()  in
       FStar_All.pipe_right uu____9147 FStar_Pervasives.ignore);
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
      let uu___104_9158 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___104_9158.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___104_9158.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___104_9158.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___104_9158.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___104_9158.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___104_9158.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___104_9158.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___104_9158.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___104_9158.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___104_9158.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___104_9158.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___104_9158.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___104_9158.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___104_9158.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___104_9158.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___104_9158.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___104_9158.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___104_9158.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___104_9158.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___104_9158.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___104_9158.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___104_9158.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___104_9158.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___104_9158.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___104_9158.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___104_9158.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___104_9158.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___104_9158.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___104_9158.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___104_9158.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___104_9158.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___104_9158.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___104_9158.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___104_9158.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv1;
        FStar_TypeChecker_Env.dep_graph =
          (uu___104_9158.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____9179 = FStar_Options.debug_any ()  in
       if uu____9179
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
         let uu___105_9184 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___105_9184.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___105_9184.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___105_9184.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___105_9184.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___105_9184.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___105_9184.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___105_9184.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___105_9184.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___105_9184.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___105_9184.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___105_9184.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___105_9184.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___105_9184.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___105_9184.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___105_9184.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___105_9184.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___105_9184.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___105_9184.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___105_9184.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___105_9184.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___105_9184.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___105_9184.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___105_9184.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___105_9184.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___105_9184.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___105_9184.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___105_9184.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___105_9184.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___105_9184.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___105_9184.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___105_9184.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___105_9184.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___105_9184.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___105_9184.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____9186 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____9186 with
       | (ses,exports,env3) ->
           ((let uu___106_9219 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___106_9219.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___106_9219.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___106_9219.FStar_Syntax_Syntax.is_interface)
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
        let uu____9241 = tc_decls env decls  in
        match uu____9241 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___107_9272 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___107_9272.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___107_9272.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___107_9272.FStar_Syntax_Syntax.is_interface)
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
        if
          FStar_Ident.lid_equals env0.FStar_TypeChecker_Env.curmodule
            FStar_Parser_Const.prims_lid
        then
          let uu___108_9317 = env0  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___108_9317.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___108_9317.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___108_9317.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___108_9317.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___108_9317.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___108_9317.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___108_9317.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___108_9317.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___108_9317.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___108_9317.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___108_9317.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___108_9317.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___108_9317.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___108_9317.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___108_9317.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___108_9317.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___108_9317.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___108_9317.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes =
              (uu___108_9317.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___108_9317.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___108_9317.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___108_9317.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___108_9317.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___108_9317.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___108_9317.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___108_9317.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___108_9317.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___108_9317.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___108_9317.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___108_9317.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___108_9317.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___108_9317.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___108_9317.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___108_9317.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___108_9317.FStar_TypeChecker_Env.dep_graph)
          }
        else env0  in
      let msg =
        Prims.strcat "Internals for "
          (m.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let env02 = push_context env01 msg  in
      let uu____9321 = tc_partial_modul env02 m  in
      match uu____9321 with
      | (modul,non_private_decls,env) ->
          let uu____9345 =
            finish_partial_modul false env modul non_private_decls  in
          (match uu____9345 with
           | (m1,m_opt,env1) ->
               (m1, m_opt,
                 (let uu___109_9372 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___109_9372.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___109_9372.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___109_9372.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___109_9372.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___109_9372.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___109_9372.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___109_9372.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___109_9372.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___109_9372.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___109_9372.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___109_9372.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___109_9372.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___109_9372.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___109_9372.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___109_9372.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___109_9372.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___109_9372.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___109_9372.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = lax_mode;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___109_9372.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___109_9372.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___109_9372.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___109_9372.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___109_9372.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___109_9372.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___109_9372.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___109_9372.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___109_9372.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___109_9372.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___109_9372.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___109_9372.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___109_9372.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___109_9372.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___109_9372.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___109_9372.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___109_9372.FStar_TypeChecker_Env.dep_graph)
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
          let uu____9387 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
             in
          if uu____9387
          then
            let en0 =
              pop_context en
                (Prims.strcat "Ending modul "
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
               in
            let en01 =
              let uu___110_9398 = en0  in
              let uu____9399 =
                let uu____9412 =
                  FStar_All.pipe_right
                    en.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                (uu____9412, FStar_Pervasives_Native.None)  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___110_9398.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___110_9398.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___110_9398.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___110_9398.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___110_9398.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___110_9398.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___110_9398.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___110_9398.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___110_9398.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___110_9398.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___110_9398.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___110_9398.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___110_9398.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___110_9398.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___110_9398.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___110_9398.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___110_9398.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___110_9398.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___110_9398.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___110_9398.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___110_9398.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___110_9398.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___110_9398.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___110_9398.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___110_9398.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___110_9398.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___110_9398.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index = uu____9399;
                FStar_TypeChecker_Env.proof_ns =
                  (uu___110_9398.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___110_9398.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___110_9398.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___110_9398.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___110_9398.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___110_9398.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___110_9398.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___110_9398.FStar_TypeChecker_Env.dep_graph)
              }  in
            let en02 =
              let uu____9450 =
                let uu____9451 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9451  in
              if uu____9450
              then
                ((let uu____9453 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____9453 FStar_Pervasives.ignore);
                 z3_reset_options en01)
              else en01  in
            let modul_iface = extract_interface en m  in
            ((let uu____9457 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                  FStar_Options.Low
                 in
              if uu____9457
              then
                let uu____9458 =
                  let uu____9459 =
                    FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9459 then "" else " (in lax mode) "  in
                let uu____9461 =
                  let uu____9462 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9462
                  then
                    let uu____9463 =
                      let uu____9464 = FStar_Syntax_Print.modul_to_string m
                         in
                      Prims.strcat uu____9464 "\n"  in
                    Prims.strcat "\nfrom: " uu____9463
                  else ""  in
                let uu____9466 =
                  let uu____9467 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9467
                  then
                    let uu____9468 =
                      let uu____9469 =
                        FStar_Syntax_Print.modul_to_string modul_iface  in
                      Prims.strcat uu____9469 "\n"  in
                    Prims.strcat "\nto: " uu____9468
                  else ""  in
                FStar_Util.print4
                  "Extracting and type checking module %s interface%s%s%s\n"
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____9458
                  uu____9461 uu____9466
              else ());
             (let env0 =
                let uu___111_9473 = en02  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___111_9473.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___111_9473.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___111_9473.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___111_9473.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___111_9473.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___111_9473.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___111_9473.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___111_9473.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___111_9473.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___111_9473.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___111_9473.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___111_9473.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___111_9473.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___111_9473.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___111_9473.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___111_9473.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface = true;
                  FStar_TypeChecker_Env.admit =
                    (uu___111_9473.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___111_9473.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___111_9473.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___111_9473.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___111_9473.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___111_9473.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___111_9473.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___111_9473.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___111_9473.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___111_9473.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___111_9473.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___111_9473.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___111_9473.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___111_9473.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___111_9473.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___111_9473.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___111_9473.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___111_9473.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___111_9473.FStar_TypeChecker_Env.dep_graph)
                }  in
              let uu____9474 = tc_modul en02 modul_iface  in
              match uu____9474 with
              | (modul_iface1,must_be_none,env) ->
                  if must_be_none <> FStar_Pervasives_Native.None
                  then
                    failwith
                      "Impossible! Expected the second component to be None"
                  else
                    (((let uu___112_9520 = m  in
                       {
                         FStar_Syntax_Syntax.name =
                           (uu___112_9520.FStar_Syntax_Syntax.name);
                         FStar_Syntax_Syntax.declarations =
                           (uu___112_9520.FStar_Syntax_Syntax.declarations);
                         FStar_Syntax_Syntax.exports =
                           (modul_iface1.FStar_Syntax_Syntax.exports);
                         FStar_Syntax_Syntax.is_interface =
                           (uu___112_9520.FStar_Syntax_Syntax.is_interface)
                       })), (FStar_Pervasives_Native.Some modul_iface1), env)))
          else
            (let modul =
               let uu____9523 = FStar_Options.use_extracted_interfaces ()  in
               if uu____9523
               then
                 let uu___113_9524 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___113_9524.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___113_9524.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___113_9524.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___114_9526 = m  in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___114_9526.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___114_9526.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___114_9526.FStar_Syntax_Syntax.is_interface)
                  })
                in
             let env = FStar_TypeChecker_Env.finish_module en modul  in
             (let uu____9529 =
                FStar_All.pipe_right
                  env.FStar_TypeChecker_Env.qtbl_name_and_index
                  FStar_Pervasives_Native.fst
                 in
              FStar_All.pipe_right uu____9529 FStar_Util.smap_clear);
             (let uu____9557 =
                ((let uu____9560 = FStar_Options.lax ()  in
                  Prims.op_Negation uu____9560) &&
                   (let uu____9562 =
                      FStar_Options.use_extracted_interfaces ()  in
                    Prims.op_Negation uu____9562))
                  && (Prims.op_Negation loading_from_cache)
                 in
              if uu____9557 then check_exports env modul exports else ());
             (let uu____9565 =
                pop_context env
                  (Prims.strcat "Ending modul "
                     (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 in
              FStar_All.pipe_right uu____9565 FStar_Pervasives.ignore);
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
               env modul;
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ();
             (let uu____9569 =
                let uu____9570 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9570  in
              if uu____9569
              then
                let uu____9571 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____9571 FStar_Pervasives.ignore
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
        let uu____9583 =
          let uu____9584 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____9584  in
        push_context env uu____9583  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____9603 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____9624 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports  in
      match uu____9624 with | (uu____9633,uu____9634,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      (let uu____9655 = FStar_Options.debug_any ()  in
       if uu____9655
       then
         let uu____9656 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____9656
       else ());
      (let env1 =
         let uu___115_9660 = env  in
         let uu____9661 =
           let uu____9662 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____9662  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___115_9660.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___115_9660.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___115_9660.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___115_9660.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___115_9660.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___115_9660.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___115_9660.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___115_9660.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___115_9660.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___115_9660.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___115_9660.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___115_9660.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___115_9660.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___115_9660.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___115_9660.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___115_9660.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___115_9660.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___115_9660.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____9661;
           FStar_TypeChecker_Env.lax_universes =
             (uu___115_9660.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___115_9660.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___115_9660.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___115_9660.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___115_9660.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___115_9660.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___115_9660.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___115_9660.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___115_9660.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___115_9660.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___115_9660.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___115_9660.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___115_9660.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___115_9660.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___115_9660.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___115_9660.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___115_9660.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____9663 = tc_modul env1 m  in
       match uu____9663 with
       | (m1,m_iface_opt,env2) ->
           ((let uu____9688 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____9688
             then
               let uu____9689 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____9689
             else ());
            (let uu____9692 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____9692
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
                       let uu____9723 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____9723 with
                       | (univnames1,e) ->
                           let uu___116_9730 = lb  in
                           let uu____9731 =
                             let uu____9734 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____9734 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___116_9730.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___116_9730.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___116_9730.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___116_9730.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____9731;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___116_9730.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___116_9730.FStar_Syntax_Syntax.lbpos)
                           }
                        in
                     let uu___117_9735 = se  in
                     let uu____9736 =
                       let uu____9737 =
                         let uu____9744 =
                           let uu____9751 = FStar_List.map update lbs  in
                           (b, uu____9751)  in
                         (uu____9744, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____9737  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____9736;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___117_9735.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___117_9735.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___117_9735.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___117_9735.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____9764 -> se  in
               let normalized_module =
                 let uu___118_9766 = m1  in
                 let uu____9767 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___118_9766.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____9767;
                   FStar_Syntax_Syntax.exports =
                     (uu___118_9766.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___118_9766.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____9768 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____9768
             else ());
            (m1, m_iface_opt, env2)))
  