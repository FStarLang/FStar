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
  FStar_TypeChecker_Env.env ->
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
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____385 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____385 with
                | (effect_params,env1,uu____394) ->
                    let uu____395 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____395 with
                     | (signature,uu____401) ->
                         let ed1 =
                           let uu___65_403 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___65_403.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___65_403.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___65_403.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___65_403.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___65_403.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___65_403.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___65_403.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___65_403.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___65_403.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___65_403.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___65_403.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___65_403.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___65_403.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___65_403.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___65_403.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___65_403.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___65_403.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___65_403.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____419 ->
                               let op uu____441 =
                                 match uu____441 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____461 =
                                       let uu____462 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____471 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____462
                                         uu____471
                                        in
                                     (us, uu____461)
                                  in
                               let uu___66_480 = ed1  in
                               let uu____481 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____482 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____483 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____484 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____485 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____486 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____487 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____488 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____489 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____490 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____491 =
                                 let uu____492 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____492  in
                               let uu____503 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____504 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____505 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___67_513 = a  in
                                      let uu____514 =
                                        let uu____515 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____515
                                         in
                                      let uu____524 =
                                        let uu____525 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____525
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___67_513.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___67_513.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___67_513.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___67_513.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____514;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____524
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___66_480.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___66_480.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___66_480.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___66_480.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____481;
                                 FStar_Syntax_Syntax.bind_wp = uu____482;
                                 FStar_Syntax_Syntax.if_then_else = uu____483;
                                 FStar_Syntax_Syntax.ite_wp = uu____484;
                                 FStar_Syntax_Syntax.stronger = uu____485;
                                 FStar_Syntax_Syntax.close_wp = uu____486;
                                 FStar_Syntax_Syntax.assert_p = uu____487;
                                 FStar_Syntax_Syntax.assume_p = uu____488;
                                 FStar_Syntax_Syntax.null_wp = uu____489;
                                 FStar_Syntax_Syntax.trivial = uu____490;
                                 FStar_Syntax_Syntax.repr = uu____491;
                                 FStar_Syntax_Syntax.return_repr = uu____503;
                                 FStar_Syntax_Syntax.bind_repr = uu____504;
                                 FStar_Syntax_Syntax.actions = uu____505;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___66_480.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____560 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____565 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____560 uu____565  in
                           let uu____572 =
                             let uu____573 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____573.FStar_Syntax_Syntax.n  in
                           match uu____572 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____608)::(wp,uu____610)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____625 -> fail1 signature1)
                           | uu____626 -> fail1 signature1  in
                         let uu____627 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____627 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____649 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____656 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____656 with
                                     | (signature1,uu____668) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____669 ->
                                    let uu____672 =
                                      let uu____677 =
                                        let uu____678 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____678)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____677
                                       in
                                    (match uu____672 with
                                     | (uu____687,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____690 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____690
                                 in
                              ((let uu____692 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____692
                                then
                                  let uu____693 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____694 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____695 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____696 =
                                    let uu____697 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____697
                                     in
                                  let uu____698 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____693 uu____694 uu____695 uu____696
                                    uu____698
                                else ());
                               (let check_and_gen' env3 uu____714 k =
                                  match uu____714 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____728::uu____729 ->
                                           let uu____732 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____732 with
                                            | (us1,t1) ->
                                                let uu____741 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____741 with
                                                 | (us2,t2) ->
                                                     let uu____748 =
                                                       let uu____749 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____749 t2 k
                                                        in
                                                     let uu____750 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____750))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____755 =
                                      let uu____762 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____763 =
                                        let uu____766 =
                                          let uu____767 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____767
                                           in
                                        [uu____766]  in
                                      uu____762 :: uu____763  in
                                    let uu____768 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____755
                                      uu____768
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____772 = fresh_effect_signature ()
                                     in
                                  match uu____772 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____788 =
                                          let uu____795 =
                                            let uu____796 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____796
                                             in
                                          [uu____795]  in
                                        let uu____797 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____788
                                          uu____797
                                         in
                                      let expected_k =
                                        let uu____803 =
                                          let uu____810 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____811 =
                                            let uu____814 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____815 =
                                              let uu____818 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____819 =
                                                let uu____822 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____823 =
                                                  let uu____826 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____826]  in
                                                uu____822 :: uu____823  in
                                              uu____818 :: uu____819  in
                                            uu____814 :: uu____815  in
                                          uu____810 :: uu____811  in
                                        let uu____827 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____803
                                          uu____827
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____832 =
                                      let uu____835 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____835
                                       in
                                    let uu____836 =
                                      let uu____837 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____837
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____832
                                      uu____836
                                     in
                                  let expected_k =
                                    let uu____849 =
                                      let uu____856 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____857 =
                                        let uu____860 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____861 =
                                          let uu____864 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____865 =
                                            let uu____868 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____868]  in
                                          uu____864 :: uu____865  in
                                        uu____860 :: uu____861  in
                                      uu____856 :: uu____857  in
                                    let uu____869 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____849
                                      uu____869
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____876 =
                                      let uu____883 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____884 =
                                        let uu____887 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____887]  in
                                      uu____883 :: uu____884  in
                                    let uu____888 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____876
                                      uu____888
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____892 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____892 with
                                  | (t,uu____898) ->
                                      let expected_k =
                                        let uu____902 =
                                          let uu____909 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____910 =
                                            let uu____913 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____914 =
                                              let uu____917 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____917]  in
                                            uu____913 :: uu____914  in
                                          uu____909 :: uu____910  in
                                        let uu____918 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____902
                                          uu____918
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____923 =
                                      let uu____926 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____926
                                       in
                                    let uu____927 =
                                      let uu____928 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____928
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____923
                                      uu____927
                                     in
                                  let b_wp_a =
                                    let uu____940 =
                                      let uu____947 =
                                        let uu____948 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____948
                                         in
                                      [uu____947]  in
                                    let uu____949 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____940
                                      uu____949
                                     in
                                  let expected_k =
                                    let uu____955 =
                                      let uu____962 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____963 =
                                        let uu____966 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____967 =
                                          let uu____970 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____970]  in
                                        uu____966 :: uu____967  in
                                      uu____962 :: uu____963  in
                                    let uu____971 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____955
                                      uu____971
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____978 =
                                      let uu____985 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____986 =
                                        let uu____989 =
                                          let uu____990 =
                                            let uu____991 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____991
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____990
                                           in
                                        let uu____1000 =
                                          let uu____1003 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1003]  in
                                        uu____989 :: uu____1000  in
                                      uu____985 :: uu____986  in
                                    let uu____1004 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____978
                                      uu____1004
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1011 =
                                      let uu____1018 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1019 =
                                        let uu____1022 =
                                          let uu____1023 =
                                            let uu____1024 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1024
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1023
                                           in
                                        let uu____1033 =
                                          let uu____1036 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1036]  in
                                        uu____1022 :: uu____1033  in
                                      uu____1018 :: uu____1019  in
                                    let uu____1037 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1011
                                      uu____1037
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1044 =
                                      let uu____1051 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1051]  in
                                    let uu____1052 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1044
                                      uu____1052
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1056 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1056 with
                                  | (t,uu____1062) ->
                                      let expected_k =
                                        let uu____1066 =
                                          let uu____1073 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1074 =
                                            let uu____1077 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1077]  in
                                          uu____1073 :: uu____1074  in
                                        let uu____1078 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1066
                                          uu____1078
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1081 =
                                  let uu____1092 =
                                    let uu____1093 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1093.FStar_Syntax_Syntax.n  in
                                  match uu____1092 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1108 ->
                                      let repr =
                                        let uu____1110 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1110 with
                                        | (t,uu____1116) ->
                                            let expected_k =
                                              let uu____1120 =
                                                let uu____1127 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1128 =
                                                  let uu____1131 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1131]  in
                                                uu____1127 :: uu____1128  in
                                              let uu____1132 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1120 uu____1132
                                               in
                                            tc_check_trivial_guard env2
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k
                                         in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.EraseUniverses;
                                            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                            env2 repr
                                           in
                                        let uu____1145 =
                                          let uu____1148 =
                                            let uu____1149 =
                                              let uu____1164 =
                                                let uu____1167 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1168 =
                                                  let uu____1171 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1171]  in
                                                uu____1167 :: uu____1168  in
                                              (repr1, uu____1164)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1149
                                             in
                                          FStar_Syntax_Syntax.mk uu____1148
                                           in
                                        uu____1145
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1186 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1186 wp  in
                                      let destruct_repr t =
                                        let uu____1199 =
                                          let uu____1200 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1200.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1199 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1211,(t1,uu____1213)::
                                             (wp,uu____1215)::[])
                                            -> (t1, wp)
                                        | uu____1258 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1269 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1269
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1270 =
                                          fresh_effect_signature ()  in
                                        match uu____1270 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1286 =
                                                let uu____1293 =
                                                  let uu____1294 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1294
                                                   in
                                                [uu____1293]  in
                                              let uu____1295 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1286 uu____1295
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
                                              let uu____1301 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1301
                                               in
                                            let wp_g_x =
                                              let uu____1305 =
                                                let uu____1306 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1307 =
                                                  let uu____1308 =
                                                    let uu____1309 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1309
                                                     in
                                                  [uu____1308]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1306 uu____1307
                                                 in
                                              uu____1305
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1318 =
                                                  let uu____1319 =
                                                    let uu____1320 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1320
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1329 =
                                                    let uu____1330 =
                                                      let uu____1333 =
                                                        let uu____1336 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1337 =
                                                          let uu____1340 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1341 =
                                                            let uu____1344 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1345 =
                                                              let uu____1348
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1348]
                                                               in
                                                            uu____1344 ::
                                                              uu____1345
                                                             in
                                                          uu____1340 ::
                                                            uu____1341
                                                           in
                                                        uu____1336 ::
                                                          uu____1337
                                                         in
                                                      r :: uu____1333  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1330
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1319 uu____1329
                                                   in
                                                uu____1318
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____1354 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____1354
                                              then
                                                let uu____1357 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____1358 =
                                                  let uu____1361 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____1361]  in
                                                uu____1357 :: uu____1358
                                              else []  in
                                            let expected_k =
                                              let uu____1366 =
                                                let uu____1373 =
                                                  let uu____1376 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____1377 =
                                                    let uu____1380 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____1380]  in
                                                  uu____1376 :: uu____1377
                                                   in
                                                let uu____1381 =
                                                  let uu____1384 =
                                                    let uu____1387 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1388 =
                                                      let uu____1391 =
                                                        let uu____1392 =
                                                          let uu____1393 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1393
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1392
                                                         in
                                                      let uu____1394 =
                                                        let uu____1397 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1398 =
                                                          let uu____1401 =
                                                            let uu____1402 =
                                                              let uu____1403
                                                                =
                                                                let uu____1410
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1410]
                                                                 in
                                                              let uu____1411
                                                                =
                                                                let uu____1414
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1414
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1403
                                                                uu____1411
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1402
                                                             in
                                                          [uu____1401]  in
                                                        uu____1397 ::
                                                          uu____1398
                                                         in
                                                      uu____1391 ::
                                                        uu____1394
                                                       in
                                                    uu____1387 :: uu____1388
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____1384
                                                   in
                                                FStar_List.append uu____1373
                                                  uu____1381
                                                 in
                                              let uu____1415 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1366 uu____1415
                                               in
                                            let uu____1418 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            (match uu____1418 with
                                             | (expected_k1,uu____1426,uu____1427)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env4 =
                                                   let uu___68_1432 = env3
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___68_1432.FStar_TypeChecker_Env.dep_graph)
                                                   }  in
                                                 let br =
                                                   check_and_gen' env4
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1
                                                    in
                                                 br)
                                         in
                                      let return_repr =
                                        let x_a =
                                          let uu____1442 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1442
                                           in
                                        let res =
                                          let wp =
                                            let uu____1449 =
                                              let uu____1450 =
                                                let uu____1451 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1451
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1460 =
                                                let uu____1461 =
                                                  let uu____1464 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1465 =
                                                    let uu____1468 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1468]  in
                                                  uu____1464 :: uu____1465
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1461
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1450 uu____1460
                                               in
                                            uu____1449
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1474 =
                                            let uu____1481 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1482 =
                                              let uu____1485 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1485]  in
                                            uu____1481 :: uu____1482  in
                                          let uu____1486 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1474
                                            uu____1486
                                           in
                                        let uu____1489 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k
                                           in
                                        match uu____1489 with
                                        | (expected_k1,uu____1503,uu____1504)
                                            ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1508 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1508 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1529 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____1554 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____1564 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____1564 with
                                               | (usubst,uvs) ->
                                                   let uu____1587 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs
                                                      in
                                                   let uu____1588 =
                                                     let uu___69_1589 = act
                                                        in
                                                     let uu____1590 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params
                                                        in
                                                     let uu____1591 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____1592 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___69_1589.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___69_1589.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____1590;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____1591;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____1592
                                                     }  in
                                                   (uu____1587, uu____1588))
                                             in
                                          match uu____1554 with
                                          | (env3,act1) ->
                                              let act_typ =
                                                let uu____1598 =
                                                  let uu____1599 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____1599.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____1598 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____1623 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____1623
                                                    then
                                                      let uu____1626 =
                                                        let uu____1629 =
                                                          let uu____1630 =
                                                            let uu____1631 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____1631
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____1630
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____1629
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____1626
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____1647 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____1648 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ
                                                 in
                                              (match uu____1648 with
                                               | (act_typ1,uu____1656,g_t) ->
                                                   let env' =
                                                     let uu___70_1659 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.dep_graph
                                                         =
                                                         (uu___70_1659.FStar_TypeChecker_Env.dep_graph)
                                                     }  in
                                                   ((let uu____1661 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____1661
                                                     then
                                                       let uu____1662 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____1663 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____1664 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____1662
                                                         uu____1663
                                                         uu____1664
                                                     else ());
                                                    (let uu____1666 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____1666 with
                                                     | (act_defn,uu____1674,g_a)
                                                         ->
                                                         let act_defn1 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.UnfoldUntil
                                                                FStar_Syntax_Syntax.Delta_constant]
                                                             env3 act_defn
                                                            in
                                                         let act_typ2 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.UnfoldUntil
                                                                FStar_Syntax_Syntax.Delta_constant;
                                                             FStar_TypeChecker_Normalize.Eager_unfolding;
                                                             FStar_TypeChecker_Normalize.Beta]
                                                             env3 act_typ1
                                                            in
                                                         let uu____1678 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs,c) ->
                                                               let uu____1706
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c
                                                                  in
                                                               (match uu____1706
                                                                with
                                                                | (bs1,uu____1716)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____1723
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1723
                                                                     in
                                                                    let uu____1726
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____1726
                                                                    with
                                                                    | 
                                                                    (k1,uu____1738,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____1740 ->
                                                               let uu____1741
                                                                 =
                                                                 let uu____1746
                                                                   =
                                                                   let uu____1747
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____1748
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____1747
                                                                    uu____1748
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____1746)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____1741
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____1678
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____1757
                                                                  =
                                                                  let uu____1758
                                                                    =
                                                                    let uu____1759
                                                                    =
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_k
                                                                    uu____1759
                                                                     in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g_a
                                                                    uu____1758
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____1757);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____1763
                                                                    =
                                                                    let uu____1764
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____1764.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____1763
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____1787
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____1787
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____1796
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1796
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1818
                                                                    =
                                                                    let uu____1819
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____1819]
                                                                     in
                                                                    let uu____1820
                                                                    =
                                                                    let uu____1829
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1829]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1818;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1820;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1830
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1830))
                                                                  | uu____1833
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____1836
                                                                  =
                                                                  if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                  then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                  else
                                                                    (
                                                                    let uu____1838
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____1838))
                                                                   in
                                                                match uu____1836
                                                                with
                                                                | (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.Beta]
                                                                    env3
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___71_1847
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___71_1847.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___71_1847.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___71_1847.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    }))))))
                                           in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action)
                                         in
                                      (repr, bind_repr, return_repr, actions)
                                   in
                                match uu____1081 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1871 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1871
                                       in
                                    let uu____1874 =
                                      let uu____1881 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1881 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1902 ->
                                               let uu____1905 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____1911 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____1911 =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____1905
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1921 =
                                                    let uu____1926 =
                                                      let uu____1927 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1928 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1927 uu____1928
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1926)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1921
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1874 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1942 =
                                             let uu____1947 =
                                               let uu____1948 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1948.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1947)  in
                                           match uu____1942 with
                                           | ([],uu____1951) -> t
                                           | (uu____1962,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1963,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1981 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1994 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1994
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1999 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____2001 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____2001))
                                                && (m <> n1)
                                               in
                                            if uu____1999
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____2017 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____2024 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____2025 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____2017 uu____2024
                                                  uu____2025
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____2033 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____2033 with
                                           | (univs2,defn) ->
                                               let uu____2040 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____2040 with
                                                | (univs',typ) ->
                                                    let uu___72_2050 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___72_2050.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___72_2050.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___72_2050.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___73_2055 = ed2  in
                                           let uu____2056 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____2057 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____2058 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____2059 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____2060 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____2061 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____2062 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____2063 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____2064 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____2065 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____2066 =
                                             let uu____2067 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____2067
                                              in
                                           let uu____2078 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____2079 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____2080 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___73_2055.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___73_2055.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2056;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2057;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2058;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2059;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2060;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2061;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2062;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2063;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2064;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2065;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2066;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2078;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2079;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2080;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___73_2055.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____2084 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____2084
                                           then
                                             let uu____2085 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____2085
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
      let uu____2103 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2103 with
      | (effect_binders_un,signature_un) ->
          let uu____2120 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2120 with
           | (effect_binders,env1,uu____2139) ->
               let uu____2140 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2140 with
                | (signature,uu____2156) ->
                    let raise_error1 a uu____2167 =
                      match uu____2167 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2193  ->
                           match uu____2193 with
                           | (bv,qual) ->
                               let uu____2204 =
                                 let uu___74_2205 = bv  in
                                 let uu____2206 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___74_2205.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___74_2205.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2206
                                 }  in
                               (uu____2204, qual)) effect_binders
                       in
                    let uu____2209 =
                      let uu____2216 =
                        let uu____2217 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2217.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2216 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2227)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2249 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2209 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2267 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2267
                           then
                             let uu____2268 =
                               let uu____2271 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2271  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2268
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2305 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2305 with
                           | (t2,comp,uu____2318) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2325 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2325 with
                          | (repr,_comp) ->
                              ((let uu____2347 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2347
                                then
                                  let uu____2348 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2348
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
                                  let uu____2354 =
                                    let uu____2355 =
                                      let uu____2356 =
                                        let uu____2371 =
                                          let uu____2378 =
                                            let uu____2383 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2384 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2383, uu____2384)  in
                                          [uu____2378]  in
                                        (wp_type1, uu____2371)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2356
                                       in
                                    mk1 uu____2355  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2354
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2409 =
                                      let uu____2414 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2414)  in
                                    let uu____2415 =
                                      let uu____2422 =
                                        let uu____2423 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2423
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2422]  in
                                    uu____2409 :: uu____2415  in
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
                                  let uu____2486 = item  in
                                  match uu____2486 with
                                  | (u_item,item1) ->
                                      let uu____2507 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2507 with
                                       | (item2,item_comp) ->
                                           ((let uu____2523 =
                                               let uu____2524 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2524
                                                in
                                             if uu____2523
                                             then
                                               let uu____2525 =
                                                 let uu____2530 =
                                                   let uu____2531 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2532 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2531 uu____2532
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2530)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2525
                                             else ());
                                            (let uu____2534 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2534 with
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
                                let uu____2554 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2554 with
                                | (dmff_env1,uu____2578,bind_wp,bind_elab) ->
                                    let uu____2581 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2581 with
                                     | (dmff_env2,uu____2605,return_wp,return_elab)
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
                                           let uu____2612 =
                                             let uu____2613 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2613.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2612 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2657 =
                                                       let uu____2672 =
                                                         let uu____2677 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2677
                                                          in
                                                       match uu____2672 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2741 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2657 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2780 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2780
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2797 =
                                                               let uu____2798
                                                                 =
                                                                 let uu____2813
                                                                   =
                                                                   let uu____2820
                                                                    =
                                                                    let uu____2825
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2826
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2825,
                                                                    uu____2826)
                                                                     in
                                                                   [uu____2820]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2813)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2798
                                                                in
                                                             mk1 uu____2797
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2841 =
                                                           let uu____2850 =
                                                             let uu____2851 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2851
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2850
                                                            in
                                                         (match uu____2841
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail1 a393
                                                                =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2870
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2872
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    let uu____2873
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
                                                                    uu____2872
                                                                    uu____2873
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
                                                                    let uu____2878
                                                                    =
                                                                    let uu____2879
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____2879
                                                                     in
                                                                    if
                                                                    uu____2878
                                                                    then
                                                                    fail1 ()
                                                                    else ());
                                                                    (
                                                                    let uu____2881
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
                                                                    uu____2881
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
                                                                  let uu____2908
                                                                    =
                                                                    let uu____2909
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2910
                                                                    =
                                                                    let uu____2911
                                                                    =
                                                                    let uu____2918
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2918,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2911]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2909
                                                                    uu____2910
                                                                     in
                                                                  uu____2908
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2943
                                                                  =
                                                                  let uu____2944
                                                                    =
                                                                    let uu____2951
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2951]
                                                                     in
                                                                  b11 ::
                                                                    uu____2944
                                                                   in
                                                                let uu____2956
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2943
                                                                  uu____2956
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2957 ->
                                                  Obj.repr
                                                    (let uu____2958 =
                                                       let uu____2963 =
                                                         let uu____2964 =
                                                           FStar_Syntax_Print.term_to_string
                                                             return_wp
                                                            in
                                                         FStar_Util.format1
                                                           "unexpected shape for return: %s"
                                                           uu____2964
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         uu____2963)
                                                        in
                                                     raise_error1 ()
                                                       uu____2958))
                                            in
                                         let return_wp1 =
                                           let uu____2966 =
                                             let uu____2967 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2967.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2966 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____3011 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____3011
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____3024 ->
                                                  Obj.repr
                                                    (let uu____3025 =
                                                       let uu____3030 =
                                                         let uu____3031 =
                                                           FStar_Syntax_Print.term_to_string
                                                             return_wp
                                                            in
                                                         FStar_Util.format1
                                                           "unexpected shape for return: %s"
                                                           uu____3031
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         uu____3030)
                                                        in
                                                     raise_error1 ()
                                                       uu____3025))
                                            in
                                         let bind_wp1 =
                                           let uu____3033 =
                                             let uu____3034 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____3034.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____3033 with
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
                                                     let uu____3061 =
                                                       let uu____3062 =
                                                         let uu____3065 =
                                                           let uu____3066 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____3066
                                                            in
                                                         [uu____3065]  in
                                                       FStar_List.append
                                                         uu____3062 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____3061 body what)
                                              | uu____3067 ->
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
                                             (let uu____3085 =
                                                let uu____3086 =
                                                  let uu____3087 =
                                                    let uu____3102 =
                                                      let uu____3103 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3103
                                                       in
                                                    (t, uu____3102)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3087
                                                   in
                                                mk1 uu____3086  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3085)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3133 = f a2  in
                                               [uu____3133]
                                           | x::xs ->
                                               let uu____3138 =
                                                 apply_last1 f xs  in
                                               x :: uu____3138
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
                                           let uu____3156 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3156 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3186 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3186
                                                 then
                                                   let uu____3187 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3187
                                                 else ());
                                                (let uu____3189 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3189))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3198 =
                                                 let uu____3203 = mk_lid name
                                                    in
                                                 let uu____3204 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3203 uu____3204
                                                  in
                                               (match uu____3198 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3208 =
                                                        let uu____3211 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3211
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3208);
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
                                          (let uu____3308 =
                                             let uu____3311 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3312 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3311 :: uu____3312  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3308);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3410 =
                                               let uu____3413 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3414 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3413 :: uu____3414  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3410);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3509 =
                                                FStar_List.fold_left
                                                  (fun uu____3549  ->
                                                     fun action  ->
                                                       match uu____3549 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3570 =
                                                             let uu____3577 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3577
                                                               params_un
                                                              in
                                                           (match uu____3570
                                                            with
                                                            | (action_params,env',uu____3586)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3606
                                                                     ->
                                                                    match uu____3606
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3617
                                                                    =
                                                                    let uu___75_3618
                                                                    = bv  in
                                                                    let uu____3619
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___75_3618.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___75_3618.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3619
                                                                    }  in
                                                                    (uu____3617,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3623
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3623
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
                                                                    uu____3653
                                                                    ->
                                                                    let uu____3654
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3654
                                                                     in
                                                                    ((
                                                                    let uu____3658
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3658
                                                                    then
                                                                    let uu____3659
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3660
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3661
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3662
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3659
                                                                    uu____3660
                                                                    uu____3661
                                                                    uu____3662
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
                                                                    let uu____3666
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    let uu___76_3670
                                                                    = action
                                                                     in
                                                                    let uu____3671
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3672
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___76_3670.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___76_3670.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___76_3670.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3671;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3672
                                                                    }  in
                                                                    uu____3669
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3666))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3509 with
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
                                                      let uu____3705 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3706 =
                                                        let uu____3709 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3709]  in
                                                      uu____3705 ::
                                                        uu____3706
                                                       in
                                                    let uu____3710 =
                                                      let uu____3711 =
                                                        let uu____3712 =
                                                          let uu____3713 =
                                                            let uu____3728 =
                                                              let uu____3735
                                                                =
                                                                let uu____3740
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3741
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3740,
                                                                  uu____3741)
                                                                 in
                                                              [uu____3735]
                                                               in
                                                            (repr,
                                                              uu____3728)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3713
                                                           in
                                                        mk1 uu____3712  in
                                                      let uu____3756 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3711
                                                        uu____3756
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3710
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3759 =
                                                    let uu____3766 =
                                                      let uu____3767 =
                                                        let uu____3770 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3770
                                                         in
                                                      uu____3767.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3766 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3780)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3809
                                                                =
                                                                let uu____3826
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3826
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3884
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3809
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3934
                                                                    =
                                                                    let uu____3935
                                                                    =
                                                                    let uu____3938
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3938
                                                                     in
                                                                    uu____3935.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3934
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3963
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3963
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3976
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____4001
                                                                     ->
                                                                    match uu____4001
                                                                    with
                                                                    | 
                                                                    (bv,uu____4007)
                                                                    ->
                                                                    let uu____4008
                                                                    =
                                                                    let uu____4009
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4009
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4008
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3976
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
                                                                    let uu____4073
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4073
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4078
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4086
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4086
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4091
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4094
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4091,
                                                                    uu____4094)))
                                                                    | 
                                                                    uu____4101
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4102
                                                                    =
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4108
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4108
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4107)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4102)))
                                                       | uu____4109 ->
                                                           Obj.repr
                                                             (let uu____4110
                                                                =
                                                                let uu____4115
                                                                  =
                                                                  let uu____4116
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____4116
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____4115)
                                                                 in
                                                              raise_error1 ()
                                                                uu____4110))
                                                     in
                                                  (match uu____3759 with
                                                   | (pre,post) ->
                                                       ((let uu____4134 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4136 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4138 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___77_4140 =
                                                             ed  in
                                                           let uu____4141 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4142 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____4143 =
                                                             let uu____4144 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4144)
                                                              in
                                                           let uu____4151 =
                                                             let uu____4152 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4152)
                                                              in
                                                           let uu____4159 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____4160 =
                                                             let uu____4161 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4161)
                                                              in
                                                           let uu____4168 =
                                                             let uu____4169 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4169)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4141;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4142;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4143;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4151;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4159;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4160;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4168;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___77_4140.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____4176 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4176
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4194
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4194
                                                               then
                                                                 let uu____4195
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4195
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
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4210
                                                                    =
                                                                    let uu____4219
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4219)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4210
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
                                                                    uu____4207;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4234
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4234
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4236
                                                                 =
                                                                 let uu____4239
                                                                   =
                                                                   let uu____4242
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4242
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4239
                                                                   sigelts'
                                                                  in
                                                               (uu____4236,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4299 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4299 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4332 = FStar_List.hd ses  in
            uu____4332.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4337 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4341,[],t,uu____4343,uu____4344);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4346;
               FStar_Syntax_Syntax.sigattrs = uu____4347;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4349,_t_top,_lex_t_top,_0_40,uu____4352);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4354;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4355;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4357,_t_cons,_lex_t_cons,_0_41,uu____4360);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4362;
                 FStar_Syntax_Syntax.sigattrs = uu____4363;_}::[]
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
                 let uu____4422 =
                   let uu____4425 =
                     let uu____4426 =
                       let uu____4433 =
                         let uu____4434 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____4434
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4433, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4426  in
                   FStar_Syntax_Syntax.mk uu____4425  in
                 uu____4422 FStar_Pervasives_Native.None r1  in
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
                   let uu____4452 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4452
                    in
                 let hd1 =
                   let uu____4454 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4454
                    in
                 let tl1 =
                   let uu____4456 =
                     let uu____4457 =
                       let uu____4460 =
                         let uu____4461 =
                           let uu____4468 =
                             let uu____4469 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____4469
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4468, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4461  in
                       FStar_Syntax_Syntax.mk uu____4460  in
                     uu____4457 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4456
                    in
                 let res =
                   let uu____4478 =
                     let uu____4481 =
                       let uu____4482 =
                         let uu____4489 =
                           let uu____4490 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____4490
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4489,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4482  in
                     FStar_Syntax_Syntax.mk uu____4481  in
                   uu____4478 FStar_Pervasives_Native.None r2  in
                 let uu____4496 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4496
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
               let uu____4535 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4535;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4540 ->
               let err_msg =
                 let uu____4544 =
                   let uu____4545 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4545  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4544
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
        let uu____4560 = FStar_Syntax_Util.type_u ()  in
        match uu____4560 with
        | (k,uu____4566) ->
            let phi1 =
              let uu____4568 = tc_check_trivial_guard env1 phi k  in
              FStar_All.pipe_right uu____4568
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
          let uu____4601 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4601 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4632 =
                  FStar_List.map
                    (FStar_TypeChecker_TcInductive.mk_data_operations quals
                       env1 tcs) datas
                   in
                FStar_All.pipe_right uu____4632 FStar_List.flatten  in
              ((let uu____4646 =
                  (FStar_Options.no_positivity ()) ||
                    (let uu____4648 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     Prims.op_Negation uu____4648)
                   in
                if uu____4646
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
                          let uu____4659 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4669,uu____4670,uu____4671,uu____4672,uu____4673)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4682 -> failwith "Impossible!"  in
                          match uu____4659 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4693 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4697,uu____4698,uu____4699,uu____4700,uu____4701)
                        -> lid
                    | uu____4710 -> failwith "Impossible"  in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    FStar_TypeChecker_TcInductive.early_prims_inductives
                   in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals
                   in
                let res =
                  let uu____4723 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4723
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
                (let uu____4745 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____4750 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____4750 en  in
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4785 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4810 ->
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
             let uu____4865 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env2)
                in
             if uu____4865
             then
               let ses1 =
                 let uu____4871 =
                   let uu____4872 =
                     let uu____4873 =
                       tc_inductive
                         (let uu___78_4882 = env2  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___78_4882.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___78_4882.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___78_4882.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___78_4882.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___78_4882.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___78_4882.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___78_4882.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___78_4882.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___78_4882.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___78_4882.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___78_4882.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___78_4882.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___78_4882.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___78_4882.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___78_4882.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___78_4882.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___78_4882.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___78_4882.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___78_4882.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___78_4882.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___78_4882.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___78_4882.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___78_4882.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___78_4882.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___78_4882.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___78_4882.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___78_4882.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___78_4882.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___78_4882.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___78_4882.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___78_4882.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___78_4882.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___78_4882.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___78_4882.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___78_4882.FStar_TypeChecker_Env.dep_graph)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____4873
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____4872
                     (FStar_TypeChecker_Normalize.elim_uvars env2)
                    in
                 FStar_All.pipe_right uu____4871
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____4894 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____4894
                 then
                   let uu____4895 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___79_4898 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___79_4898.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___79_4898.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___79_4898.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___79_4898.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____4895
                 else ());
                ses1)
             else ses  in
           let uu____4905 =
             tc_inductive env2 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4905 with
            | (sigbndle,projectors_ses) -> ([sigbndle], projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4937 = cps_and_elaborate env1 ne  in
           (match uu____4937 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___80_4974 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___80_4974.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___80_4974.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___80_4974.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___80_4974.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___81_4976 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___81_4976.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___81_4976.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___81_4976.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___81_4976.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____4983 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____4983
             then
               let ne1 =
                 let uu____4985 =
                   let uu____4986 =
                     let uu____4987 =
                       tc_eff_decl
                         (let uu___82_4990 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___82_4990.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___82_4990.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___82_4990.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___82_4990.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___82_4990.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___82_4990.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___82_4990.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___82_4990.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___82_4990.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___82_4990.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___82_4990.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___82_4990.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___82_4990.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___82_4990.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___82_4990.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___82_4990.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___82_4990.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___82_4990.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___82_4990.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___82_4990.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___82_4990.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___82_4990.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___82_4990.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___82_4990.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___82_4990.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___82_4990.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___82_4990.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___82_4990.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___82_4990.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___82_4990.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___82_4990.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___82_4990.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___82_4990.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___82_4990.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___82_4990.FStar_TypeChecker_Env.dep_graph)
                          }) ne
                        in
                     FStar_All.pipe_right uu____4987
                       (fun ne1  ->
                          let uu___83_4994 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___83_4994.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___83_4994.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___83_4994.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___83_4994.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____4986
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____4985
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____4996 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____4996
                 then
                   let uu____4997 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___84_5000 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___84_5000.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___84_5000.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___84_5000.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___84_5000.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____4997
                 else ());
                ne1)
             else ne  in
           let ne2 = tc_eff_decl env1 ne1  in
           let se1 =
             let uu___85_5005 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___85_5005.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___85_5005.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___85_5005.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___85_5005.FStar_Syntax_Syntax.sigattrs)
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
           let uu____5013 =
             let uu____5020 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5020
              in
           (match uu____5013 with
            | (a,wp_a_src) ->
                let uu____5035 =
                  let uu____5042 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____5042
                   in
                (match uu____5035 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____5058 =
                         let uu____5061 =
                           let uu____5062 =
                             let uu____5069 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____5069)  in
                           FStar_Syntax_Syntax.NT uu____5062  in
                         [uu____5061]  in
                       FStar_Syntax_Subst.subst uu____5058 wp_b_tgt  in
                     let expected_k =
                       let uu____5073 =
                         let uu____5080 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____5081 =
                           let uu____5084 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____5084]  in
                         uu____5080 :: uu____5081  in
                       let uu____5085 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____5073 uu____5085  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5106 =
                           let uu____5111 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5111)
                            in
                         let uu____5112 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____5106 uu____5112  in
                       let uu____5115 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____5115 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____5147 =
                             let uu____5148 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____5148  in
                           if uu____5147
                           then no_reify eff_name
                           else
                             (let uu____5154 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____5155 =
                                let uu____5158 =
                                  let uu____5159 =
                                    let uu____5174 =
                                      let uu____5177 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____5178 =
                                        let uu____5181 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____5181]  in
                                      uu____5177 :: uu____5178  in
                                    (repr, uu____5174)  in
                                  FStar_Syntax_Syntax.Tm_app uu____5159  in
                                FStar_Syntax_Syntax.mk uu____5158  in
                              uu____5155 FStar_Pervasives_Native.None
                                uu____5154)
                        in
                     let uu____5187 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____5239 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5248 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____5248 with
                               | (usubst,uvs1) ->
                                   let uu____5271 =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env1 uvs1
                                      in
                                   let uu____5272 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____5271, uu____5272)
                             else (env1, lift_wp)  in
                           (match uu____5239 with
                            | (env2,lift_wp1) ->
                                let lift_wp2 =
                                  if
                                    (FStar_List.length uvs) =
                                      (Prims.parse_int "0")
                                  then check_and_gen env2 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env2 lift_wp1
                                         expected_k
                                        in
                                     let uu____5285 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____5285))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____5312 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5325 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____5325 with
                               | (usubst,uvs) ->
                                   let uu____5350 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____5350)
                             else ([], lift)  in
                           (match uu____5312 with
                            | (uvs,lift1) ->
                                ((let uu____5369 =
                                    FStar_TypeChecker_Env.debug env1
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____5369
                                  then
                                    let uu____5370 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____5370
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env1
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env1 FStar_Range.dummyRange)
                                     in
                                  let uu____5373 =
                                    let uu____5380 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env1 uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____5380 lift1
                                     in
                                  match uu____5373 with
                                  | (lift2,comp,uu____5389) ->
                                      let uu____5390 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____5390 with
                                       | (uu____5403,lift_wp,lift_elab) ->
                                           let uu____5406 =
                                             recheck_debug "lift-wp" env1
                                               lift_wp
                                              in
                                           let uu____5407 =
                                             recheck_debug "lift-elab" env1
                                               lift_elab
                                              in
                                           let uu____5408 =
                                             let uu____5417 =
                                               let uu____5424 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_elab
                                                  in
                                               (uvs, uu____5424)  in
                                             FStar_Pervasives_Native.Some
                                               uu____5417
                                              in
                                           let uu____5433 =
                                             let uu____5440 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 uvs lift_wp
                                                in
                                             (uvs, uu____5440)  in
                                           (uu____5408, uu____5433)))))
                        in
                     (match uu____5187 with
                      | (lift,lift_wp) ->
                          let env2 =
                            let uu___86_5472 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___86_5472.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___86_5472.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___86_5472.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___86_5472.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___86_5472.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___86_5472.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___86_5472.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___86_5472.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___86_5472.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___86_5472.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___86_5472.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___86_5472.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___86_5472.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___86_5472.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___86_5472.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___86_5472.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___86_5472.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___86_5472.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___86_5472.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___86_5472.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___86_5472.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___86_5472.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___86_5472.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___86_5472.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___86_5472.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___86_5472.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___86_5472.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___86_5472.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___86_5472.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___86_5472.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___86_5472.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___86_5472.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___86_5472.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___86_5472.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___86_5472.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____5490 =
                                  let uu____5495 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____5495 with
                                  | (usubst,uvs1) ->
                                      let uu____5518 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env2 uvs1
                                         in
                                      let uu____5519 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____5518, uu____5519)
                                   in
                                (match uu____5490 with
                                 | (env3,lift2) ->
                                     let uu____5524 =
                                       let uu____5531 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env3
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env3
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____5531
                                        in
                                     (match uu____5524 with
                                      | (a1,wp_a_src1) ->
                                          let wp_a =
                                            FStar_Syntax_Syntax.new_bv
                                              FStar_Pervasives_Native.None
                                              wp_a_src1
                                             in
                                          let a_typ =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          let wp_a_typ =
                                            FStar_Syntax_Syntax.bv_to_name
                                              wp_a
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
                                                env3
                                                (FStar_Pervasives_Native.snd
                                                   lift_wp)
                                               in
                                            let lift_wp_a =
                                              let uu____5555 =
                                                FStar_TypeChecker_Env.get_range
                                                  env3
                                                 in
                                              let uu____5556 =
                                                let uu____5559 =
                                                  let uu____5560 =
                                                    let uu____5575 =
                                                      let uu____5578 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____5579 =
                                                        let uu____5582 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____5582]  in
                                                      uu____5578 ::
                                                        uu____5579
                                                       in
                                                    (lift_wp1, uu____5575)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____5560
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____5559
                                                 in
                                              uu____5556
                                                FStar_Pervasives_Native.None
                                                uu____5555
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____5591 =
                                              let uu____5598 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____5599 =
                                                let uu____5602 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____5603 =
                                                  let uu____5606 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____5606]  in
                                                uu____5602 :: uu____5603  in
                                              uu____5598 :: uu____5599  in
                                            let uu____5607 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5591 uu____5607
                                             in
                                          let uu____5610 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env3 expected_k1
                                             in
                                          (match uu____5610 with
                                           | (expected_k2,uu____5620,uu____5621)
                                               ->
                                               let lift3 =
                                                 if
                                                   (FStar_List.length uvs) =
                                                     (Prims.parse_int "0")
                                                 then
                                                   check_and_gen env3 lift2
                                                     expected_k2
                                                 else
                                                   (let lift3 =
                                                      tc_check_trivial_guard
                                                        env3 lift2
                                                        expected_k2
                                                       in
                                                    let uu____5625 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____5625))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          let sub2 =
                            let uu___87_5629 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___87_5629.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___87_5629.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___88_5631 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___88_5631.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___88_5631.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___88_5631.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___88_5631.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let uu____5646 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env1, uvs, tps, c)
             else
               (let uu____5664 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____5664 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____5693 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____5693 c  in
                    let uu____5700 =
                      FStar_TypeChecker_Env.push_univ_vars env1 uvs1  in
                    (uu____5700, uvs1, tps1, c1))
              in
           (match uu____5646 with
            | (env2,uvs1,tps1,c1) ->
                let env3 = FStar_TypeChecker_Env.set_range env2 r  in
                let uu____5716 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____5716 with
                 | (tps2,c2) ->
                     let uu____5731 =
                       FStar_TypeChecker_TcTerm.tc_tparams env3 tps2  in
                     (match uu____5731 with
                      | (tps3,env4,us) ->
                          let uu____5749 =
                            FStar_TypeChecker_TcTerm.tc_comp env4 c2  in
                          (match uu____5749 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env4 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____5770 =
                                   let uu____5771 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____5771
                                    in
                                 match uu____5770 with
                                 | (uvs2,t) ->
                                     let uu____5786 =
                                       let uu____5799 =
                                         let uu____5804 =
                                           let uu____5805 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____5805.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____5804)  in
                                       match uu____5799 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____5820,c5)) -> ([], c5)
                                       | (uu____5860,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____5887 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____5786 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____5931 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____5931 with
                                              | (uu____5936,t1) ->
                                                  let uu____5938 =
                                                    let uu____5943 =
                                                      let uu____5944 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____5945 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____5946 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____5944 uu____5945
                                                        uu____5946
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____5943)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5938 r)
                                           else ();
                                           (let se1 =
                                              let uu___89_5949 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___89_5949.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___89_5949.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___89_5949.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___89_5949.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5966,uu____5967,uu____5968) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___58_5972  ->
                   match uu___58_5972 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5973 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5978,uu____5979) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___58_5987  ->
                   match uu___58_5987 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5988 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5998 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5998
             then
               let uu____5999 =
                 let uu____6004 =
                   let uu____6005 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____6005
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____6004)
                  in
               FStar_Errors.raise_error uu____5999 r
             else ());
            (let uu____6007 =
               if uvs = []
               then
                 let uu____6008 =
                   let uu____6009 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____6009  in
                 check_and_gen env2 t uu____6008
               else
                 (let uu____6015 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____6015 with
                  | (uvs1,t1) ->
                      let env3 =
                        FStar_TypeChecker_Env.push_univ_vars env2 uvs1  in
                      let t2 =
                        let uu____6024 =
                          let uu____6025 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____6025  in
                        tc_check_trivial_guard env3 t1 uu____6024  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env3 t2
                         in
                      let uu____6031 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____6031))
                in
             match uu____6007 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___90_6047 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___90_6047.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___90_6047.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___90_6047.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___90_6047.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____6057 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____6057 with
            | (us1,phi1) ->
                let env2 = FStar_TypeChecker_Env.push_univ_vars env1 us1  in
                let phi2 =
                  let uu____6074 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env2)
                     in
                  if uu____6074
                  then
                    let phi2 =
                      let uu____6076 =
                        tc_assume
                          (let uu___91_6079 = env2  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___91_6079.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___91_6079.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___91_6079.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___91_6079.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___91_6079.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___91_6079.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___91_6079.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___91_6079.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___91_6079.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___91_6079.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___91_6079.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___91_6079.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___91_6079.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___91_6079.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___91_6079.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___91_6079.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___91_6079.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___91_6079.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___91_6079.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___91_6079.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___91_6079.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___91_6079.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___91_6079.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___91_6079.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___91_6079.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___91_6079.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___91_6079.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___91_6079.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___91_6079.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___91_6079.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___91_6079.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___91_6079.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___91_6079.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___91_6079.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___91_6079.FStar_TypeChecker_Env.dep_graph)
                           }) phi1 r
                         in
                      FStar_All.pipe_right uu____6076
                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                           env2)
                       in
                    ((let uu____6081 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env2)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____6081
                      then
                        let uu____6082 =
                          FStar_Syntax_Print.term_to_string phi2  in
                        FStar_Util.print1 "Assume after phase 1: %s\n"
                          uu____6082
                      else ());
                     phi2)
                  else phi1  in
                let phi3 = tc_assume env2 phi2 r  in
                let uu____6086 =
                  if us1 = []
                  then FStar_TypeChecker_Util.generalize_universes env2 phi3
                  else
                    (let uu____6088 =
                       FStar_Syntax_Subst.close_univ_vars us1 phi3  in
                     (us1, uu____6088))
                   in
                (match uu____6086 with
                 | (us2,phi4) ->
                     ([{
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_assume (lid, us2, phi4));
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
           let uu____6112 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____6112 with
            | (e1,c,g1) ->
                let uu____6130 =
                  let uu____6137 =
                    let uu____6140 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____6140  in
                  let uu____6141 =
                    let uu____6146 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____6146)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____6137 uu____6141
                   in
                (match uu____6130 with
                 | (e2,uu____6156,g) ->
                     ((let uu____6159 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____6159);
                      (let se1 =
                         let uu___92_6161 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_6161.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___92_6161.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_6161.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_6161.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____6173 = FStar_Options.debug_any ()  in
             if uu____6173
             then
               let uu____6174 =
                 FStar_Ident.string_of_lid
                   env1.FStar_TypeChecker_Env.curmodule
                  in
               let uu____6175 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____6174
                 uu____6175
             else ());
            (let ses = env1.FStar_TypeChecker_Env.splice env1 t  in
             let lids' =
               FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses  in
             FStar_List.iter
               (fun lid  ->
                  let uu____6188 =
                    FStar_List.tryFind (FStar_Ident.lid_equals lid) lids'  in
                  match uu____6188 with
                  | FStar_Pervasives_Native.Some uu____6191 -> ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____6192 =
                        let uu____6197 =
                          let uu____6198 = FStar_Ident.string_of_lid lid  in
                          let uu____6199 =
                            let uu____6200 =
                              FStar_List.map FStar_Ident.string_of_lid lids'
                               in
                            FStar_All.pipe_left (FStar_String.concat ", ")
                              uu____6200
                             in
                          FStar_Util.format2
                            "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                            uu____6198 uu____6199
                           in
                        (FStar_Errors.Fatal_SplicedUndef, uu____6197)  in
                      FStar_Errors.raise_error uu____6192 r) lids;
             ([], ses)))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____6255 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____6255
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____6263 =
                      let uu____6268 =
                        let uu____6269 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____6270 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____6271 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____6269 uu____6270 uu____6271
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____6268)
                       in
                    FStar_Errors.raise_error uu____6263 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____6297 =
                   let uu____6298 = FStar_Syntax_Subst.compress def  in
                   uu____6298.FStar_Syntax_Syntax.n  in
                 match uu____6297 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6308,uu____6309)
                     -> binders
                 | uu____6330 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6340;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6418) -> val_bs1
                     | (uu____6441,[]) -> val_bs1
                     | ((body_bv,uu____6465)::bt,(val_bv,aqual)::vt) ->
                         let uu____6502 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6518) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___93_6520 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___94_6523 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___94_6523.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___93_6520.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___93_6520.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6502
                      in
                   let uu____6524 =
                     let uu____6527 =
                       let uu____6528 =
                         let uu____6541 = rename_binders1 def_bs val_bs  in
                         (uu____6541, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6528  in
                     FStar_Syntax_Syntax.mk uu____6527  in
                   uu____6524 FStar_Pervasives_Native.None r1
               | uu____6559 -> typ1  in
             let uu___95_6560 = lb  in
             let uu____6561 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___95_6560.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___95_6560.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6561;
               FStar_Syntax_Syntax.lbeff =
                 (uu___95_6560.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___95_6560.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___95_6560.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___95_6560.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____6564 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6615  ->
                     fun lb  ->
                       match uu____6615 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6657 =
                             let uu____6668 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6668 with
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
                                   | uu____6753 ->
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
                                  (let uu____6796 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def,
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____6796, quals_opt1)))
                              in
                           (match uu____6657 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6564 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6890 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___59_6894  ->
                                match uu___59_6894 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6895 -> false))
                         in
                      if uu____6890
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6905 =
                    let uu____6908 =
                      let uu____6909 =
                        let uu____6922 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6922)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6909  in
                    FStar_Syntax_Syntax.mk uu____6908  in
                  uu____6905 FStar_Pervasives_Native.None r  in
                let env0 =
                  let uu___96_6941 = env2  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___96_6941.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___96_6941.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___96_6941.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___96_6941.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___96_6941.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___96_6941.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___96_6941.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___96_6941.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___96_6941.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___96_6941.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___96_6941.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___96_6941.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___96_6941.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___96_6941.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___96_6941.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___96_6941.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___96_6941.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___96_6941.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___96_6941.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___96_6941.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___96_6941.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___96_6941.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___96_6941.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___96_6941.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___96_6941.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___96_6941.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___96_6941.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___96_6941.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___96_6941.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___96_6941.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___96_6941.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___96_6941.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___96_6941.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___96_6941.FStar_TypeChecker_Env.dep_graph)
                  }  in
                let e1 =
                  let uu____6943 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env0)
                     in
                  if uu____6943
                  then
                    let drop_lbtyp e_lax =
                      let uu____6948 =
                        let uu____6949 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____6949.FStar_Syntax_Syntax.n  in
                      match uu____6948 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____6967 =
                              let uu____6968 = FStar_Syntax_Subst.compress e
                                 in
                              uu____6968.FStar_Syntax_Syntax.n  in
                            match uu____6967 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____6971,lb1::[]),uu____6973) ->
                                let uu____6986 =
                                  let uu____6987 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____6987.FStar_Syntax_Syntax.n  in
                                uu____6986 = FStar_Syntax_Syntax.Tm_unknown
                            | uu____6990 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___97_6991 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___98_7003 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___98_7003.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___98_7003.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___98_7003.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___98_7003.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___98_7003.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___98_7003.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___97_6991.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___97_6991.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____7005 -> e_lax  in
                    let e1 =
                      let uu____7007 =
                        let uu____7008 =
                          let uu____7009 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___99_7018 = env0  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___99_7018.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___99_7018.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___99_7018.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___99_7018.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___99_7018.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___99_7018.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___99_7018.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___99_7018.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___99_7018.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___99_7018.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___99_7018.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___99_7018.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___99_7018.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___99_7018.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___99_7018.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___99_7018.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___99_7018.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___99_7018.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___99_7018.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___99_7018.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___99_7018.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___99_7018.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___99_7018.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___99_7018.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___99_7018.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___99_7018.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___99_7018.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___99_7018.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___99_7018.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___99_7018.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___99_7018.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___99_7018.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___99_7018.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___99_7018.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___99_7018.FStar_TypeChecker_Env.dep_graph)
                               }) e
                             in
                          FStar_All.pipe_right uu____7009
                            (fun uu____7029  ->
                               match uu____7029 with
                               | (e1,uu____7037,uu____7038) -> e1)
                           in
                        FStar_All.pipe_right uu____7008
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env0)
                         in
                      FStar_All.pipe_right uu____7007 drop_lbtyp  in
                    ((let uu____7040 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env2)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____7040
                      then
                        let uu____7041 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____7041
                      else ());
                     e1)
                  else e  in
                let uu____7044 =
                  let uu____7055 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1
                     in
                  match uu____7055 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e2);
                       FStar_Syntax_Syntax.pos = uu____7074;
                       FStar_Syntax_Syntax.vars = uu____7075;_},uu____7076,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____7105 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____7105)  in
                      let quals1 =
                        match e2.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____7123,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____7128 -> quals  in
                      ((let uu___100_7136 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___100_7136.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___100_7136.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___100_7136.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____7145 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____7044 with
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
                      (let uu____7194 = log env2  in
                       if uu____7194
                       then
                         let uu____7195 =
                           let uu____7196 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____7211 =
                                         let uu____7220 =
                                           let uu____7221 =
                                             let uu____7224 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____7224.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____7221.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____7220
                                          in
                                       match uu____7211 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____7231 -> false  in
                                     if should_log
                                     then
                                       let uu____7240 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____7241 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____7240 uu____7241
                                     else ""))
                              in
                           FStar_All.pipe_right uu____7196
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____7195
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
             (fun uu___60_7287  ->
                match uu___60_7287 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7288 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7294) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7300 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7309 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____7314 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7329 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7354 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7378) ->
          let uu____7387 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7387
          then
            let for_export_bundle se1 uu____7418 =
              match uu____7418 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7457,uu____7458) ->
                       let dec =
                         let uu___101_7468 = se1  in
                         let uu____7469 =
                           let uu____7470 =
                             let uu____7477 =
                               let uu____7480 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7480  in
                             (l, us, uu____7477)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7470  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7469;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___101_7468.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___101_7468.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___101_7468.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7492,uu____7493,uu____7494) ->
                       let dec =
                         let uu___102_7500 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___102_7500.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___102_7500.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___102_7500.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7505 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7527,uu____7528,uu____7529) ->
          let uu____7530 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7530 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7551 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7551
          then
            ([(let uu___103_7567 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___103_7567.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___103_7567.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___103_7567.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7569 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___61_7573  ->
                       match uu___61_7573 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7574 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7579 -> true
                       | uu____7580 -> false))
                in
             if uu____7569 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7598 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7603 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7608 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7613 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7618 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7636) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7653 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7653
          then ([], hidden)
          else
            (let dec =
               let uu____7670 = FStar_Ident.range_of_lid lid  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____7670;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____7685 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7685
          then
            let uu____7694 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___104_7707 = se  in
                      let uu____7708 =
                        let uu____7709 =
                          let uu____7716 =
                            let uu____7717 =
                              let uu____7720 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7720.FStar_Syntax_Syntax.fv_name  in
                            uu____7717.FStar_Syntax_Syntax.v  in
                          (uu____7716, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7709  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7708;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___104_7707.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___104_7707.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___104_7707.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7694, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7740 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7757 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7772) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____7775 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7776 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7786 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7786) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7787,uu____7788,uu____7789) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7793  ->
                  match uu___62_7793 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7794 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7795,uu____7796) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7804  ->
                  match uu___62_7804 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7805 -> false))
          -> env
      | uu____7806 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7866 se =
        match uu____7866 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7919 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7919
              then
                let uu____7920 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7920
              else ());
             (let uu____7922 = tc_decl env1 se  in
              match uu____7922 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7972 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____7972
                             then
                               let uu____7973 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7973
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
                          FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
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
                    (let uu____7996 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____7996
                     then
                       let uu____7997 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____8003 =
                                  let uu____8004 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____8004 "\n"  in
                                Prims.strcat s uu____8003) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____7997
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____8009 =
                       let uu____8018 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____8018
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____8053 se1 =
                            match uu____8053 with
                            | (exports1,hidden1) ->
                                let uu____8081 = for_export hidden1 se1  in
                                (match uu____8081 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____8009 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___105_8160 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___105_8160.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___105_8160.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___105_8160.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___105_8160.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____8238 = acc  in
        match uu____8238 with
        | (uu____8273,uu____8274,env1,uu____8276) ->
            let uu____8289 =
              FStar_Util.record_time
                (fun uu____8335  -> process_one_decl acc se)
               in
            (match uu____8289 with
             | (r,ms_elapsed) ->
                 ((let uu____8399 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8399
                   then
                     let uu____8400 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8401 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8400 uu____8401
                   else ());
                  r))
         in
      let uu____8403 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8403 with
      | (ses1,exports,env1,uu____8451) ->
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
          let uu___106_8482 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___106_8482.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___106_8482.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___106_8482.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___106_8482.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___106_8482.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___106_8482.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___106_8482.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___106_8482.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___106_8482.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___106_8482.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___106_8482.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___106_8482.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___106_8482.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___106_8482.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___106_8482.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___106_8482.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___106_8482.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___106_8482.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___106_8482.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___106_8482.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___106_8482.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___106_8482.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___106_8482.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___106_8482.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___106_8482.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___106_8482.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___106_8482.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___106_8482.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___106_8482.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___106_8482.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___106_8482.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___106_8482.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___106_8482.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8493 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8493 with
          | (univs2,t1) ->
              ((let uu____8501 =
                  let uu____8502 =
                    let uu____8505 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8505  in
                  FStar_All.pipe_left uu____8502
                    (FStar_Options.Other "Exports")
                   in
                if uu____8501
                then
                  let uu____8506 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8507 =
                    let uu____8508 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8508
                      (FStar_String.concat ", ")
                     in
                  let uu____8517 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8506 uu____8507 uu____8517
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____8520 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____8520 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____8544 =
             let uu____8545 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8546 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8545 uu____8546
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8544);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8553) ->
              let uu____8562 =
                let uu____8563 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8563  in
              if uu____8562
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8573,uu____8574) ->
              let t =
                let uu____8586 =
                  let uu____8589 =
                    let uu____8590 =
                      let uu____8603 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8603)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8590  in
                  FStar_Syntax_Syntax.mk uu____8589  in
                uu____8586 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8610,uu____8611,uu____8612) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8620 =
                let uu____8621 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8621  in
              if uu____8620 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8625,lbs),uu____8627) ->
              let uu____8642 =
                let uu____8643 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8643  in
              if uu____8642
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
              let uu____8662 =
                let uu____8663 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8663  in
              if uu____8662
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8670 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8671 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8678 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8679 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8680 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____8681 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8688 -> ()  in
        let uu____8689 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____8689 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____8766) -> true
             | uu____8767 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8786 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____8817 ->
                   let uu____8818 =
                     let uu____8821 =
                       let uu____8822 =
                         let uu____8835 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____8835)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____8822  in
                     FStar_Syntax_Syntax.mk uu____8821  in
                   uu____8818 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____8843,uu____8844) ->
            let s1 =
              let uu___107_8854 = s  in
              let uu____8855 =
                let uu____8856 =
                  let uu____8863 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____8863)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____8856  in
              let uu____8864 =
                let uu____8867 =
                  let uu____8870 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____8870  in
                FStar_Syntax_Syntax.Assumption :: uu____8867  in
              {
                FStar_Syntax_Syntax.sigel = uu____8855;
                FStar_Syntax_Syntax.sigrng =
                  (uu___107_8854.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____8864;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___107_8854.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___107_8854.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____8873 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____8887 =
        match uu____8887 with
        | (uvs,t) ->
            let uu___108_8894 = s  in
            let uu____8895 =
              let uu____8898 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____8898  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___108_8894.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____8895;
              FStar_Syntax_Syntax.sigmeta =
                (uu___108_8894.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___108_8894.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____8910 -> failwith "Impossible!"  in
        let c_opt =
          let uu____8914 = FStar_Syntax_Util.is_unit t  in
          if uu____8914
          then
            let uu____8917 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____8917
          else
            (let uu____8919 =
               let uu____8920 = FStar_Syntax_Subst.compress t  in
               uu____8920.FStar_Syntax_Syntax.n  in
             match uu____8919 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____8925,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____8945 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____8954 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____8954
           then
             let uu____8955 =
               let uu____8956 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____8956 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____8955
           else
             (let uu____8964 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect env uu____8964))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____8973 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____8992 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_splice uu____9009 ->
            failwith "Impossible! Trying to extract splice"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9049,uu____9050,uu____9051,uu____9052,uu____9053)
                         ->
                         ((let uu____9063 =
                             let uu____9066 =
                               FStar_ST.op_Bang abstract_inductive_tycons  in
                             lid :: uu____9066  in
                           FStar_ST.op_Colon_Equals abstract_inductive_tycons
                             uu____9063);
                          (let uu____9159 = vals_of_abstract_inductive s1  in
                           FStar_List.append uu____9159 sigelts1))
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____9163,uu____9164,uu____9165,uu____9166,uu____9167)
                         ->
                         ((let uu____9173 =
                             let uu____9176 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____9176  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____9173);
                          sigelts1)
                     | uu____9269 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9276 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9276
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____9282 =
                   let uu___109_9283 = s  in
                   let uu____9284 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___109_9283.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___109_9283.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9284;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___109_9283.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___109_9283.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9282])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____9294 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9294
            then []
            else
              (let uu____9298 = lbs  in
               match uu____9298 with
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
                       (fun uu____9354  ->
                          match uu____9354 with
                          | (uu____9361,t) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____9379  ->
                            match uu____9379 with
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
                          (fun uu____9399  ->
                             match uu____9399 with
                             | (uu____9406,t) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____9419,uu____9420) ->
            let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____9425 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____9476 =
                       FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                        in
                     FStar_Ident.lid_equals lid uu____9476) uu____9425
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____9479 =
                   let uu___110_9480 = s  in
                   let uu____9481 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___110_9480.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___110_9480.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9481;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___110_9480.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___110_9480.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9479]
               else [])
            else
              (let uu____9486 =
                 let uu___111_9487 = s  in
                 let uu____9488 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___111_9487.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___111_9487.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____9488;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___111_9487.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___111_9487.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____9486])
        | FStar_Syntax_Syntax.Sig_new_effect uu____9491 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9492 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____9493 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9494 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____9507 -> [s]  in
      let uu___112_9508 = m  in
      let uu____9509 =
        let uu____9510 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____9510  in
      {
        FStar_Syntax_Syntax.name = (uu___112_9508.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9509;
        FStar_Syntax_Syntax.exports =
          (uu___112_9508.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      (let uu____9524 = FStar_Syntax_DsEnv.pop ()  in
       FStar_All.pipe_right uu____9524 FStar_Pervasives.ignore);
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
      let uu___113_9535 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___113_9535.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___113_9535.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___113_9535.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___113_9535.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___113_9535.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___113_9535.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___113_9535.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___113_9535.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___113_9535.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___113_9535.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___113_9535.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___113_9535.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___113_9535.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___113_9535.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___113_9535.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___113_9535.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___113_9535.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___113_9535.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___113_9535.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___113_9535.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___113_9535.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___113_9535.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___113_9535.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___113_9535.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___113_9535.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___113_9535.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___113_9535.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___113_9535.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___113_9535.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___113_9535.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___113_9535.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___113_9535.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___113_9535.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___113_9535.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv1;
        FStar_TypeChecker_Env.dep_graph =
          (uu___113_9535.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____9556 = FStar_Options.debug_any ()  in
       if uu____9556
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
         let uu___114_9561 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___114_9561.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___114_9561.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___114_9561.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___114_9561.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___114_9561.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___114_9561.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___114_9561.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___114_9561.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___114_9561.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___114_9561.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___114_9561.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___114_9561.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___114_9561.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___114_9561.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___114_9561.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___114_9561.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___114_9561.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___114_9561.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___114_9561.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___114_9561.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___114_9561.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___114_9561.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___114_9561.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___114_9561.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___114_9561.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___114_9561.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___114_9561.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___114_9561.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___114_9561.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___114_9561.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___114_9561.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___114_9561.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___114_9561.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___114_9561.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____9563 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____9563 with
       | (ses,exports,env3) ->
           ((let uu___115_9596 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___115_9596.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___115_9596.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___115_9596.FStar_Syntax_Syntax.is_interface)
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
        let uu____9618 = tc_decls env decls  in
        match uu____9618 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___116_9649 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___116_9649.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___116_9649.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___116_9649.FStar_Syntax_Syntax.is_interface)
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
        let uu____9694 =
          FStar_Ident.lid_equals env0.FStar_TypeChecker_Env.curmodule
            FStar_Parser_Const.prims_lid
           in
        if uu____9694
        then
          let uu___117_9695 = env0  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___117_9695.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___117_9695.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___117_9695.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___117_9695.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___117_9695.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___117_9695.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___117_9695.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___117_9695.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___117_9695.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___117_9695.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___117_9695.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___117_9695.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___117_9695.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___117_9695.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___117_9695.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___117_9695.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___117_9695.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___117_9695.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes =
              (uu___117_9695.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___117_9695.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___117_9695.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___117_9695.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___117_9695.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___117_9695.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___117_9695.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___117_9695.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___117_9695.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___117_9695.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___117_9695.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___117_9695.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___117_9695.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___117_9695.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___117_9695.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___117_9695.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___117_9695.FStar_TypeChecker_Env.dep_graph)
          }
        else env0  in
      let msg =
        Prims.strcat "Internals for "
          (m.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let env02 = push_context env01 msg  in
      let uu____9699 = tc_partial_modul env02 m  in
      match uu____9699 with
      | (modul,non_private_decls,env) ->
          let uu____9723 =
            finish_partial_modul false env modul non_private_decls  in
          (match uu____9723 with
           | (m1,m_opt,env1) ->
               (m1, m_opt,
                 (let uu___118_9750 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___118_9750.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___118_9750.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___118_9750.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___118_9750.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___118_9750.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___118_9750.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___118_9750.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___118_9750.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___118_9750.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___118_9750.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___118_9750.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___118_9750.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___118_9750.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___118_9750.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___118_9750.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___118_9750.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___118_9750.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___118_9750.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = lax_mode;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___118_9750.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___118_9750.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___118_9750.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___118_9750.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___118_9750.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___118_9750.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___118_9750.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___118_9750.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___118_9750.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___118_9750.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___118_9750.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___118_9750.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___118_9750.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___118_9750.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___118_9750.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___118_9750.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___118_9750.FStar_TypeChecker_Env.dep_graph)
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
          let uu____9765 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
             in
          if uu____9765
          then
            let en0 =
              pop_context en
                (Prims.strcat "Ending modul "
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
               in
            let en01 =
              let uu___119_9776 = en0  in
              let uu____9777 =
                let uu____9790 =
                  FStar_All.pipe_right
                    en.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                (uu____9790, FStar_Pervasives_Native.None)  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___119_9776.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___119_9776.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___119_9776.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___119_9776.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___119_9776.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___119_9776.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___119_9776.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___119_9776.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___119_9776.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___119_9776.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___119_9776.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___119_9776.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___119_9776.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___119_9776.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___119_9776.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___119_9776.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___119_9776.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___119_9776.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___119_9776.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___119_9776.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___119_9776.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___119_9776.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___119_9776.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___119_9776.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___119_9776.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___119_9776.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___119_9776.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index = uu____9777;
                FStar_TypeChecker_Env.proof_ns =
                  (uu___119_9776.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___119_9776.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___119_9776.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___119_9776.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___119_9776.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___119_9776.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___119_9776.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___119_9776.FStar_TypeChecker_Env.dep_graph)
              }  in
            let en02 =
              let uu____9828 =
                let uu____9829 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9829  in
              if uu____9828
              then
                ((let uu____9831 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____9831 FStar_Pervasives.ignore);
                 z3_reset_options en01)
              else en01  in
            let modul_iface = extract_interface en m  in
            ((let uu____9835 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                  FStar_Options.Low
                 in
              if uu____9835
              then
                let uu____9836 =
                  let uu____9837 =
                    FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9837 then "" else " (in lax mode) "  in
                let uu____9839 =
                  let uu____9840 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9840
                  then
                    let uu____9841 =
                      let uu____9842 = FStar_Syntax_Print.modul_to_string m
                         in
                      Prims.strcat uu____9842 "\n"  in
                    Prims.strcat "\nfrom: " uu____9841
                  else ""  in
                let uu____9844 =
                  let uu____9845 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____9845
                  then
                    let uu____9846 =
                      let uu____9847 =
                        FStar_Syntax_Print.modul_to_string modul_iface  in
                      Prims.strcat uu____9847 "\n"  in
                    Prims.strcat "\nto: " uu____9846
                  else ""  in
                FStar_Util.print4
                  "Extracting and type checking module %s interface%s%s%s\n"
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____9836
                  uu____9839 uu____9844
              else ());
             (let env0 =
                let uu___120_9851 = en02  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___120_9851.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___120_9851.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___120_9851.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___120_9851.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___120_9851.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___120_9851.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___120_9851.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___120_9851.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___120_9851.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___120_9851.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___120_9851.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___120_9851.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___120_9851.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___120_9851.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___120_9851.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___120_9851.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface = true;
                  FStar_TypeChecker_Env.admit =
                    (uu___120_9851.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___120_9851.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___120_9851.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___120_9851.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___120_9851.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___120_9851.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___120_9851.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___120_9851.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___120_9851.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___120_9851.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___120_9851.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___120_9851.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___120_9851.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___120_9851.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___120_9851.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___120_9851.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___120_9851.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___120_9851.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___120_9851.FStar_TypeChecker_Env.dep_graph)
                }  in
              let uu____9852 = tc_modul en02 modul_iface  in
              match uu____9852 with
              | (modul_iface1,must_be_none,env) ->
                  if must_be_none <> FStar_Pervasives_Native.None
                  then
                    failwith
                      "Impossible! Expected the second component to be None"
                  else
                    (((let uu___121_9898 = m  in
                       {
                         FStar_Syntax_Syntax.name =
                           (uu___121_9898.FStar_Syntax_Syntax.name);
                         FStar_Syntax_Syntax.declarations =
                           (uu___121_9898.FStar_Syntax_Syntax.declarations);
                         FStar_Syntax_Syntax.exports =
                           (modul_iface1.FStar_Syntax_Syntax.exports);
                         FStar_Syntax_Syntax.is_interface =
                           (uu___121_9898.FStar_Syntax_Syntax.is_interface)
                       })), (FStar_Pervasives_Native.Some modul_iface1), env)))
          else
            (let modul =
               let uu____9901 = FStar_Options.use_extracted_interfaces ()  in
               if uu____9901
               then
                 let uu___122_9902 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___122_9902.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___122_9902.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___122_9902.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___123_9904 = m  in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___123_9904.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___123_9904.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___123_9904.FStar_Syntax_Syntax.is_interface)
                  })
                in
             let env = FStar_TypeChecker_Env.finish_module en modul  in
             (let uu____9907 =
                FStar_All.pipe_right
                  env.FStar_TypeChecker_Env.qtbl_name_and_index
                  FStar_Pervasives_Native.fst
                 in
              FStar_All.pipe_right uu____9907 FStar_Util.smap_clear);
             (let uu____9935 =
                ((let uu____9938 = FStar_Options.lax ()  in
                  Prims.op_Negation uu____9938) &&
                   (let uu____9940 =
                      FStar_Options.use_extracted_interfaces ()  in
                    Prims.op_Negation uu____9940))
                  && (Prims.op_Negation loading_from_cache)
                 in
              if uu____9935 then check_exports env modul exports else ());
             (let uu____9943 =
                pop_context env
                  (Prims.strcat "Ending modul "
                     (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 in
              FStar_All.pipe_right uu____9943 FStar_Pervasives.ignore);
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
               env modul;
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ();
             (let uu____9947 =
                let uu____9948 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9948  in
              if uu____9947
              then
                let uu____9949 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____9949 FStar_Pervasives.ignore
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
        let uu____9961 =
          let uu____9962 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____9962  in
        push_context env uu____9961  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____9981 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____10002 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports  in
      match uu____10002 with | (uu____10011,uu____10012,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      (let uu____10033 = FStar_Options.debug_any ()  in
       if uu____10033
       then
         let uu____10034 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____10034
       else ());
      (let env1 =
         let uu___124_10038 = env  in
         let uu____10039 =
           let uu____10040 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____10040  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_10038.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_10038.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_10038.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_10038.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_10038.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_10038.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_10038.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_10038.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_10038.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_10038.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_10038.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_10038.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___124_10038.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___124_10038.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_10038.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_10038.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___124_10038.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___124_10038.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____10039;
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_10038.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___124_10038.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___124_10038.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___124_10038.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___124_10038.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_10038.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___124_10038.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___124_10038.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___124_10038.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___124_10038.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___124_10038.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___124_10038.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___124_10038.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___124_10038.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___124_10038.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___124_10038.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___124_10038.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____10041 = tc_modul env1 m  in
       match uu____10041 with
       | (m1,m_iface_opt,env2) ->
           ((let uu____10066 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____10066
             then
               let uu____10067 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____10067
             else ());
            (let uu____10070 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____10070
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
                       let uu____10101 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____10101 with
                       | (univnames1,e) ->
                           let uu___125_10108 = lb  in
                           let uu____10109 =
                             let uu____10112 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____10112 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___125_10108.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_10108.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___125_10108.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_10108.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____10109;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___125_10108.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___125_10108.FStar_Syntax_Syntax.lbpos)
                           }
                        in
                     let uu___126_10113 = se  in
                     let uu____10114 =
                       let uu____10115 =
                         let uu____10122 =
                           let uu____10129 = FStar_List.map update lbs  in
                           (b, uu____10129)  in
                         (uu____10122, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____10115  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____10114;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___126_10113.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___126_10113.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___126_10113.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___126_10113.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____10142 -> se  in
               let normalized_module =
                 let uu___127_10144 = m1  in
                 let uu____10145 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___127_10144.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____10145;
                   FStar_Syntax_Syntax.exports =
                     (uu___127_10144.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___127_10144.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____10146 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____10146
             else ());
            (m1, m_iface_opt, env2)))
  